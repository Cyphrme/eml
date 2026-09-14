//! The byte-exact object layout: hex naming, blob encodings, and the pure
//! epoch-projection helpers the checkpoint tree's `epochs/` section needs.
//!
//! Every function here is a pure transform over bytes/integers; no `gix`
//! type appears in this module. Keeping the encoding decoupled from the git
//! plumbing is what makes the golden-vector and property tests in
//! `tests/structural.rs` exercise it without a repository at all.

use crate::error::GitStorageError as Error;

/// `hex(x, 16)` — a `u64` rendered as 16 lowercase hex digits.
#[must_use]
pub fn hex16(x: u64) -> String {
    format!("{x:016x}")
}

/// `hex(x, 2)` — a value `0..=255` rendered as 2 lowercase hex digits.
///
/// # Panics
///
/// Panics if `x > 0xff`; every caller in this crate bounds `x` to `0..k` or
/// `0..d_j` first, both of which `spine::ARITY_RANGE` (`2..=256`) keeps
/// within `0..=255`.
#[must_use]
pub fn hex2(x: u64) -> String {
    assert!(x <= 0xff, "hex2: value {x} exceeds 2 hex digits");
    format!("{x:02x}")
}

/// Decode a `hex(_, 16)` name back to its `u64`, or `None` if it is not
/// exactly 16 lowercase hex digits.
#[must_use]
pub fn parse_hex16(name: &str) -> Option<u64> {
    if name.len() != 16 || !name.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    u64::from_str_radix(name, 16).ok()
}

/// `meta`'s fixed 12-byte encoding (§3.1, SG12). One shape, for every log
/// regardless of resume history: there is nothing this early to stay
/// compatible with, so no second, wider shape and no boundary field exist
/// to distinguish.
#[must_use]
pub fn encode_meta(arity: u64, count: u64, kind: u8) -> [u8; 12] {
    let mut out = [0u8; 12];
    out[0] = 0x01;
    out[1..3].copy_from_slice(&(arity as u16).to_be_bytes());
    out[3..11].copy_from_slice(&count.to_be_bytes());
    out[11] = kind;
    out
}

/// Decode `meta`'s bytes (§3.1, SG12). Rejects any length other than 12 or
/// an unrecognized version byte.
pub fn decode_meta(bytes: &[u8]) -> Result<(u64, u64, u8), Error> {
    if bytes.len() != 12 {
        return Err(Error::Corruption(format!(
            "meta blob must be exactly 12 bytes, got {}",
            bytes.len()
        )));
    }
    if bytes[0] != 0x01 {
        return Err(Error::Corruption(format!(
            "meta blob has unrecognized version byte {:#04x}",
            bytes[0]
        )));
    }
    let arity = u16::from_be_bytes([bytes[1], bytes[2]]) as u64;
    let count = u64::from_be_bytes(bytes[3..11].try_into().unwrap());
    let kind = bytes[11];
    Ok((arity, count, kind))
}

/// A `epochs/hex(alg_id,16)` blob's encoding (§3.2): a sequence of
/// `(start, end)` `u64` BE pairs, each 16 bytes.
#[must_use]
pub fn encode_epochs(epochs: &[(u64, u64)]) -> Vec<u8> {
    let mut out = Vec::with_capacity(epochs.len() * 16);
    for &(start, end) in epochs {
        out.extend_from_slice(&start.to_be_bytes());
        out.extend_from_slice(&end.to_be_bytes());
    }
    out
}

/// Decode an `epochs/hex(alg_id,16)` blob (§3.2). Rejects a length that is
/// not a multiple of 16, or an empty result (an algorithm is only ever
/// recorded once registered, with at least one epoch).
pub fn decode_epochs(bytes: &[u8]) -> Result<Vec<(u64, u64)>, Error> {
    if bytes.is_empty() || bytes.len() % 16 != 0 {
        return Err(Error::Corruption(format!(
            "epochs blob length {} is not a positive multiple of 16",
            bytes.len()
        )));
    }
    Ok(bytes
        .chunks_exact(16)
        .map(|chunk| {
            let start = u64::from_be_bytes(chunk[0..8].try_into().unwrap());
            let end = u64::from_be_bytes(chunk[8..16].try_into().unwrap());
            (start, end)
        })
        .collect())
}

/// The epoch timeline as it stood at `size`, mirroring
/// `cml::engine::AlgView::epochs_at` (`cml/src/engine.rs:203-216`) exactly,
/// reimplemented here as a free function over a raw epoch list so this crate
/// does not need a `Box<dyn Hasher>` just to call an `AlgView` method.
/// `tests/epoch_parity.rs` checks this copy against the real `AlgView` for
/// randomized histories so the two cannot silently drift apart.
#[must_use]
pub fn epochs_at(history: &[(u64, u64)], size: u64) -> Option<Vec<(u64, u64)>> {
    let mut out = Vec::new();
    for &(start, end) in history {
        if start > size {
            break;
        }
        if end > size {
            out.push((start, u64::MAX));
            break;
        }
        out.push((start, end));
    }
    if out.is_empty() { None } else { Some(out) }
}

/// Whether the epoch timeline's last entry is active (open) at `size`.
#[must_use]
pub fn is_active_at(epochs_at_size: &[(u64, u64)]) -> bool {
    epochs_at_size
        .last()
        .is_some_and(|&(_, end)| end == u64::MAX)
}

#[cfg(test)]
mod tests {
    use cml::AlgView;
    use proptest::prelude::*;

    use super::*;

    #[derive(Debug)]
    struct NullHasher;
    impl cml::Hasher for NullHasher {
        fn leaf(&self, _: &[u8]) -> Vec<u8> {
            vec![0; 4]
        }

        fn node(&self, _: &[&[u8]]) -> Vec<u8> {
            vec![0; 4]
        }

        fn empty(&self) -> Vec<u8> {
            vec![0; 4]
        }

        fn hash(&self, _: &[u8]) -> Vec<u8> {
            vec![0; 4]
        }

        fn clone_box(&self) -> Box<dyn cml::Hasher> {
            Box::new(NullHasher)
        }
    }

    fn view(epochs: Vec<(u64, u64)>) -> AlgView {
        AlgView {
            hasher: Box::new(NullHasher),
            epochs,
            frontier: Vec::new(),
            frontier_coords: Vec::new(),
        }
    }

    fn arb_epochs() -> impl Strategy<Value = Vec<(u64, u64)>> {
        // A handful of monotonically increasing boundaries, the last
        // optionally left open -- matches AlgView::epochs_at's own
        // documented shape (`cml/src/engine.rs`).
        (prop::collection::vec(1u64..20, 1..6), any::<bool>()).prop_map(|(deltas, open)| {
            let mut bounds = Vec::with_capacity(deltas.len());
            let mut acc = 0u64;
            for d in deltas {
                acc += d;
                bounds.push(acc);
            }
            let mut epochs = Vec::new();
            for pair in bounds.chunks(2) {
                match pair {
                    [start, end] => epochs.push((*start, *end)),
                    [start] => {
                        if open {
                            epochs.push((*start, u64::MAX));
                        }
                    },
                    _ => unreachable!(),
                }
            }
            if epochs.is_empty() {
                epochs.push((0, u64::MAX));
            }
            epochs
        })
    }

    proptest! {
        /// SG13: `layout::epochs_at` mirrors `cml::engine::AlgView::epochs_at`
        /// exactly, for randomized histories and sizes -- the parity check
        /// this module's doc comment promises.
        #[test]
        fn epochs_at_matches_alg_view(epochs in arb_epochs(), size in 0u64..200) {
            let expected = view(epochs.clone()).epochs_at(size);
            let actual = epochs_at(&epochs, size);
            prop_assert_eq!(actual, expected);
        }
    }

    #[test]
    fn hex_round_trips() {
        for x in [0u64, 1, 255, 65535, u64::MAX] {
            assert_eq!(parse_hex16(&hex16(x)), Some(x));
        }
        assert_eq!(parse_hex16("not-hex-at-all!!"), None);
        assert_eq!(hex2(0), "00");
        assert_eq!(hex2(255), "ff");
    }

    #[test]
    fn meta_round_trip() {
        let bytes = encode_meta(4, 12345, 1);
        assert_eq!(bytes.len(), 12, "meta's one fixed shape is 12 bytes");
        assert_eq!(decode_meta(&bytes).unwrap(), (4, 12345, 1));
        assert!(decode_meta(&bytes[..11]).is_err());
    }

    #[test]
    fn meta_rejects_any_length_other_than_twelve() {
        let bytes = encode_meta(4, 12345, 1);
        let mut too_long = bytes.to_vec();
        too_long.push(0);
        assert!(decode_meta(&too_long).is_err());
        assert!(decode_meta(&bytes[..11]).is_err());
    }

    #[test]
    fn meta_rejects_an_unrecognized_version_byte() {
        let mut bytes = encode_meta(4, 12345, 1);
        bytes[0] = 0x02;
        assert!(decode_meta(&bytes).is_err());
    }

    #[test]
    fn epochs_round_trip() {
        let epochs = vec![(0, 10), (15, u64::MAX)];
        let bytes = encode_epochs(&epochs);
        assert_eq!(decode_epochs(&bytes).unwrap(), epochs);
        assert!(decode_epochs(&[]).is_err());
        assert!(decode_epochs(&[0u8; 15]).is_err());
    }

    /// SG6: no fixed literal name is ever a valid `hex(_, w)` string for any
    /// `w`, so it can never collide with a `hex16`/`hex2` sibling name --
    /// checked exhaustively over the fixed literal alphabet, the way SG6
    /// itself frames the claim ("a name-collision or prefix-ambiguity check
    /// is exhaustive over the fixed alphabet").
    #[test]
    fn literal_names_never_collide_with_a_hex_encoded_name() {
        for name in ["meta", "epochs", "roots", "peaks", "leaf", "digest"] {
            assert!(
                !name.bytes().all(|b| b.is_ascii_hexdigit()),
                "{name:?} is all-hex and could collide with a \
                 hex(alg_id,16)/hex(j,2)/hex(q,2)/hex(c,2) sibling"
            );
        }
    }
}
