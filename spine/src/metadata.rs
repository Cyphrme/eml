//! Opaque metadata channel for PMT commitments.
//!
//! `Meta` is an **arbitrary, opaque byte buffer** that PMT attaches to a
//! commitment ([`crate::Sealed`]) without interpretation. The library never
//! reads, validates, or signs its contents — that is the consumer's concern.
//! Any byte sequence is a valid `Meta` value, including the empty slice.
//!
//! # Design note
//!
//! The type is intentionally a plain newtype over `Vec<u8>`. It carries no
//! variant for a specific attestation format, no schema, and no embedded
//! length or version field — the consumer controls all of that. The name
//! deliberately avoids cryptographic or application-layer vocabulary; the
//! fact that an optional tree-head attestation *may* ride here is purely a
//! consumer convention, invisible to the kernel.

/// Opaque, application-defined byte payload attached to a PMT commitment.
///
/// The library never inspects or validates the contents; round-trip
/// fidelity (store then retrieve) is the only guarantee.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Meta(Vec<u8>);

impl Meta {
    /// Wrap raw bytes into a `Meta` value.
    #[must_use]
    pub fn new(bytes: Vec<u8>) -> Self {
        Self(bytes)
    }

    /// Borrow the raw bytes.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Consume into the raw bytes.
    #[must_use]
    pub fn into_bytes(self) -> Vec<u8> {
        self.0
    }

    /// Whether the payload is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Length of the payload in bytes.
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl From<Vec<u8>> for Meta {
    fn from(bytes: Vec<u8>) -> Self {
        Self(bytes)
    }
}

impl From<&[u8]> for Meta {
    fn from(bytes: &[u8]) -> Self {
        Self(bytes.to_vec())
    }
}

impl AsRef<[u8]> for Meta {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // Property: round-trip fidelity — whatever bytes go in come back out.
    // -----------------------------------------------------------------------

    #[test]
    fn empty_round_trips() {
        let m = Meta::new(vec![]);
        assert_eq!(m.as_bytes(), b"");
        assert!(m.is_empty());
        assert_eq!(m.len(), 0);
        assert_eq!(m.into_bytes(), Vec::<u8>::new());
    }

    #[test]
    fn arbitrary_bytes_round_trip() {
        // Arbitrary payload: mix of zeros, high bytes, structured data.
        let payload: Vec<u8> = (0u8..=255u8).collect();
        let m = Meta::new(payload.clone());
        assert_eq!(m.as_bytes(), payload.as_slice());
        assert!(!m.is_empty());
        assert_eq!(m.len(), 256);
        assert_eq!(m.clone().into_bytes(), payload);
    }

    #[test]
    fn from_slice_and_vec_agree() {
        let payload = b"opaque payload, library does not interpret this";
        let from_slice = Meta::from(payload.as_slice());
        let from_vec = Meta::from(payload.to_vec());
        assert_eq!(from_slice, from_vec);
        assert_eq!(from_slice.as_bytes(), payload);
    }

    #[test]
    fn as_ref_matches_as_bytes() {
        let payload = vec![0xDE, 0xAD, 0xBE, 0xEF];
        let m = Meta::new(payload.clone());
        assert_eq!(m.as_ref(), m.as_bytes());
        assert_eq!(m.as_ref(), payload.as_slice());
    }

    #[test]
    fn distinct_payloads_are_not_equal() {
        let a = Meta::new(vec![1, 2, 3]);
        let b = Meta::new(vec![1, 2, 4]);
        assert_ne!(a, b);
    }

    #[test]
    fn clone_is_independent() {
        let original = Meta::new(vec![0xFF; 32]);
        let mut cloned = original.clone();
        // Mutate the clone; original must be unchanged.
        cloned.0.push(0x00);
        assert_eq!(original.len(), 32);
        assert_eq!(cloned.len(), 33);
    }

    #[test]
    fn default_is_empty() {
        let m = Meta::default();
        assert!(m.is_empty());
        assert_eq!(m.as_bytes(), b"");
    }

    // -----------------------------------------------------------------------
    // Property: library-agnostic — the module has no interpretation logic.
    // The absence of match/pattern arms or conditional branches over the
    // byte content is structural; these tests confirm the bytes are opaque.
    // -----------------------------------------------------------------------

    #[test]
    fn null_byte_payload_round_trips() {
        let payload = vec![0x00; 64];
        let m = Meta::new(payload.clone());
        assert_eq!(m.as_bytes(), payload.as_slice());
    }

    #[test]
    fn large_payload_round_trips() {
        let payload: Vec<u8> = (0..4096).map(|i| (i % 256) as u8).collect();
        let m = Meta::new(payload.clone());
        assert_eq!(m.len(), 4096);
        assert_eq!(m.into_bytes(), payload);
    }
}
