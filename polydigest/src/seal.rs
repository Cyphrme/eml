//! Freezing the combinator's append-only log into the one commitment currency
//! [`crate::Sealed`].
//!
//! There is exactly one commitment currency. A mutable `Emt` and this
//! append-only log both seal into [`crate::Sealed`]; the combinator computes the
//! resumable frontier, so every `Sealed` uniformly carries a frontier whatever
//! sealed it. An append-only log already holds its frontier natively, so its
//! seal freezes the active algorithms' frontier peaks at the sealed size and
//! each closed algorithm's peaks at its close size, and pairs them with the
//! committed timeline (the epoch facet, D13).
//!
//! The seal is one-way: it consumes the log and there is no path back to one
//! (C-SEAL-ONEWAY). The way *forward* from a `Sealed` is the orthogonal
//! operation set keyed by what each needs:
//!
//! - **verify** — the proofs ([`crate::snapshot_proof`], binding/leaf/consistency) check against
//!   the `Sealed`'s derived roots; needs nothing but the `Sealed`;
//! - **resume** ([`NaryMerkleLog::resume`]) — needs only the frontier (which the `Sealed` *is*);
//!   reopens an append-only log onto the committed frontier;
//! - **[`fill`](crate::fill)** — needs the real leaf data; rebuilds a full, readable tree and
//!   verifies it against the committed binding root.
//!
//! # What a seal commits
//!
//! For every algorithm active at the sealed size (its epoch covers the final
//! position) the seal freezes that algorithm's **frontier peaks** — the digests
//! of the perfect k-ary subtrees [`spine::frontier_for_size`] names — together
//! with the committed epoch timeline and an optional opaque metadata payload
//! ([`spine::Meta`]). An algorithm closed before the seal has no member root at
//! the sealed size, so its peaks at its close size ride beside the structural
//! seal ([`Sealed::dormant_frontiers`]); that is O(log n) per algorithm, and
//! lets a resumed log resume it. The member root, binding root, and run-extents are
//! *derived views* of the `Sealed`, not stored.

use spine::Meta;

use crate::Sealed;
use crate::log_error::{LogError, LogResult as Result};
use crate::storage::Storage;
use crate::tree::NaryMerkleLog;

impl<S: Storage> NaryMerkleLog<S> {
    /// Seal this log into the commitment currency [`Sealed`] at its current size,
    /// consuming the log.
    ///
    /// Freezes the frontier peaks of every algorithm active at the sealed size,
    /// the peaks of every closed algorithm at its close size, and the committed
    /// epoch timeline. The transition is one-way: the log is
    /// consumed and a `Sealed` cannot be walked back to a log (C-SEAL-ONEWAY).
    ///
    /// To attach an optional opaque metadata payload (where a tree-head
    /// attestation may ride), use [`Self::seal_with_meta`].
    ///
    /// # Errors
    ///
    /// Returns a storage error if a frontier node cannot be read.
    pub async fn seal(self) -> Result<Sealed, S::Error> {
        self.seal_inner(None).await
    }

    /// Seal this log into [`Sealed`], attaching an opaque metadata payload,
    /// consuming the log.
    ///
    /// Identical to [`Self::seal`] except the `Sealed` carries `meta`. The
    /// library never reads or validates the payload; any byte sequence is
    /// accepted (INV-METADATA-AGNOSTIC).
    ///
    /// # Errors
    ///
    /// As [`Self::seal`].
    pub async fn seal_with_meta(self, meta: Meta) -> Result<Sealed, S::Error> {
        self.seal_inner(Some(meta)).await
    }

    /// Shared seal body: gather the active algorithms' frontier peaks and the
    /// committed timeline, then build the one-way [`Sealed`]. Consumes `self`.
    async fn seal_inner(self, meta: Option<Meta>) -> Result<Sealed, S::Error> {
        let size = self.count();
        let k = self.config().arity;

        // At size 0 there is no active algorithm and no timeline to freeze.
        let (frontiers, dormant, alg_epochs) = if size == 0 {
            (Vec::new(), Vec::new(), Vec::new())
        } else {
            let alg_epochs = self.committed_epochs_at(size);
            let frozen = self.hasherless_frozen();

            // Active algorithms contribute a frontier at the sealed size; a
            // closed one contributes its frontier at its close size, which a
            // resume needs to bring it back.
            let mut frontiers = Vec::new();
            let mut dormant = Vec::new();
            for (id, epochs) in &alg_epochs {
                // A closed algorithm held without its hasher has no view; its
                // close-size peaks were carried from the seal it came from, or
                // read from storage, so freezing them again keeps it from
                // being forgotten.
                if let Some(h) = frozen.get(id) {
                    let peaks: Option<Vec<Vec<u8>>> = h.peaks.iter().cloned().collect();
                    let peaks = peaks.ok_or(LogError::UnknownAlgorithm(*id))?;
                    dormant.push((*id, peaks));
                    continue;
                }
                match crate::committed_active_at(&alg_epochs, *id, size) {
                    Some(true) => {
                        let peaks = self.frontier_peaks_at(*id, size).await?;
                        frontiers.push((*id, peaks));
                    },
                    _ => {
                        let close = epochs.last().map_or(0, |&(_, end)| end);
                        let peaks = self.frontier_peaks_at(*id, close).await?;
                        dormant.push((*id, peaks));
                    },
                }
            }
            (frontiers, dormant, alg_epochs)
        };

        let sealed = Sealed::new(size, k, frontiers, alg_epochs)
            .and_then(|s| s.with_dormant_frontiers(dormant))
            .map_err(|_| LogError::MalformedSeal)?;
        Ok(match meta {
            Some(m) => sealed.with_meta(m),
            None => sealed,
        })
    }
}
