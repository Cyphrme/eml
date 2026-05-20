//! Hash abstraction for EML.
//!
//! Extends the RFC 9162 leaf/node/empty operations with a null constant
//! (Definition 1, §3 of the formal model).

use std::fmt::Debug;

/// Hash operations required by the EML tree.
///
/// Each algorithm registered with the [`Log`](crate::Log) provides an
/// implementation of this trait. The trait is object-safe to permit
/// heterogeneous algorithm storage.
///
/// # Model Mapping
///
/// | Trait method | Formal model  | Operation              |
/// |:-------------|:--------------|:-----------------------|
/// | [`leaf`]     | `leaf(a, d)`  | `H_a(0x00 ‖ data)`    |
/// | [`node`]     | `node(a,l,r)` | `H_a(0x01 ‖ l ‖ r)`   |
/// | [`empty`]    | `empty(a)`    | `H_a("")`              |
/// | [`null`]     | `N₀(a)`       | `H_a(0x02)`            |
///
/// [`leaf`]: Hasher::leaf
/// [`node`]: Hasher::node
/// [`empty`]: Hasher::empty
/// [`null`]: Hasher::null
///
/// # Domain Separation (D-SEP)
///
/// The three prefix bytes `0x00`, `0x01`, `0x02` establish three-way domain
/// separation. Implementations **must** use these exact prefixes:
///
/// - `leaf(d) ≠ node(l, r)` for all inputs  (0x00 ≠ 0x01)
/// - `null() ≠ leaf(d)` for all inputs       (0x02 ≠ 0x00)
/// - `null() ≠ node(l, r)` for all inputs    (0x02 ≠ 0x01)
pub trait Hasher: Debug + Send + Sync {
    /// Hash a leaf entry: `H(0x00 ‖ data)`.
    fn leaf(&self, data: &[u8]) -> Vec<u8>;

    /// Hash two child nodes: `H(0x01 ‖ left ‖ right)`.
    fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8>;

    /// Hash of the empty string: `H("")`. Root of an empty tree.
    fn empty(&self) -> Vec<u8>;

    /// Null leaf constant: `H(0x02)`.
    ///
    /// This is Definition 1 (§3) of the formal model. The single byte `0x02`
    /// is domain-separated from leaf (`0x00`) and node (`0x01`) prefixes.
    fn null(&self) -> Vec<u8>;

    /// Digest output length in bytes.
    fn digest_len(&self) -> usize;
}
