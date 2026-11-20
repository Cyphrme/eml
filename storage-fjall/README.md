# storage-fjall — Fjall-backed persistent storage

**A production-grade storage backend for EML.** `storage-fjall` implements the
`Storage` trait from the `polydigest` combinator, providing durable, efficient
leaf persistence via [Fjall](https://github.com/fjall-rs/fjall), an LSM-based
embedded key-value store.

## Role

The EML stack operates on an abstract `Storage` interface for leaf and metadata
persistence. This crate supplies a concrete implementation backed by Fjall,
suitable for production deployments with durability, concurrency, and
compaction guarantees.

## Features

- **Durable leaf storage** — leaves persisted to disk via Fjall's LSM engine
- **Concurrent access** — thread-safe key-value operations with isolation
- **Many logs, fixed keyspaces** — scopes are a length-prefixed key prefix over one
  keyspace triplet, so adding a log creates no keyspace
- **Configurable backends** — Fjall's column families for flexible schema design

## Usage

```rust
use storage_fjall::{FjallStorage, LogKeyspaces};

// Once per database: creates `eml_leaves`, `eml_nodes`, `eml_metadata`.
let keyspaces = LogKeyspaces::open(db)?;

// Per log (e.g. per principal): no IO, no keyspace creation. Free to call
// on every load.
let storage = FjallStorage::scoped(&keyspaces, principal_id_bytes)?;
// Pass to polydigest/EML constructors...

// Retire a log: one batch, not synced.
FjallStorage::scoped(&keyspaces, old_scope)?.drop_scope()?;
```

`FjallStorage::open(path)` and `with_database(db)` remain for the
single-log case; they use the empty scope.

## Scoping and durability

Every key is `u16 BE scope length ++ scope ++ suffix`, so no scope's keys
collide with, or are a byte-prefix of, another's, and scans stay inside
their scope. Scope is a key prefix and not a keyspace name because creating a
fjall keyspace costs about 14 fsyncs under a database-wide lock, which a
per-principal keyspace triplet paid on every new principal.

`apply` commits one fjall batch and never syncs; durability policy
(`Database::persist`) belongs to the caller, who can then cover a log write
and its other writes with one sync.

## Migrating from 0.2

0.3.0 is breaking in API and on-disk layout.

- `with_database_scoped(db, prefix)` is removed, with
  `FjallStorageError::InvalidPrefix`. Use `LogKeyspaces::open` once and
  `FjallStorage::scoped`; the scope is arbitrary bytes (at most 65535), and
  a too-long one is `InvalidScope`.
- Keys now carry the scope prefix, including the empty scope that `open` and
  `with_database` use. A 0.2 store is not readable and must be rebuilt from
  its source of truth; delete any leftover `{prefix}_eml_*` keyspaces. Opened
  with 0.3, it reports `MetadataCorruption` (`len`: "leaf key has wrong
  length"; `load_algorithm_metas`), and `append_count` reads 0 -- 0.2 keys
  that begin with two zero bytes fall under the empty scope's prefix. This
  is the layout change, not disk corruption.

## Place in the stack

```
merkle-spine → canonical-ml → polydigest → EML
                                  ↓
                           Storage trait
                                  ↓
         polydigest-storage-fjall (this crate: Fjall backend)
```

## Further reading

- `polydigest` — the combinator that defines the `Storage` interface
- [`../docs/architecture.md`](../docs/architecture.md) — system design
