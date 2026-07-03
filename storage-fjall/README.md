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
- **Multi-database support** — scoped keyspaces per tenant via `with_database`
- **Configurable backends** — Fjall's column families for flexible schema design

## Usage

```rust
use storage_fjall::FjallStorage;

let storage = FjallStorage::with_database(db, "leaves")?;
// Pass to polydigest/EML constructors...
```

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
