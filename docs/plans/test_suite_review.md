# Test Suite Review: Multi-Hash Coupling & Non-Divergence Auditing

This document reviews the validation strategy and test coverage for the N-ary Epoch Merkle Log (`neml`) implementation. Following the principles outlined in [robust-testing](file:///var/home/nrd/.gemini/antigravity-cli/plugins/predicate/skills/robust-testing/SKILL.md), we assess the current test suite, identify validation gaps, and propose robust testing methodologies (including Metamorphic Testing, Fuzzing, and Differential Assertions) to secure the codebase against regressions and logic bugs.

---

## 1. Current Test Suite Assessment

The current test suite in [`neml/tests/integration.rs`](file:///var/home/nrd/git/github.com/Cyphrme/eml/neml/tests/integration.rs) and [`neml/tests/proptests.rs`](file:///var/home/nrd/git/github.com/Cyphrme/eml/neml/tests/proptests.rs) is structurally rich but has several critical validation gaps:

### What is Well-Covered
* **Tree Topologies**: Base-$k$ carry-reduction schedules are validated across various arities ($k \in [2, 4]$) and sizes ($N \in [1, 64]$).
* **Multi-Epoch State Transitions**: Registration, freezing, and resumption of hash algorithms are verified to match standard MTH (Merkle Tree Hash) and recursive subtree definitions under happy-path scenarios.
* **Basic Proof Construction**: Log-level and subtree inclusion/consistency proofs are verified against expected verifier outputs.

### Critical Gaps and Mock Inundation
> [!WARNING]
> Multiple core validation functions are currently stubbed out (returning dummy `Ok(false)` or `None` values) in [`neml/src/proof.rs`](file:///var/home/nrd/git/github.com/Cyphrme/eml/neml/src/proof.rs) and [`neml/src/tree.rs`](file:///var/home/nrd/git/github.com/Cyphrme/eml/neml/src/tree.rs). Because the tests targeting these stubs are run on incomplete implementations, they fail out-of-the-box, indicating a need for both implementation completion and a more rigorous test harness to cover the edge boundaries.

Specifically:
1. **`verify_non_divergence` Coverage**: The only test for this auditing feature is `test_verify_non_divergence` (a simple happy-path append of one leaf `b"a"`). It does not test multi-epoch logs, multiple algorithms, or fault injection (tampering).
2. **Coupling Proof Property Fuzzing**: Property tests cover basic happy-path proof verification, but they do not fuzz verifier limits (DoS mitigation via `VerifierConfig::max_active_algorithms`) or malformed/unsorted inputs.
3. **No Cross-Crate Differential Assertions**: Even though `neml` generalizes `eml` to arbitrary arities ($k \ge 2$), there are no tests asserting that `neml` with $k=2$ matches the binary `eml` implementation.

---

## 2. Advanced Verification Methodologies

To eliminate the "self-deception loop" of AI-generated code, we propose integrating the following methodologies:

### A. Metamorphic Testing (MT)
We define three core Metamorphic Relations (MR) to assert semantic invariants without needing a hardcoded oracle:

| Metamorphic Relation | Input Transformation ($x \to x'$) | Expected Invariant Relation ($f(x) \sim f(x')$) | Target Feature |
| :--- | :--- | :--- | :--- |
| **MR-1: Checkpoint Monotonicity** | Audit checkpoint size subset ($M < N$ of active log) | $f(\text{log}, N) \implies f(\text{log}, M)$ | `verify_non_divergence` |
| **MR-2: Registration Commutativity** | Shuffle order of algorithm addition/resumption | $f(\text{log}_A) == f(\text{log}_B)$ | Multi-Hash Epoch state |
| **MR-3: Coupling Permutation** | Permute ordering of inactive/active elements in coupling proof | $f(\text{proof}) == f(\text{proof}')$ | `CouplingProof::verify` |

### B. Differential Assertions (EML vs NEML)
Since `neml` with arity $k=2$ is mathematically equivalent to the binary epoch log in `eml`, we can assert that both implementations yield identical tree roots, inclusion proofs, and consistency proofs for any arbitrary sequence of appends, freezes, and resumptions.

### C. Storage Fault Injection (Fuzzing / Security Boundaries)
We must stress-test `verify_non_divergence` by mutating the underlying storage backend. Under the hood, `MemoryStorage` holds three components: leaves, node hashes, and epoch metadata. Mutating any of these must cause the audit to fail.

---

## 3. Concrete Recommendations & Code Drafts

### Recommendation 1: Add Differential Proptests (EML vs NEML)
Integrate a differential property test in [`neml/tests/proptests.rs`](file:///var/home/nrd/git/github.com/Cyphrme/eml/neml/tests/proptests.rs) comparing `neml::NaryMerkleLog` ($k=2$) against `eml::Log`.

```rust
// Draft code block for differential verification (NEML vs EML)
// Paste into neml/tests/proptests.rs

use eml::Log as EmlLog;
use eml::storage::MemoryStorage as EmlMemoryStorage;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]
    
    #[test]
    fn differential_neml_eml_binary_equivalence(
        ops in proptest::collection::vec(op_strategy(4), 10..30),
        is_subtree_mode in any::<bool>(),
    ) {
        smol::block_on(async {
            let config = TreeConfig { log_arity: 2 };
            let mut neml_log = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(Sha256Hasher),
                config,
            )
            .await;

            let mut eml_log = EmlLog::new(EmlMemoryStorage::new());
            eml_log.add_algorithm(0, Box::new(Sha256Hasher)).await.unwrap();

            // Track algorithm IDs to keep them aligned (both logs support algorithm 0 and 1)
            neml_log.add_algorithm(1, new_hasher_for(1)).await.unwrap();
            eml_log.add_algorithm(1, Box::new(Sha256Hasher)).await.unwrap();

            for op in ops {
                match op {
                    Op::AppendLeaf(data) => {
                        neml_log.append_leaf(&data).await.unwrap();
                        eml_log.append(&data).await.unwrap();
                    }
                    Op::AppendSubtree(subtree) => {
                        if is_subtree_mode {
                            // Subtrees are promoted in NEML. We evaluate the subtree root 
                            // to append to EML to keep leaf inputs equivalent.
                            let evaluated = evaluate(&Sha256Hasher, &subtree);
                            neml_log.append_subtree(&subtree).await.unwrap();
                            eml_log.append(&evaluated).await.unwrap();
                        } else {
                            let evaluated = evaluate(&Sha256Hasher, &subtree);
                            neml_log.append_leaf(&evaluated).await.unwrap();
                            eml_log.append(&evaluated).await.unwrap();
                        }
                    }
                    Op::RemoveAlg(id) if id == 0 || id == 1 => {
                        // Avoid removing all active algorithms to prevent panics
                        let active_count = neml_log.storage().load_algorithm_metas().await.unwrap()
                            .iter()
                            .filter(|(_, epochs)| epochs.last().is_some_and(|&(_, end)| end == u64::MAX))
                            .count();
                        if active_count > 1 {
                            neml_log.remove_algorithm(id).await.unwrap();
                            eml_log.remove_algorithm(id).await.unwrap();
                        }
                    }
                    Op::ResumeAlg(id) if id == 0 || id == 1 => {
                        let is_frozen = neml_log.storage().load_algorithm_metas().await.unwrap()
                            .iter()
                            .find(|(alg_id, _)| *alg_id == id)
                            .is_some_and(|(_, epochs)| epochs.last().is_some_and(|&(_, end)| end != u64::MAX));
                        if is_frozen {
                            neml_log.resume_algorithm(id).await.unwrap();
                            eml_log.resume_algorithm(id).await.unwrap();
                        }
                    }
                    _ => {} // Ignore other algorithms for this differential test
                }

                // Assert root equivalence for all registered algorithms
                for id in &[0, 1] {
                    let neml_root = neml_log.root_for(*id).unwrap();
                    let eml_root = eml_log.root(*id).unwrap();
                    prop_assert_eq!(neml_root, eml_root, "Divergence found for alg {}", id);
                }
            }
            Ok::<(), proptest::test_runner::TestCaseError>(())
        })?;
    }
}
```

---

### Recommendation 2: Add Non-Divergence Fault Injection Tests
Add tests in [`neml/tests/fault_injection.rs`](file:///var/home/nrd/git/github.com/Cyphrme/eml/neml/tests/fault_injection.rs) that mutate storage state to check if `verify_non_divergence` properly detects malicious tampering.

```rust
// Draft code block for Non-Divergence Auditing via Fault Injection
// Paste into neml/tests/fault_injection.rs

#[test]
fn test_verify_non_divergence_tamper_detection() {
    smol::block_on(async {
        let hasher = Sha256Hasher;
        let storage = MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(hasher), config).await;

        // Populate log
        for i in 0..15u8 {
            log.append_leaf(&[i]).await.unwrap();
        }
        let root_0 = log.root();
        
        // Assert clean state passes
        assert!(log.verify_non_divergence(None, &[]).await.unwrap());

        // 1. Leaf data tampering
        {
            let mut tampered_storage = log.storage().clone();
            // Mutate leaf 7 payload
            tampered_storage.leaves[7] = vec![0xFF; 16];
            let tampered_log = NaryMerkleLog::from_storage(tampered_storage, vec![(0, Box::new(Sha256Hasher))]).await.unwrap();
            assert!(
                !tampered_log.verify_non_divergence(None, &[]).await.unwrap(),
                "Failed to detect tampered leaf data"
            );
        }

        // 2. Internal node hash tampering
        {
            let mut tampered_storage = log.storage().clone();
            // Find an internal node and tamper it
            let key = (0, 3); // (alg_id, node_id)
            if tampered_storage.nodes.contains_key(&key) {
                tampered_storage.nodes.insert(key, vec![0x00; 32]);
                let tampered_log = NaryMerkleLog::from_storage(tampered_storage, vec![(0, Box::new(Sha256Hasher))]).await.unwrap();
                assert!(
                    !tampered_log.verify_non_divergence(None, &[]).await.unwrap(),
                    "Failed to detect tampered internal node hash"
                );
            }
        }

        // 3. Epoch metadata tampering
        {
            let mut tampered_storage = log.storage().clone();
            // Shorten the active epoch interval for algorithm 0
            if let Some(epochs) = tampered_storage.algorithm_metas.get_mut(&0) {
                if !epochs.is_empty() {
                    epochs[0].1 = 10; // set arbitrary frozen boundary where it should be active (u64::MAX)
                }
            }
            let tampered_log = NaryMerkleLog::from_storage(tampered_storage, vec![(0, Box::new(Sha256Hasher))]).await.unwrap();
            assert!(
                !tampered_log.verify_non_divergence(None, &[]).await.unwrap(),
                "Failed to detect tampered epoch metadata"
            );
        }
    });
}
```

---

### Recommendation 3: Add Metamorphic Relations to Auditing proptests
Ensure that audit checks obey size monotonicity: if the log is audit-valid at size $N$, then auditing any checkpoint size $M < N$ using historical checkpoint roots must also be valid.

```rust
// Draft code block for Metamorphic Monotonicity checks
// Paste into neml/tests/proptests.rs

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]
    
    #[test]
    fn metamorphic_non_divergence_monotonicity(
        size in 5usize..40,
        checkpoint_size in 1usize..39,
    ) {
        smol::block_on(async {
            let k = 2;
            let checkpoint = checkpoint_size.min(size - 1) as u64;
            let log = build_log(size, 0, k).await;

            // Compute trusted roots at historical checkpoint size
            let mut trusted_roots = Vec::new();
            for (&alg_id, _) in log.storage().load_algorithm_metas().await.unwrap().iter() {
                if let Ok(root) = log.root_for_at(alg_id, checkpoint).await {
                    trusted_roots.push((alg_id, root));
                }
            }

            // If the full log is consistent:
            if log.verify_non_divergence(None, &[]).await.unwrap() {
                // Then auditing the sub-checkpoint MUST also pass
                prop_assert!(
                    log.verify_non_divergence(Some(checkpoint), &trusted_roots).await.unwrap(),
                    "Metamorphic Monotonicity violated: audit failed at checkpoint={}", checkpoint
                );
            }
            Ok(())
        })?;
    }
}
```

---

### Recommendation 4: Add Input Boundary Fuzzing for coupling proofs
Assert robustness of `CouplingProof::verify` under malformed/adversarial inputs to mitigate potential Denial-of-Service (DoS) and signature validation bypasses.

```rust
// Draft code block for input fuzzing
// Paste into neml/tests/integration.rs

#[test]
fn test_coupling_proof_edge_case_fuzzing() {
    let hasher = Sha256Hasher;
    let root_0 = vec![0; 32];
    let root_1 = vec![1; 32];

    let proof = neml::CouplingProof {
        active_roots: vec![(0, root_0.clone()), (1, root_1.clone())],
    };

    // Calculate correct combined root
    let mut buf = Vec::new();
    buf.extend_from_slice(&0u64.to_be_bytes());
    buf.extend_from_slice(&32u64.to_be_bytes());
    buf.extend_from_slice(&root_0);
    buf.extend_from_slice(&1u64.to_be_bytes());
    buf.extend_from_slice(&32u64.to_be_bytes());
    buf.extend_from_slice(&root_1);
    let combined_root = hasher.hash(&buf);

    let config = neml::VerifierConfig::default();

    // 1. Unsorted expected algorithms rejection
    assert!(
        proof.verify(&hasher, 0, &combined_root, &[1, 0], config).is_none(),
        "Accepted unsorted expected algorithms"
    );

    // 2. Duplicate expected algorithms rejection
    assert!(
        proof.verify(&hasher, 0, &combined_root, &[0, 0], config).is_none(),
        "Accepted duplicate expected algorithms"
    );

    // 3. DoS limit threshold verification
    let doS_config = neml::VerifierConfig { max_active_algorithms: 1 };
    assert!(
        proof.verify(&hasher, 0, &combined_root, &[0, 1], doS_config).is_none(),
        "Allowed verification exceeding max_active_algorithms limit"
    );

    // 4. Verification with empty roots (must not crash)
    let empty_proof = neml::CouplingProof { active_roots: vec![] };
    assert!(
        empty_proof.verify(&hasher, 0, &combined_root, &[0, 1], config).is_none()
    );
}
```
