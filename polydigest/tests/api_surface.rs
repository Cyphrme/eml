//! Compile-level API-surface checks for the `Storage` trait redesign
//! (head's ruling, 2026-09-17): exactly one mutating entry point (C), and
//! the legacy linear-probe fallback is gone outright (B).
//!
//! Parses this crate's own source with `syn`, mirroring `storage-git`'s own
//! syn-based tripwires (`storage-git/tests/acceptance_encodings.rs`'s
//! `no_reconstruction_*` checks) rather than trusting a doc comment's claim.

use std::path::Path;

use syn::visit::{self, Visit};

fn manifest_src(rel: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(rel);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn parse(rel: &str) -> syn::File {
    let text = manifest_src(rel);
    syn::parse_file(&text).unwrap_or_else(|e| panic!("{rel}: failed to parse as Rust: {e}"))
}

/// Every `fn` signature whose first parameter is `&mut self`, found inside
/// `trait Storage { .. }` specifically (never an inherent impl or another
/// trait) -- collected by walking every `ItemTrait` in the file and keeping
/// only the one named `Storage`.
struct StorageTraitVisitor {
    mutating_methods: Vec<String>,
    all_methods: Vec<String>,
    found_trait: bool,
}

impl<'a> Visit<'a> for StorageTraitVisitor {
    fn visit_item_trait(&mut self, node: &'a syn::ItemTrait) {
        if node.ident == "Storage" {
            self.found_trait = true;
            for item in &node.items {
                if let syn::TraitItem::Fn(f) = item {
                    self.all_methods.push(f.sig.ident.to_string());
                    let takes_mut_self = f.sig.inputs.iter().any(|arg| {
                        matches!(
                            arg,
                            syn::FnArg::Receiver(r) if r.mutability.is_some()
                        )
                    });
                    if takes_mut_self {
                        self.mutating_methods.push(f.sig.ident.to_string());
                    }
                }
            }
        }
        visit::visit_item_trait(self, node);
    }
}

/// [OPERATION ENUM] `Storage` has exactly one method taking `&mut self`:
/// `apply`. Demonstrated by mutation: reintroducing any of the retired
/// standalone mutators (`store_leaf`, `store_node`, `store_algorithm_meta`)
/// or a second `&mut self` method turns this red immediately, without
/// needing to inspect a single call site.
#[test]
fn storage_trait_has_exactly_one_mutating_method() {
    let parsed = parse("src/storage.rs");
    let mut visitor = StorageTraitVisitor {
        mutating_methods: Vec::new(),
        all_methods: Vec::new(),
        found_trait: false,
    };
    visitor.visit_file(&parsed);

    assert!(
        visitor.found_trait,
        "sanity: could not find `trait Storage` in src/storage.rs -- has it moved or been renamed?"
    );
    assert_eq!(
        visitor.mutating_methods,
        vec!["apply".to_string()],
        "OPERATION ENUM: `Storage` must have exactly one `&mut self` method (`apply`); found {:?} \
         among all methods {:?}",
        visitor.mutating_methods,
        visitor.all_methods
    );
}

/// [OPERATION ENUM] `Storage::apply` takes a slice of `WriteOp`, the closed
/// enum -- not five parallel optional parameters. Checked by shape: exactly
/// one non-`self` parameter, and its type's token text mentions `WriteOp`.
#[test]
fn storage_apply_takes_a_write_op_slice_not_five_parameters() {
    let parsed = parse("src/storage.rs");
    struct ApplySigVisitor {
        found: Option<syn::Signature>,
    }
    impl<'a> Visit<'a> for ApplySigVisitor {
        fn visit_item_trait(&mut self, node: &'a syn::ItemTrait) {
            if node.ident == "Storage" {
                for item in &node.items {
                    if let syn::TraitItem::Fn(f) = item {
                        if f.sig.ident == "apply" {
                            self.found = Some(f.sig.clone());
                        }
                    }
                }
            }
            visit::visit_item_trait(self, node);
        }
    }
    let mut visitor = ApplySigVisitor { found: None };
    visitor.visit_file(&parsed);
    let sig = visitor
        .found
        .expect("sanity: Storage::apply must exist to check its shape");

    let non_self_params: Vec<&syn::FnArg> = sig
        .inputs
        .iter()
        .filter(|a| !matches!(a, syn::FnArg::Receiver(_)))
        .collect();
    assert_eq!(
        non_self_params.len(),
        1,
        "OPERATION ENUM: apply must take exactly one non-self parameter (a WriteOp slice), found \
         {}",
        non_self_params.len()
    );
    if let syn::FnArg::Typed(pt) = non_self_params[0] {
        let ty_tokens = quote_to_string(&pt.ty);
        assert!(
            ty_tokens.contains("WriteOp"),
            "OPERATION ENUM: apply's one parameter must be a WriteOp slice, got token text {:?}",
            ty_tokens
        );
    }
}

fn quote_to_string(ty: &syn::Type) -> String {
    use quote::ToTokens;
    ty.to_token_stream().to_string()
}

/// [NON-OPTIONAL META] `determine_global_size`, the legacy linear-probe
/// fallback `from_storage_with_config` used when no log metadata had been
/// persisted, is gone outright -- not merely unreachable dead code. Checked
/// by name across every source file in `src/`, since `append_count` (never
/// `Option`) leaves no caller for it.
#[test]
fn determine_global_size_does_not_exist() {
    let src_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    for entry in std::fs::read_dir(&src_dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("rs") {
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap();
        assert!(
            !text.contains("determine_global_size"),
            "NON-OPTIONAL META: {} still mentions determine_global_size -- the legacy \
             linear-probe fallback must be gone outright, not merely unreachable",
            path.display()
        );
    }
}
