# Models for dagger categories II: Lean companion

This is the separate, **AI-assisted** Lean companion to *Models for dagger
(infinity,1)-categories II: Dagger complete Segal spaces and the dagger
Joyal--Tierney equivalence*, by Keima Akasaka. The prose and English catalogue
were generated with AI assistance. Independent human correspondence review is
pending.

## Start here

- **[English catalogue of Theorems A, B, C and major results (PDF)](docs/formalization-companion/part2-lean-formalization-companion-en.pdf)**.
- **[Fixed paper-facing release: v0.1.0-rc2](https://github.com/Yonoha/dagger-models-lean-part-ii/releases/tag/v0.1.0-rc2)**.
- [Main A/B/C entry points](lean/MainTheoremsPartII.lean).
- [Catalogue source, grouped result index and build instructions](docs/formalization-companion/README.md).
- [Current selected-root verification](verification/catalogue-20261125/README.md).
- [Exact original Theorem C correspondence](docs/THEOREM_C.md).
- [Machine-readable status](formalization.yaml) and [citation metadata](CITATION.cff).

The expanded catalogue has **49 grouped results**: three main theorems and
46 substantial supporting propositions or construction theorems, linked to
166 distinct Lean declarations. It covers the resolution model, dagger Segal
models, actual change of index, model-category generation, Borel and word-cell
theory, frames and density, recognition, and ordinary completion.
Groups overlap through their dependencies; this is not a count of independent
new mathematical theorems.

Theorem A retains its original universe parameter. Theorem B means the **full**
statement with native simplicial enrichment, literal Hom comparison, tensor,
cotensor and naturality data at value universe zero. Theorem C is the unchanged
original universe-zero four-link statement, with its models, adjoints, directions
and ordered endpoints retained. The current A/B/C aliases and all 166 catalogue
roots passed local Lean checks with standard transitive axioms only.

The current check uses verified existing imports and source-freshness gates.
It is not a cold full build of this repository, a new Linux CI or Comparator
pass, or independent human certification. Each conditional recognition or
reflection entry states its actual premises. Contextual manuscript labels do not
claim that every clause of every manuscript proposition has been formalized.

## Build

Install the toolchain in `lean-toolchain`, then run from this repository root:

```sh
lake update
lake build MainTheoremsPartII
lake env lean verification/catalogue-20261125/CheckCatalogueAxioms.lean
```

The first build can be substantial. Part I is a Git dependency fixed at
[`9ee62295a79ef61269259e27216afc0292458931`](https://github.com/Yonoha/dagger-models-lean/commit/9ee62295a79ef61269259e27216afc0292458931).
Its Mathlib pin and Lean 4.27.0 toolchain are retained. No Part I source tree is
copied into this repository.

For fast checks of the saved source inventory and exact catalogue evidence:

```sh
python3 scripts/verify_snapshot.py
```

The optional GitHub workflow is manual. It is not triggered for publication.

## Layout

| Location | Contents |
| --- | --- |
| `lean/MainTheoremsPartII.lean` | The original A, full B and four-link C |
| `lean/DaggerModelsPartII/` | Part II definitions and auxiliary developments |
| `lean/TheoremCStages/` | The 359 unchanged named stages used by the final C proof |
| `docs/formalization-companion/` | English PDF, editable LaTeX and result index |
| `verification/catalogue-20261125/` | Current 166-root audit and explicit verification scope |
| `verification/theorem-c-20261125/` | Earlier C-specific local evidence |
| `scripts/` | Deterministic catalogue, evidence and release tools |

The stage library keeps its original bare module names through a separate source
root. Native Part II modules retain their `DaggerModelsPartII` names.

## Citation and provenance

Use [v0.1.0-rc2](https://github.com/Yonoha/dagger-models-lean-part-ii/releases/tag/v0.1.0-rc2)
or its exact commit for a fixed paper reference. The earlier
[v0.1.0-rc1](https://github.com/Yonoha/dagger-models-lean-part-ii/releases/tag/v0.1.0-rc1)
remains the C-focused historical snapshot.

See [publication scope](PUBLICATION.md) and [third-party notices](THIRD_PARTY_NOTICES.md).
The [Part I companion](https://github.com/Yonoha/dagger-models-lean) and its
releases remain unchanged. From a clean committed checkout, regenerate the
source archive, PDF copy and checksums with `python3 scripts/build_release_bundle.py`.
