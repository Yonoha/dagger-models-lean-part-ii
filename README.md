# Models for dagger categories II: Lean companion

This is the separate, **AI-assisted** Lean companion to *Models for dagger
(infinity,1)-categories II: Dagger complete Segal spaces and the dagger
Joyal--Tierney equivalence*, by Keima Akasaka.
The prose and English result catalogue were generated with AI assistance.
Independent human review of the manuscript correspondence is pending.

## Start here

- [English catalogue (PDF)](docs/formalization-companion/part2-theorem-c-companion-en.pdf).
- [Original Theorem C: statement and correspondence](docs/THEOREM_C.md).
- [Paper-facing Lean entry point](lean/MainTheoremCPartII.lean).
- [Full final proof](lean/TheoremCStages/TheoremCOriginalCompletionProof.lean)
  and [literal checks of the four links](lean/TheoremCStages/TheoremCOriginalFourLinksAudit.lean).
- [Verification scope and saved evidence](verification/theorem-c-20261125/README.md).
- [Machine-readable formalization status](formalization.yaml).

The proved target is the original universe-zero
`DaggerModels.PartII.TheoremCStatement.statement`, with no extra hypotheses.
It contains all four original Quillen equivalences, with the original models,
adjoints, directions and ordered endpoints. Completeness of the original input
is not added as an assumption. The main theorem and the four individual links
have successful local Lean checks using only `propext`, `Classical.choice` and
`Quot.sound`.

This release candidate preserves the checked sources and local evidence.
It does not claim a fresh full build of this separate repository, a Linux CI
or Comparator pass, or independent human certification.
Earlier auxiliary Part II developments are included as source, without claiming
that each of them is needed by the final Theorem C proof.

## Build

Install the Lean toolchain named in `lean-toolchain`, then run:

```sh
lake update
lake build MainTheoremCPartII
```

The first build can be substantial. Part I is a Git dependency fixed at
[`9ee62295a79ef61269259e27216afc0292458931`](https://github.com/Yonoha/dagger-models-lean/commit/9ee62295a79ef61269259e27216afc0292458931).
Its existing Mathlib pin and Lean 4.27.0 toolchain are retained.
No Part I source tree is copied into this repository.

For a fast source/evidence check without invoking Lean:

```sh
python3 scripts/verify_snapshot.py
```

An optional manual GitHub workflow provides this evidence check and a separately
selected Lean build. It is not automatically run on publication.

## Layout

| Location | Contents |
| --- | --- |
| `lean/DaggerModelsPartII/` | Part II definitions and auxiliary developments |
| `lean/TheoremCStages/` | The 359 byte-identical named stages used by the final proof |
| `lean/MainTheoremCPartII.lean` | Public alias for the original four-link theorem |
| `docs/formalization-companion/` | English PDF and editable LaTeX |
| `verification/` | Saved, explicitly scoped local verification evidence |
| `scripts/` | Source and evidence checker |

The stage library has its own source directory, so its original bare module
names and imports remain unchanged. The Part II library also retains its
original `DaggerModelsPartII` module names.

## Citation and provenance

Use the dedicated release tag or an exact commit as the paper's fixed link.
The first dedicated release candidate is
[v0.1.0-rc1](https://github.com/Yonoha/dagger-models-lean-part-ii/releases/tag/v0.1.0-rc1).
Its source archive, PDF and checksums can be regenerated from a clean committed
checkout with `python3 scripts/build_release_bundle.py`.
See [publication scope](PUBLICATION.md), [citation metadata](CITATION.cff),
[mathematical correspondence](docs/THEOREM_C.md) and
[third-party notices](THIRD_PARTY_NOTICES.md).
The [Part I companion](https://github.com/Yonoha/dagger-models-lean) and its
existing releases remain separate.
