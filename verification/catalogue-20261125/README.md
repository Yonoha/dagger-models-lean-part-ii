# Current Part II catalogue verification

The expanded English catalogue has 49 grouped results (three main theorems plus
46 supporting groups), mapped to 166 distinct declaration roots in 80 owner
modules. This is an AI-assisted selection and correspondence record, not human
certification or a count of independent new theorems.

- [Exact catalogue roots](CheckCatalogueAxioms.lean).
- [Current transitive axiom log](catalogue-axioms.log).
- [Current source/import/hash receipt](catalogue-audit.json).
- [Main A/B/C alias compile log](main-a-b-c.log).
- [Historical A/B milestone and current drift boundary](a-b-history.json).
- [Log-validator controls](validator-controls.json).

The current selected-root Lean compilation exited zero; every advertised root
has only standard transitive axioms. The A/B/C aliases were freshly compiled
with original statement types. The 68 native owner roots and the A/B proof
graphs passed original-workspace content-rehash/no-build freshness checks.
The new local layout uses verified original import caches. This is not a cold
full build, hosted Linux CI, real Comparator or independent human review.

The machine-readable `docs/formalization-companion/results.json` is hash-bound
to the audit. `scripts/verify_catalogue.py` checks exact coverage, source hashes,
log hashes and allowed axioms. `--axioms PATH` validates a fresh Lean audit log.
Negative controls reject an injected nonstandard axiom *in a copied log* and a
missing advertised root; they do not inject an axiom into Lean or compare a
weakened theorem statement.

Three bounded AI inventories covered A, B and frame theory. A separate agent
cross-checked the six most sensitive strict/derived/cofibrancy/reflection
summaries and found no correction needed. All remaining premises are displayed.
The Rezk criterion is the sufficient component-surjectivity implication, not
the manuscript's full iff characterization. The zero-vertex reflection theorem
retains its explicit Quillen premise. Conditional strictification interfaces
are not advertised as unconditional proofs.
