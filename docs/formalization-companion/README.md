# English catalogue for all of Part II

The expanded PDF covers Theorems A, B and C and 46 substantial supporting
propositions or construction theorems, grouped into 49 entries with 166 distinct
Lean declaration pointers. The first page explicitly discloses AI-generated
prose and result summaries. Main notation follows Part II.

The editable result index is `results.json`; `scripts/build_catalogue.py`
generates the six TeX result sections and the exact selected-root axiom audit.
Each entry records its assumptions, universe, manuscript context, declaration
names, clickable source files and construction/reuse notes. The conditional
recognition and reflection criteria are distinguished from unconditional main
results. The fonts retain the Part I companion's Latin Modern text and standard
LaTeX mathematics.

From the repository root, regenerate the sections, then compile:

```sh
python3 scripts/build_catalogue.py
cd docs/formalization-companion
latexmk -lualatex -interaction=nonstopmode -halt-on-error -outdir=../../build/catalogue main.tex
```

The final PDF is `part2-lean-formalization-companion-en.pdf` in this directory
and is also a release asset. The historical C-focused PDF remains available
from the unchanged v0.1.0-rc1 tag and release.

The catalogue distinguishes current selected-root local kernel checks from
historical whole-owner audits, a cold full build, hosted Linux CI, Comparator
and independent human review.
