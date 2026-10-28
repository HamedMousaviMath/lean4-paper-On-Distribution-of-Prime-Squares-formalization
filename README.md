# Prime Squares: a conditional Lean formalization

A formalization of Hamed Mousavi's **On the Distribution of Prime Squares and Its Applications**.

Start with [the compact blueprint](docs/PrimeSquares_Blueprint.pdf), the [paper map](docs/PAPER_MAP.md), and the [independent-input catalogue](docs/ASSUMPTIONS.md).

## Mathematical scope

The numbered ledger contains **22 proved results under their source hypotheses, 31 complete conditional implications, and one quoted external theorem**, plus **four formalized definitions**. The headline improving, sparse, ergodic and Goldbach results are conditional on the exact independent inputs recorded in Lean. The optional Granville–Kurlberg spacing theorem is not used by the persistent-badness headline.

There are no `sorry` placeholders or added mathematical axioms in the proof library. This does **not** remove explicit hypotheses: their truth, and the bridges from published results to the exact interfaces, remain outside this formalization. A kernel axiom audit alone does not certify those hypotheses or the paper-to-Lean correspondence.

## Blueprint and implementation

The public blueprint has **52 nodes**: 39 mathematical groups and 13 groups of independent inputs. It covers every numbered result and definition, with a DAG, `uses` / `proves` tags and exact Lean targets. Small calculations remain in the proof implementation, not in the public graph.

The implementation retains its 1,382 existing modules and the `PrimeSquares` namespace. These files have not been merged or renamed: doing so would be a separate refactor and would require a fresh build. [The module index](docs/MODULE_INDEX.md) supplies the compact subject navigation. The complete original notes are now included under [`blueprint/full_unedited/`](blueprint/full_unedited/INDEX.md), with an index and original hashes. Historical notes are preserved unedited and do not override the current scope ledger.

## Reproduce the Lean checks

Install Lean via elan, then run from this directory:

```sh
lake exe cache get
lake build
python3 scripts/check_source.py
python3 scripts/check_axioms.py
lake env lean scripts/CheckBlueprint.lean
lake env lean scripts/CheckHeadlines.lean
python3 scripts/verify_release.py
```

The Lean version and Mathlib revision are pinned in `lean-toolchain` and `lake-manifest.json`. `CheckHeadlines.lean` exposes the actual types and axioms; this package does not claim an independent Comparator certification.

The saved full build at proof checkpoint 1265 covered 1,382 project modules, 4,517 named theorem axiom audits and 973 evidence declaration signatures. Publication package 1266 preserves those proof bytes exactly. A new Lean build was **not** run for this documentation-only release: the temporary Lean runtime and compiled cache were unavailable. The new manuscript, blueprint source, PDF, web output, graph and source identities were checked separately. GitHub CI is supplied but has not run on GitHub.

## Build the blueprint

Install TeX Live with pdfLaTeX, latexmk and the usual AMS packages. For HTML also install Graphviz and `pip install -r blueprint/requirements.txt`.

```sh
python3 scripts/render_blueprint.py
cd blueprint/src
latexmk -output-directory=../print
plastex -c plastex.cfg web.tex
```

The standard `leanblueprint pdf` and `leanblueprint web` commands also work after `git init` at the project root. Use the supplied `lake env lean scripts/CheckBlueprint.lean` for declaration checking; no extra `checkdecls` dependency is added. The generated `content_web.tex` only omits empty leaf dependency commands and adapts two literal command names for plasTeX; mathematical content is shared with `content.tex`.

To view the generated web blueprint locally:

```sh
python3 -m http.server --directory blueprint/web 8000
```

Open `http://localhost:8000/`. MathJax rendering requires internet access.

## Files

- `PrimeSquares/`, `PrimeSquares.lean`: unchanged checked proof implementation.
- `paper/`: manuscript and PDF under the updated title, plus the supplied bibliography; exact original source/PDF preserved in `paper/archive/`.
- `blueprint/src/`: standard leanblueprint LaTeX sources and generated web variant.
- `blueprint/nodes.json`: curated graph and proof-architecture summaries.
- `blueprint/full_unedited/`: all 1,303 original blueprint artifacts, with topic/checkpoint navigation.
- `blueprint/full_unedited_manifest.json`: byte-for-byte preservation record.
- `blueprint/web/`: compiled HTML and interactive dependency graph.
- `docs/`: compact blueprint PDF, paper/module maps, scope and author note.
- `scripts/`: source, axiom, declaration and release checks.
- `verification/`: saved proof evidence and current packaging checks.

## Author action before publication

[AUTHOR_ACTIONS.tex](docs/AUTHOR_ACTIONS.tex) replaces the new acknowledgement's phrase “complete formalization” with an accurate statement of the conditional scope. The supplied manuscript files are preserved exactly, so this wording change has not been silently applied. The previous duplicate-display and missing-citation issues are resolved.

No repository has been published and no new license is assigned by this package. Choose the desired license as author before licensing the public repository. The repository layout is inspired by the Lacey et al. Hua formalization; its mathematical text and code are not copied.

## Title and full-archive update

The title is **On the Distribution of Prime Squares and Its Applications**. Only the title is changed in the current manuscript source; all 58 numbered result/definition bodies and all Lean proof files are unchanged. The compact PDF is the analogue of the current-paper part of the supplied 866-page Hua blueprint. That reference also contains an earlier draft and about 771 pages of Lean listings. Here the full Lean implementation is supplied as source files, and all unedited blueprint notes are included alongside the compact exposition. See [the comparison note](docs/HUA_BLUEPRINT_COMPARISON.md).
