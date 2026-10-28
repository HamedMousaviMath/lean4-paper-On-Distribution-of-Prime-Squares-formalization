# Checkpoint 1265: Current manuscript review and fresh full rebuild

The current complete manuscript has been reviewed directly against the checked source and Section11 replacement. It retains all54 numbered results and4 definitions with the same stable labels. Of the58 statements,57 are unchanged modulo whitespace. The only rewritten statement is the presieving lemma. Its corrected hypotheses and conclusion are retained, and the rewrite is covered by three new proved Lean equivalences: the old strict D0<D condition follows from the current level chain, and the inline preliminary/outer prime conditions define the same interval products.

The changed proof passages are reviewed separately: both approximation branches and periodized lifts, ordinary unweighted SW/BV major approximation with the strict endpoint and q+1 finite errors, refined interval dimensions, preliminary coefficient bounds, uniform lower/upper sieve levels, exact weighted integration constants and discarded-range absorption. They preserve the checked source conclusions and use the same documented independent inputs. No new independent mathematical hypothesis is introduced.

One cleanup is needed: two consecutive identical displays carry the label e:integratedW10. Keep the first and remove the preceding Therefore plus the second copy. No mathematical replacement is required. The original upload is preserved byte-for-byte; a complete cleaned TeX copy, exact deletion fragment and minimal patch are supplied. All numbered statement bodies are identical between the upload and cleaned copy; the cleanup removes the duplicate label without changing the formalization target.

The entire local project is freshly rebuilt from source, with project build traces removed and remote project artifact reuse disabled. All source scans, complete transitive theorem axiom audits and current paper evidence declaration-type checks are rerun. The project retains pinned Lean4.34.1 and Mathlib revisiond13f23b723b8a846827a245b89c10fc7d3f11612. The final verification below records the actual counts.

All54 numbered targets retain their agreed scopes:22 proved under ordinary source hypotheses,31 complete implications from explicit independent general inputs, one quoted external theorem, and no open internal numbered endpoint. All4 definitions are formalized. The independent deep analytic, sampling, ergodic, Weil and sieve theorem inputs and their formulation bridges remain unproved; the axiom audit checks the deductions and does not establish those input truths. No blanket claim is made for stronger unnumbered alternative-route assertions. The current upload's mathematical edits are verified; the earlier pending manuscript synchronization status is resolved.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachPresieveSourceEquivalence.lean | 3 |

- `goldbach_current_presieve_strict_level`
- `goldbach_current_presieve_preliminary_filter`
- `goldbach_current_presieve_outer_filter`


Bibliography check: the uploaded TeX cites Ghosh1981, which is absent from the bibliography saved with this project. The user's local bibliography was not supplied, so no absence is presumed there. A reviewed bibliography adds only that entry: A.Ghosh, The Distribution of alpha p squared Modulo1, Proceedings of the London Mathematical Society s3-42(2),252–269(1981), DOI10.1112/plms/s3-42.2.252. These details are checked against the primary publisher record at https://doi.org/10.1112/plms/s3-42.2.252. If the user's own .bib already contains that key, no bibliography edit is needed. The reviewed manuscript bundle supplies a matching BibPrimeSquares.bib; all earlier entries are preserved. This is a bibliography repair, not a new mathematical hypothesis or proof.

<!-- checkpoint-verification -->

## Verification

All 1382 project modules and the root were freshly rebuilt: 5179 jobs pass without warnings/errors. All 4517 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 1384 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The complete28 October2026 user upload is reviewed directly: all54 numbered results and4 definitions are matched in the agreed conditional scope. The presieving rewrite retains the corrected hypotheses and is covered by three proved Lean equivalences; no mathematical replacement remains pending. One repeated e:integratedW10 display needs the supplied cosmetic cleanup. The entire project and root are freshly rebuilt from source with full source, theorem-axiom and declaration-type audits. Independent general inputs and their formulation bridges remain explicit and unproved. The original upload and earlier frozen sources are unchanged; a one-display cleanup copy is separately supplied.
