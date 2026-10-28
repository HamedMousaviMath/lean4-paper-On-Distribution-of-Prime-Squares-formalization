# Dependency-driven roadmap for Draft5

Source: the archived 99-page paper in `sources/current/`, with the accepted
Lemma 3.14 fragment in `sources/updates/` and status in `docs/SOURCE_UPDATE_08.md`. Progress is organized
by mathematical dependencies; the statement inventory preserves the section
and label correspondence. This avoids redoing definitions when a proof in a
later section supplies an input used earlier.

| Stage | Main work | Paper location | Checkpoint status |
|---|---|---|---|
| 0 | Lock sources, reproduce references, state the trust boundary | Whole paper | Current files locked; 58 statements inventoried |
| 1A | Quadratic Cohen identity: prime and prime-power local factors | Section 3, `l:cohenquadratic` | Complete Lemma 3.1; see Cohen_Identity.md |
| 1B | CRT and the global product; progression-restricted correlations | Remaining first part of Section 3 | Complete 3.11, 3.12, accepted 3.14/3.16 and original 3.20 |
| 1C | Gauss-sum bounds and exceptional-character arithmetic | Remaining Section 3 | Full 3.21 with explicit PNT limits; full 3.24 for all complex characters and full 3.27 for all real characters, both unconditional |
| 2 | Abstract high--low optimization and improving inequalities | Section 4, Theorem 4.1 and Corollary 4.15 | Complete: both abstract endpoints, full strong interior interpolation and p=2, actual complex lp operators, exact N scaling and uniform constants |
| 3 | Establish the prime-square high--low inputs and connect the first main theorem | Section 6, Proposition 4.19 and Theorem 1.1 | The actual current user upload is matched to the completed formalization in the agreed conditional scope. No internal numbered source claim remains open. |
| 4 | Stopping intervals, local estimates, sparse recursion | Section 5, `t:sparsebound` | Both source Theorem1.3 clauses complete conditional at checkpoint828; actual sparse major subsets and all-cutoff maximum are proved. General auxiliary source lemmas remain partial. |
| 5 | Quantitative maximal and Orlicz estimates | Section 7, `t:orlicz-maximal` | Partial at checkpoint846: gauge, scalar growth/moment, finite layers and general modular deductions proved; actual IW low/high, restricted bound, strong lp and ergodic conclusions unfinished. |
| 6 | Local density correlations and the badness criterion | Section 8, first part of `t:pet` | Open |
| 7 | Sieve reductions, local densities, circle method, final error assembly | Sections 9--11, `t:repmotthm` | Open; earlier finite support lemmas available |

Within each stage:

1. Expand the selected statement into definitions and a dependency graph, with
   all parameter restrictions and exceptional cases visible.
2. Find the relevant Mathlib declarations in the pinned source before writing
   replacement infrastructure.
3. Prove a coherent mathematical unit; include the q=1, small-prime, zero,
   support, and endpoint cases relevant to that unit.
4. Build all project imports and audit every named theorem's transitive axioms.
5. Use exact finite experiments when they can expose an error. Record their
   range and arithmetic; never count them as an unbounded proof.
6. Update the status, proof specification, and continuation note; save the
   checkpoint before proceeding to the next substantial unit.

The current branch does not contain unfinished Lean proof stubs. Open targets
live in the blueprint. No main theorem is counted as proved until its precise
statement and every input have been connected, with any deep external
hypotheses displayed in the final theorem.
