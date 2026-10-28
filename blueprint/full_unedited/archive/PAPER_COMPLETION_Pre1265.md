# Completion of the reviewed corrected paper

The internal formalization is complete within the agreed conditional scope. The complete inventory has 54 numbered theorem, proposition, lemma and corollary targets and four definitions. There are 22 claims proved under ordinary source hypotheses, 31 complete implications from explicit independent inputs, one quoted external theorem, and no open internal numbered endpoint. The four definitions are formalized. These counts measure statement coverage and are not proof-completion percentages.

| Main result | Current checked evidence | Scope |
| --- | --- | --- |
| Theorem 1.1 | theorem_1_1, theorem_1_1_restricted, theorem_1_1_strong_real | Complete conditional improving estimates for the actual averages and source normalization |
| Theorem 1.3 | theorem_1_3, theorem_1_3_endpoint, theorem_1_3_open_pq | Complete conditional sparse domination, endpoint and open triangle |
| Theorem 1.5(i) | theorem_1_5_i | Complete conditional persistent universal L1 badness |
| Theorem 1.5(ii) | theorem_1_5_ii_closed_signed_maximal | Complete conditional near-L1 ergodic maximal estimate; signed maximal input proved internally |
| Theorem 7.2 | theorem_7_2_closed_signed_maximal | Complete conditional three-family quantitative Orlicz theorem |
| Corollaries 7.6 and 7.46 | corollary_7_6_closed_signed_maximal, corollary_7_46_closed_signed_maximal | Complete conditional Lp maximal, transfer and convergence conclusions |
| Quantitative Goldbach theorem | goldbach_section9_headline_complete | Complete conditional estimate at all sufficiently large real cutoffs, with arithmetic criterion and smooth seed proved internally |

The current continuation proves the general finite signed-sum maximal theorem at constant 6. Its binary bound holds for every exponent at least one, including all finite lengths and extended norm bounds. Exact Boolean-sign averaging and the Lp triangle inequality replace its former independent hypothesis. The public Section 7 and near-L1 exports consume this proof. The prior primitive two-square criterion, W(alpha) integrability for every alpha>1 and concrete smooth seed remain proved and integrated.

The paper-wide audit independently checks every declared theorem-like environment type, all source labels and statement hashes, all four definitions and all current evidence anchors. Lean prints the exact types of those declarations. The audit verifies removal of the signed maximal hypothesis from the four public exports and of the primitive criterion from the current Section 9 arithmetic/headline exports. Source scans, authenticated compilation receipts and complete transitive axiom audits cover the proof files. The only allowed foundational axioms are propext, Classical.choice and Quot.sound. Numerical experiments remain supplementary and are not Lean proofs; unchanged verified probes are preserved without redundant reruns.

Independent general inputs remain unproved, including the PNT/progression, Ren/Ghosh, multifrequency, IW/sampling, general real-variable and ergodic, Weil, and general sieve/Mertens/effective mean interfaces. Their exact scopes and still-unproved formulation bridges are listed in INDEPENDENT_INPUTS_CURRENT.md and the proof registry. This is a partial formalization of the mathematics used by the paper, with complete own-paper deductions in the agreed scope. An axiom audit does not establish the truth of explicit input hypotheses. The quoted Granville–Kurlberg theorem is external and optional for the badness conclusion.

The completeness target is the selected full source plus the explicitly supplied corrected Section 11 presieving statement. The weaker original presieving statement is not claimed. The user is applying manuscript edits; application is pending verification against a revised upload. No original source file is changed and no additional replacement passage is needed from this continuation. Stronger unnumbered assertions in alternative proof routes retain their separate documented scopes.

See blueprint/Paper_Proof_Status.json and blueprint/Paper_Proof_Status.csv for exact per-statement evidence. verification/paper-completion-current.json records the final coverage checks; verification/paper-declaration-types-current.log records the actual Lean types. Read docs/Remaining_Work_Plan.md for source synchronization and the separately optional independent-input projects.
