# Checkpoint 783: Complete the square-sign reflection and integrate it into Theorem 1.1

The requested square-sign reflection is complete. The new PositiveFullSquareDecompositionInput states the independent ordinary-square global high/low hypothesis using the literal x+n^2 kernel. Lean proves it equivalent to the existing FullSquareDecompositionInput at exactly the same constant C, then derives the existing minus-sign and plus-sign annular inputs with the already proved factor 3C. The final theorem_1_1_from_positive_square_input accepts the positive-sign global hypothesis and returns both existing conclusions of Theorem 1.1 for the paper's actual minus-sign prime-square average, without adding an analytic assumption. The literal von-Mangoldt sum and the reflected source interval [-2N^2,N^2] are checked. Together with checkpoints779-782 this proves the lp isometries through infinity, general convolution and pairing identities, high/low/error constant transfer, full/annular formulas, actual maximal-bound transfer and support/localization changes. Reflection is removed from the unformalized boundary; the independent ordinary-square analytic theorem and its local-to-global passage remain explicit global hypotheses. The manuscript is unchanged. Current external-input, statement-review, completion and work-plan documents are reconciled; paper claim statuses remain 10 proved,3 conditional,6 partial,1 external candidate,34 open. The blueprint-length report distinguishes topic/reference notes, individual checkpoint expositions and overlapping batch summaries; the old 19-page PDF is only the initial blueprint, and there is no current combined PDF. See docs/SQUARE_REFLECTION_COMPLETION.md and docs/BLUEPRINT_LENGTH.md.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| SquareDecompositionReflection.lean | 8 |

- `fullSquareDecompositionInput_sign_iff`
- `fullSquare_decomposition_from_plus`
- `plusSquare_decomposition_from_minus`
- `positiveFullSquare_decomposition_annular`
- `positiveFullSquare_decomposition_annular_plus`
- `primeSquareSourceInterval_reflection`
- `primeSquareAverageValue_reflection`
- `theorem_1_1_from_positive_square_input`

<!-- checkpoint-verification -->

## Verification

All 850 project modules and the root were freshly rebuilt: 4457 jobs pass without warnings/errors. All 2187 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 852 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results under their paper hypotheses remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. In addition, Lemma 3.21 and BOTH conclusions of Theorem 1.1 are complete checked implications under their explicit independent deep inputs. The PNT limits are used in the sharp Gauss/high bound; an imported PNT bridge is not integrated. Both source clauses of Proposition 6.21 are also complete checked implications under their recorded independent inputs. The whole paper, Proposition 4.19 and the later headline applications remain unfinished. See docs/THEOREM_1_1_EXTERNAL_INPUTS.md. PNT limits, raw compatible progression/Ren/Ghosh data, and the global independent square decomposition remain explicit hypotheses. Reflection between plus and minus square translations is proved without any extra analytic assumption. The smooth multifrequency boundary is only for later maximal applications.
