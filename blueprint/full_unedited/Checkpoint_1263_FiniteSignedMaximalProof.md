# Checkpoint 1263: General finite signed maximal inequality proved

The general finite signed-sum maximal inequality is now proved without an independent analytic hypothesis. For any finite sequence of complex functions on the integers and every exponent at least one, a uniform Lp bound B for all sums with scalar coefficients of modulus at most one gives an Lp bound (ceil(log2 J)+1) B for the largest initial partial sum. The checked depth comparison gives the explicit bound 6 log(2+J) B. This proves the exact existing RawFiniteSignedMaximalInput interface at constant 6, including J=0, Lp membership, and extended-real B.

The proof uses exact finite Boolean-sign orthogonality and reconstruction. Each coordinate is dominated by the finite average of the norms of all signed sums. Minkowski then bounds the largest block at each level, and an aligned binary decomposition bounds every initial partial sum. There is no probabilistic oracle, Khintchine hypothesis, numerical testing dependency, new axiom, or unchecked evaluation in this argument.

This is a general theorem, not a new paper endpoint assumption. The next milestone consumes the proved constant in the public Section7 and near-L1 exports and completes the paper-wide source/assumption audit. All 54 numbered paper targets retain their existing source statuses; no extra paper result is counted merely because supporting lemmas were added. The deep inputs previously excluded from scope remain explicit. The user is applying manuscript edits, and no revised upload is presumed.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| FiniteSignedMaximalProof.lean | 16 |

- `finiteBooleanSign_norm`
- `finiteBooleanSign_not`
- `finiteBooleanSign_self`
- `finiteBooleanSign_orthogonality`
- `finiteBooleanSign_reconstruction`
- `finiteSignAverage_nonneg`
- `finiteSignAverage_dominates`
- `finiteSignAverage_Lp`
- `signed_block_partition`
- `finiteBooleanSignLift_norm`
- `signedBlockFamily_sum`
- `signed_binary_strict_prefix_bound`
- `signed_binary_prefix_bound`
- `finite_signed_maximal_binary`
- `finite_signed_binary_log_bound`
- `rawFiniteSignedMaximalInput_proved`

<!-- checkpoint-verification -->

## Verification

All 1380 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5177-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4510 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1382 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. All Section9 arithmetic reductions are proved for the adopted closed L without an extra primitive two-square hypothesis. The full real-X Goldbach estimate and exceptional-density limit follow from the documented independent analytic inputs, with the smooth seed constructed internally; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; All Section11 theorem statements, using the explicitly supplied corrected presieving replacement, are complete in the agreed conditional scope. The common-cutoff lower/upper assembly, exact constants and complete error estimates are proved; the original manuscript still needs the supplied replacements. Independent general effective mean-value and classical Mertens hypotheses remain explicit and unproved; all own weighted upper main-term deductions are complete. Earlier independent theorem scopes are unchanged. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The full weighted upper main-term comparison l:wumatomakisum is a complete checked implication from the documented independent effective mean-value and Mertens inputs, with the exact printed constant and uniform retained-range quantifiers. The complete upper-sieve proposition and strict numerical comparison are proved conditionally with exact constants and uniform quantifiers. The joint Section11 estimates are proved at one cutoff. The full quantitative Goldbach theorem is proved conditionally at every large real cutoff X; the supplied presieving replacement still needs to be copied into the user manuscript. Section9 also includes a proved full primitive two-square criterion and convergence of W(alpha) for every alpha>1. The old parameterized theorems remain for compatibility; the current matched exports remove those discharged parameters. The user is applying manuscript edits and their application has not been verified against a new upload.
