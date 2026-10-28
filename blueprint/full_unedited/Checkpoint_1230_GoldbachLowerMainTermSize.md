# Checkpoint 1230: Complete lower-bound side with uniform main term and common cutoff

All mathematical source claims on the lower-bound side are now complete in the agreed conditional scope. The new main-term endpoint is `goldbach_lower_main_term_size`, matching `l:maintermsize8`. The existing full lower-sieve proposition is strengthened to allow any prescribed minimum cutoff exponent. Their joint application is `goldbach_lower_bounds_complete`, which uses the same chosen R=(log N)^C throughout.

## Uniform actual main-term lower bound

For every A0>0, every fixed C>=A0+6, and all sufficiently large integer N, Lean proves uniformly for n=12 mod24 and N^2(log N)^(-A0)<=n<N^2 that

\[
 X_n\Theta_n(z)\geq k_C N(\log N)^{-(A_0/2+6)},
 \qquad z=N^{8/9},\qquad k_C>0.
\]

Thus C_(A0)=A0/2+6 is an explicit admissible exponent, independent of C. This is the exact uniformity required by the source lemma. The quantities are the actual original arithmetic factor, smoothed singular integral and local-density Euler product; no replacement main term is assumed.

For the dimension constant K, let L=(1+K/log2)/(log2)^2. The proof gives the explicit choice

\[
 k_C=\frac{3}{32L^2(C+1)^2}.
\]

K and the smoothing seed are fixed classical/construction parameters, so the implied constant has the dependencies allowed in the paper.

## Archimedean lower bound and smoothing

For64<=n<=N^2 the interval[sqrt(n)/4,sqrt(n)/2] lies inside the original domain2<=u<=N,2<=n-u^2<=N^2. On it the integrand is at least1/(2(log N)^2). Integrability, nonnegativity, interval restriction and the real part of the original complex integral are proved. Therefore

\[
 H_1(n)\geq\frac{\sqrt n}{8(\log N)^2}
 \geq\frac{N}{8(\log N)^{A_0/2+2}}.
\]

The retained n range eventually implies n>=64; this growth claim is proved. The already proved smoothing estimate has error at most K_psi N/sqrt(R). If C>=A0+6, then for sufficiently large N this is at most N/(16(log N)^(A0/2+2)), uniformly over the retained n range. Hence the actual H_(1,R)(n) is at least N/(16(log N)^(A0/2+2)). No positivity or lower estimate for this actual function is a new hypothesis.

## Actual local products

Every unrestricted factor p(p-1-rho_p(n))/(p-1)^2 with p>=7 is at least1-2/(p-3); the prime5 factor is at least1/2. The original arithmetic factor is proved to be exactly24 times their real product. The already recorded independent interval Mertens input gives

\[
 G_R(1,24,n)\geq
 \frac{12}{L(\log(R+1))^2}
 \geq\frac{12}{L(C+1)^2(\log N)^2}.
\]

Separately, the same input and the actual local density bound give Theta_n(z)^(-1)<=L(log z)^2<=L(log N)^2. Together with phi(24)=8 and the smoothed archimedean lower bound, these yield the stated k_C and exponent. This direct product proof does not assume the paper's own main-term estimate or the more precise asymptotic normalization used in the later weighted upper calculation. That normalization remains part of the upper-side work; it is not needed to close this source lower-bound lemma.

## One common sufficiently large cutoff

The earlier circle-method theorem returned an exponent C, but did not by its statement alone allow C to be enlarged. The new theorems explicitly select C=max(max(CC,CM),Cmin) in the original major/minor assembly. All applicability thresholds are checked again. The cutoff and full circle estimates, selected signed remainder estimate, lower mean-square estimate and complete lower-sieve application are exported with Cmin<=C.

Taking Cmin=A0+6 proves the lower-sieve inequality, its N^4(log N)^(-A) mean-square remainder estimate, and the actual main-term size simultaneously for one shared C and coefficient family chosen before n. This removes the possible mismatch between an existence statement for C and the smoothing requirement on C.

## Positive coefficients and exceptions

Lean proves positivity of the explicit classical half-sieve value sqrt(8 exp(gamma)/(9 pi))*log2 for every real gamma. The classical sieve-function identification/normalization remains in the already recorded classical input boundary; this positivity lemma does not claim to reconstruct that deep theory.

The finite deduction from the lower inequality to positive counts is proved: if v>=T>0, f>0, eta<=f/2 and count>=v(f-eta)+E, then E>=-Tf/4 implies count>=Tf/4. The associated exceptional-set estimate is also proved:

\[
 \#\{n\in I:\mathrm{count}(n)<Tf/4\}(Tf/4)^2
 \leq\sum_{n\in I}E(n)^2.
\]

It is a general finite algebraic consequence, ready to apply to the actual common-cutoff lower theorem. No new own-paper endpoint is an external assumption. The numerical comparison with the upper sieve constant and the final Goldbach exceptional-set theorem are separate remaining results.

## Conditional scope and source synchronization

No new deep hypothesis was introduced in this continuation. The main-term size consumes only the already recorded general interval Mertens products; its archimedean and smoothing arguments are internal proofs. The joint lower estimate retains the earlier ordinary SW/BV, raw Ren/Ghosh, general one-stage sieve, interval Mertens and classical function-continuity inputs. None is declared as a new Lean axiom.

The selected manuscript is unchanged. The user is editing the compact presieving replacements, and no completed edited source is claimed. Two minor notation corrections in the lower-bound exposition are saved in `blueprint/Section11_LowerBound_Notation_Fixes.tex`: use A0 in the final lower bound of e:H1elementary10 and in the smoothing-choice sentence of the main-term proof. These change notation, not the statements or mathematical argument.

The source ledger is now19 proved,29 complete conditional implications,1 quoted external theorem and5 open claims, plus4 definitions. Four open claims are substantive: the weighted upper main-term comparison, full upper sieve application, strict normalized numerical comparison and final Goldbach assembly. The fifth is the original weaker presieving statement awaiting manuscript synchronization. Supporting-theorem and checkpoint counts are not completion percentages.

## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| GoldbachLowerMainTermSize.lean | 6 |
| GoldbachLowerSmoothedSize.lean | 5 |
| GoldbachLowerBoundsComplete.lean | 4 |

- `goldbach_mertens_product_constant_pos`
- `goldbach_lower_log_preliminary`
- `goldbach_lower_arithmetic_logN`
- `goldbach_lower_theta_logN`
- `goldbach_lower_main_term_real`
- `goldbach_lower_main_term_size`
- `goldbach_retained_sqrt_lower`
- `goldbach_archimedean_retained_lower`
- `goldbach_smoothing_error_small`
- `goldbach_retained_height_eventually`
- `goldbach_lower_smoothed_size`
- `goldbach_lower_bounds_complete`
- `goldbach_half_sieve_closed_value_positive`
- `goldbach_lower_count_from_main_and_error`
- `goldbach_lower_bad_card`

<!-- checkpoint-verification -->

## Verification

All 1315 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 5108-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 4259 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 1317 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

All reviewed current-paper statements in Sections3–8 are complete under their normal hypotheses or as complete implications from explicit independent general inputs. The corrected prime-square input includes one fixed-level Page datum per N, the full extended major range and the sufficient complementary minor estimate. The broad quantitative IW proposition includes the exact real-Q construction, rough full-Lp multiplier norm, both full-space sampling directions, unique interpolation and finite-dimensional Shannon sampling for every1<=p<=infinity. The general Page/progression, Ren/Ghosh, Tao and other previously recorded independent theorems and their explicit bridges remain unproved. No own-paper endpoint is a new external assumption. The latest upload and selected reconciled copy are preserved. The Section9 arithmetic/final-count reductions are checked for the user-corrected closed L; all Section10 statements and the full circle-method implication are complete in the agreed conditional scope; Section11 remains open. No new deep input was introduced. Main-term size consumes the existing interval Mertens input; joint lower sieve uses the previously recorded ordinary SW/BV, Ren/Ghosh and general classical one-stage sieve/function-continuity inputs. The full Section11 lower-sieve proposition p:sieveneedlower8 is a complete conditional implication, including its actual main term, uniform o(1), n-independent coefficients and mean-square error. The uniform main-term lower bound l:maintermsize8 and its joint application with the same large cutoff C are also complete conditionally. The weighted upper main-term sum, upper sieve, numerical comparison and final Goldbach conclusion remain open.
