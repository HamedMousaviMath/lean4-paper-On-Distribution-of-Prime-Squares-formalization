# Exact rational-arc separation

For integers a,b and positive q,r, a nonzero determinant \(ar-bq\) gives
\[
 |a/q-b/r|\ge 1/(qr).
\]
The proof casts the nonzero integer determinant to the reals, proves its absolute value at least one, and divides by the positive denominator product.

For rationals u,v with their reduced positive denominators, this yields
\[
u\ne v\Longrightarrow
|(u:\mathbb R)-(v:\mathbb R)|\ge1/(\operatorname{den}(u)\operatorname{den}(v)).
\]
If u,v are distinct canonical representatives in [0,1), the same lower bound holds for \(|u-v-k|\) for every integer k. An equality u=v+k would force -1<k<1, hence k=0 and u=v. This accounts explicitly for integer lifts when an arc crosses the boundary of a fundamental interval.

If both denominators are at most D, separation is at least \(1/D^2\). Two real arcs of radius delta centered at distinct such rationals cannot contain a common point when \(2\delta<1/D^2\). The final theorem proves that uniqueness from the triangle inequality.

| Module | New named theorems |
| --- | ---: |
| RationalArcSeparation.lean | 6 |

## Scope

These are exact unconditional proofs. No numerical sampling is used. Dyadic support uniqueness will only be asserted when its strict radius inequality is proved; the smallest denominator scales will not be silently included by an inapplicable estimate. The analytic minor-arc gap remains unchanged.

<!-- checkpoint-verification -->

## Verification

All 101 project modules and the root were freshly rebuilt: 3616 jobs pass without warnings/errors. All 800 named theorems pass the complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound. The source scan checks 103 Lean files. Exact unique import/audit coverage and unchanged frozen source hashes are checked before packaging. There are no placeholders or added mathematical axioms.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. No new deep analytic input or own-paper lemma is assumed.
