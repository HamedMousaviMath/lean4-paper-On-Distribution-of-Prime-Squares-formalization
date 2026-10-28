# Section 11: fixed sieve sets and progression sequences

This note explains the checked starting results through checkpoint1218. It does not claim the later local-density, presieving or final sieve propositions.

## Actual sets

The lower sequence consists of integers r-1, where r is prime, r=11 modulo24 and n-r is a prime square. The original sieve uses primes p=3 modulo4 which do not divide n-1. The fixed sieve uses all primes p>3 with p=3 modulo4. Both use the strict real cutoff p<z.

The upper sequence M_n(ell) consists of integers r=ell*t+1<N² with t a prime congruent to3 modulo4 and n-r=m² for a prime m>3. The original upper sieve primes do not divide12*ell*n. The fixed upper sieve primes do not divide12*ell. The level is exactly (N²/ell)^(1/4). The actual closed multiplier set L and its subset L_n are retained.

These definitions are implemented as `goldbachFixedLowerSiftedValues`, `goldbachFixedUpperSifted` and the previously proved original sets. No formal set is replaced by a generic counting hypothesis.

## Lower comparison

For every lower-sequence element, r-1=10 modulo24, so3 does not divide r-1. Every other prime in the original lower sieve belongs to the fixed prime set. Surviving the fixed sieve therefore implies surviving the original sieve. Taking cardinalities gives exactly the source lower inequality. The shift from r to r-1 is implemented on actual finite sets.

Checked declarations: `goldbach_fixed_lower_subset`, `goldbach_fixed_lower_values_subset`, `goldbach_fixed_lower_count`.

## Exact upper exceptional count

Suppose a pair (ell,r), with ell in L_n, survives the original upper sieve but fails the fixed sieve. Some prime p below the actual level divides r and does not divide12*ell. If p did not divide n, it would be an original upper sieve prime, contradicting survival. Thus p divides n.

Write n-r=m² using the actual defining prime m of M_n(ell). Since p divides both n and r, p divides m². Primality gives p=m, hence r=n-p². Also r-1=ell*t>0, so ell divides the positive integer n-p²-1.

For a fixed p dividing n, the number of such multiplier pairs is therefore at most tau(n-p²-1). Summing gives the exact finite inequality

\[
 \sum_{\ell\in L_n}S(M_n(\ell),W_{\ell,n},z_\ell)
 \leq
 \sum_{\ell\in L}S(M_n(\ell),W_\ell,z_\ell)
 +\sum_{p\mid n}\tau(n-p^2-1).
\]

The proof counts pairs (ell,r), so multiplicities across different multipliers are retained. Enlarging L_n to L is handled by a proved finite-set inclusion. Divisor arguments equal to0 contribute0 in the finite envelope; every actual exceptional pair has a positive divisor argument.

Checked declarations: `goldbach_fixed_upper_exception`, `goldbach_fixed_sieve_exceptions_card`, `goldbach_fixed_upper_source_count_finite`.

## Uniform power error

For each epsilon>0, the elementary prime-factor bound gives a constant K1 such that the number of prime divisors of n is at most K1 N^(epsilon/2), uniformly for positive n<=N². The proved divisor bound gives a constant K2 such that tau(a)<=K2 N^(epsilon/2) for every0<=a<=N². Both constants are chosen before N and n.

Applying the second bound to each n-p²-1 gives

\[
 \sum_{p\mid n}\tau(n-p^2-1)
 \leq K_1K_2N^\varepsilon.
\]

The actual proof covers every N>=1,0<n<=N² and every real z, which contains the full retained source range. Neither PNT nor a sieve theorem is used. This closes the whole source lemma `l:fixedsievesets10`, not merely a numerical instance or an implication from the desired error bound.

Checked declarations: `goldbach_uniform_divisor_card`, `goldbach_fixed_sieve_divisor_sum`, `goldbach_fixed_sieve_sets`.

## Lower progression identity

For a positive d whose prime divisors exceed3, the CRT supplies a coprime class a modulo24d satisfying a=11 modulo24 and a=1 modulo d. For every prime r, these two conditions are equivalent to r=a modulo24d and d dividing r-1.

The actual lower divisibility count is therefore exactly the number of prime pairs m,r with m²+r=n and r=a modulo24d. The finite count bijection is proved; uniqueness of the positive prime m follows from injectivity of squaring. The residue a is chosen before every n.

Using the actual definition of the already proved circle-method remainder then gives the exact G_R H_R/phi(24d) plus remainder decomposition. Normalizing this by the source X_n and omega_n still requires the local-density calculation, which remains open.

Checked declarations: `goldbach_lower_sieve_sequence_count`, `goldbach_lower_sequence_fixed_residue`, `goldbach_lower_sequence_circle_identity`.

## Upper progression identity

For ell in the actual closed L and z>3, the source factorization ell=2*u*p2 gives ell=2v with v=3 modulo4 and coprime to6. This is proved from the prime support of u and the primality and lower bound of p2.

For d coprime to12*ell, the upper CRT class a modulo12d satisfies v*a=5 modulo12 and ell*a+1=0 modulo d. The congruence t=a modulo12d is proved equivalent to these two conditions with t in place of a.

For n=12 modulo24, the equation m²+ell*t=n-1 and this residue condition force m>3 and t=3 modulo4. Conversely, the actual defining conditions of M_n(ell) yield that residue condition. The proof therefore gives the exact finite identity at n-1, including the source prime exclusions and the actual r<N² cutoff. Again a is chosen before every n.

Checked declarations: `goldbach_upper_sieve_sequence_count`, `goldbach_closed_multiplier_residue_data`, `goldbach_upper_sequence_fixed_residue`, `goldbach_upper_sequence_circle_identity`.

## Mean-square remainder transport

Let I be any fixed finite subset of the allowed circle-method indices. Extend its coefficients by0 outside I and extend the residue family by the coprime representative1. The full circle-method theorem applies to these extended families. A checked finite sum identity removes every added index and recovers the sum over I exactly. The constant and threshold retain their original order before all families and cutoffs.

For the upper sieve, n maps to n-1 injectively on positive integers. Thus a sum over any positive subset of n<N² is bounded by the full original mean-square sum. If the whole range0<=n<N² is used, the value at0 is counted twice after taking natural predecessors. Its square is bounded by the original full sum, giving a harmless factor2. No value of the remainder at0 is assumed to vanish.

The transport uses only the existing independent ordinary SW, ordinary BV and uniform raw Ren/Ghosh inputs of the completed circle-method theorem. No additional deep input or own-paper sieve endpoint is introduced.

Checked declarations: `goldbach_pred_square_sum_bound`, `goldbach_pred_full_square_sum_bound`, `goldbach_sieve_remainders_selected`.

## Next obligations

The local-density identities and their multiplicative normalization must still be proved for the actual Euler factors. Then the two-range presieve construction and its levels, dimension bounds, coefficient estimates and main-term analysis must be completed before either full sieve proposition is awarded source-level credit. The statement map and current paper ledger distinguish these unfinished claims from the checked reductions above.
