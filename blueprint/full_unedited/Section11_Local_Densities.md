# Section11: the two local-density lemmas

Both `l:lowerlocaldensity` and `l:upperlocaldensity` are proved for the retained source context. No new external input is used. The selected manuscript is unchanged. The clause-by-clause source review is in `verification/section11-local-density-source-review1221.json`.

The root count is the actual cardinality of the units satisfying the square equation. Consequently zero is excluded from the variable being squared, and rho is zero at the zero residue. Opening the prime Ramanujan sum proves

\[
C_p(a)=p\rho_p(a)-(p-1),\qquad
\rho_p(a)=\begin{cases}2,&(a/p)=1,\\0,&(a/p)\ne1.\end{cases}
\]

The normalized character coefficient agrees with the earlier original definition. Its unrestricted factor, when the multiplier is invertible, is

\[
1+G_p=\frac{p(p-1-\rho_p(n))}{(p-1)^2}.
\]

If the progression fixes its unit variable to b, the factor becomes

\[
1+G_p=\frac{p\rho_p(n-\ell b)}{p-1}.
\]

The proof also checks the multiplier-zero case, whose common factor can vanish. The actual unrestricted pair cardinality plus rho equals p-1.

The finite coefficient identity for q dividing ell*k is needed at the small primes. It is proved from reduction of units and their exact normalized fiber mass. Under the source congruence n-ell*b=1 modulo24, this gives the factor8 at2 and3 at3. In particular, the upper modulus12 with its even multiplier is treated correctly at8.

Adjoining one prime p>3 to a coprime progression modulus proves an identity between the original normalized arithmetic factors. The identity multiplies by

\[
g(p)=\begin{cases}
\rho_p(n-c)/(p-1-\rho_p(n)),&p\leq R,\\
1/(p-1),&p>R,
\end{cases}
\]

when ell*b=c modulo p. The cutoff is inclusive, including a prime equal to R. Every other prime factor is proved unchanged. Induction over a finite set of distinct primes, followed by the square-free prime-factor product identity, proves the full factorization for d.

For the lower sieve, the actual CRT conditions are b=11 modulo24 and b=1 modulo d, while n=12 modulo24. They give c=1. The base arithmetic factor at modulus24 is proved nonzero, so the paper's original quotient definition is identified with this density. The prime formula is proved for every p>3; the lower sieve's additional restriction p=3 modulo4 is therefore included.

For the upper sieve, the existing source multiplier result supplies ell=2v and v coprime6. The actual conditions vb=5 modulo12 and ell*b+1=0 modulo d imply the required congruence at24 and give c=-1 at every divisor prime. Unit cancellation shows that every representative reduces to the same base class modulo12. The resulting density is

\[
g_{n,\ell}(p)=\begin{cases}
\rho_p(n)/(p-1-\rho_p(n-1)),&p\leq R,\\
1/(p-1),&p>R.
\end{cases}
\]

One explicit function omega(d)=d times the product of these prime densities is constructed before all supported square-free d and all representatives of the source CRT classes. Its value at1 and its multiplicativity on coprime arguments are proved. The complete existence and factorization statement is `goldbach_upper_local_density`.

The denominator is positive for p>3. Both candidate densities are nonnegative and at most 2/(p-3), which is below1 for p>=7. At5, a kernel-checked finite calculation gives either rho_5(n)=0, or rho_5(n)=2 and rho_5(n-1)=0. The upper density is therefore at most1/2 at5. This proves its full required range [0,1).

The upper identity never divides by its base arithmetic factor. If a common obstructing local factor is zero, the multiplicative identity still proves equality with zero on both sides. A zero base is not an extra hypothesis or an omitted case.

The paper-level ledger is now19 proved claims,27 complete conditional implications,1 quoted external result and7 open claims, with4 definitions separate. Presieving and the later sieve estimates remain open. The later analytic use of these densities does not retroactively become an input to the local-density proofs.
