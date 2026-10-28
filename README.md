Prime Squares: a conditional Lean formalization

A formalization of Hamed Mousavi's On the Distribution of Prime Squares and Its Applications.

Start with the compact blueprint, the paper map, and the independent-input catalogue.

Mathematical scope

The numbered ledger contains 22 proved results under their source hypotheses, 31 complete conditional implications, and one quoted external theorem, plus four formalized definitions. The headline improving, sparse, ergodic and Goldbach results are conditional on the exact independent inputs recorded in Lean. The optional Granville–Kurlberg spacing theorem is not used by the persistent-badness headline.

There are no sorry placeholders or added mathematical axioms in the proof library. This does not remove explicit hypotheses: their truth, and the bridges from published results to the exact interfaces, remain outside this formalization. A kernel axiom audit alone does not certify those hypotheses or the paper-to-Lean correspondence.

Conditional inputs and references

The formalization uses the following 13 families of explicit hypotheses. Several families contain multiple predicates, and individual theorems use different subsets. The formulas below summarize the mathematical content; exact quantifiers and conventions are in the Lean declarations and docs/EXTERNAL_INPUTS.json.

Scope of the citations. References identify the literature underlying the inputs. They do not constitute a Lean proof of those inputs or a certification of every passage from a published statement to the exact assumed interface. Such passages include normalization, globalization, full-domain extensions, uniformity and probability-space conventions. Where a source is background or a proposed route rather than a verified direct match, that is stated explicitly.

1. Prime number theorem, progression estimates and exceptional characters

We assume

$$
\vartheta(y)=\sum_{p\le y}\log p\sim y,
\qquad
\sum_{p\le y}p^{-1/2}\sim\frac{2\sqrt y}{\log y},
$$

compatible uniform progression estimates with a possible exceptional-character term,

$$
\sum_{n\le t, n\equiv a\pmod q}\Lambda(n)
=\frac{t-\mathbf{1}{q\chi\mid q}\chi_q(a)t^\beta/\beta}{\phi(q)}
+O\left(Ne^{-c\sqrt{\log N}}\right),
$$

in the specified exponential modulus range and for $N/2\le t\le N$; Landau–Page uniqueness; and fixed-modulus prime frequencies $\frac{1}{K}\sum_{k<K}\mathbf{1}_{p_k\equiv a\pmod q}\to1/\phi(q)$.

References: IK04, §§5.6 and 5.9; Tao14, Corollary 39 and Exercises 40, 50, 54 and 55(iii). Exercise 54 is Page's theorem; Exercise 55(iii) contains the exceptional-term progression estimate. The reciprocal-square-root sum follows mathematically by partial summation.

Unproved passage: deriving the exact compatible progression packages and interpreting the code's limiting character-sum zeros as classical Dirichlet $L$-function zeros. The second PNT limit has no $\log p$ weight.

2. Ren–Ghosh bounds and ordinary quadratic Weyl approximation

For $S(x,\xi)=\sum_{x<n\le2x}\Lambda(n)e(\xi n^2)$, the assumed Ren bound is

$$
|S(x,\xi)|\ll\tau(q)^{3/2}(\log x)^d
\left(\sqrt{xT}+x^{4/5}+x/\sqrt T\right),
\qquad T=q(1+|\xi-a/q|x^2),
$$

in the small-denominator range. The complementary Ghosh input is

$$
|S(x,\xi)|\ll x^{17/16}
\left(q^{-1}+x^{-1/2}+q/x^2\right)^{1/4}.
$$

The ordinary-square input assumes a rational-center expansion of the normalized quadratic sum by a complete Gauss sum times its oscillatory integral, with error $O(\sqrt q/M)$.

References: Ren05, Theorem 1.1 with $k=2$; Ghosh81. Ren's equation (1.4) records and attributes the Ghosh estimate with an arbitrary $\varepsilon$; the interface uses $\varepsilon=1/16$. For ordinary squares: FJK77, Theorem 1, as restated in HLY21, Theorem 3.1 (arXiv v2).

Unproved passage: the precise annular/von-Mangoldt normalization and fixed uniform constants, and the ordinary-square rational selection, reduction and negative-phase convention. No unverified original Ghosh theorem number is assigned here.

3. Independent ordinary-square decomposition and stopping estimates

For $B_Nf(x)=N^{-1}\sum_{n\le N}f(x-n^2)$, we assume a decomposition on finite indicators, $B_N\mathbf{1}F=L{N,J}\mathbf{1}F+H{N,J}\mathbf{1}_F$, with

$$
||L_{N,J}f||_\infty\le C N^{-2}J(\log J)^2||f||1,
\qquad
||H{N,J}f||_2\le C J^{-1/2}\log J ||f||_2.
$$

A separate stronger stopping input gives the corresponding local low/high estimates under the exact support and admissibility conditions.

Reference: HLY21, Lemma 2.2 for the local fixed-scale high/low method, and §5, especially equation (5.1) and Lemmas 5.1–5.6, for the stopping argument (arXiv v2 numbering).

Unproved passage: the cited local arguments are the literature basis; this README does not claim that they verbatim state the assumed global norm-map package or the exact fivefold-support stopping interface. Those globalization and convention bridges remain external. The spatial reflection from $x+n^2$ to $x-n^2$ is proved internally. The interface does not require the low/high maps to be linear.

4. Smooth multifrequency maximal estimates

For the fixed smooth cutoff and separated rational centers $\Gamma$, the general input has the form

$$
||\sup_{j\in J}|T_{m_j^\Gamma}f|||_2
\lesssim (1+\log(|\Gamma|+1))^2||f||_2.
$$

A separate common-period input, with denominators dividing $P$, assumes loss

$$
1+\log(1+\log P)+\log(|\Gamma|+1).
$$

Literature references: B89 for Bourgain's multifrequency/maximal framework; L97 for the related rational-frequency refinement.

Citation qualification: the exact common-period inequality displayed above has not been independently matched to a numbered statement in L97 in this reference audit. Treat L97 as the intended/background source, not as a verified direct citation proving that predicate. The precise rational estimate and the smooth-real-to-circle sampling/normalization passages remain explicit external assumptions.

5. Quantitative Ionescu–Wainger construction, multipliers and sampling

The construction supplies suitable coprime data, a period $P\le3^Q$, and a rational set containing all source denominators. For good data, narrow $m$, $||\nu||_{\mathrm{TV}}\le1$, and $p_r=2r/(2r-1)\le p\le2r$, the multiplier input has the form

$$
||T_{\sum_{\alpha\in\Sigma}\widehat\nu(\alpha)m(\cdot-\alpha)}||{\ell^p\to\ell^p}
\le (Cr\log(2+k))^{Ck}||T_m||{L^p\to L^p}.
$$

The sampling inputs include two-sided major-arc interpolation bounds and narrow-band diagonal sampling $G\mapsto(G(n,n\bmod P))_n$.

Reference: Tao21, Lemma 5.1 (construction), Theorem 1.7 (adelic multipliers), Theorem 1.6 (major-arc sampling), and Proposition 1.5 (quantitative Shannon sampling), using arXiv v2 numbering.

Unproved passage: the exact finite-quotient and Fourier realizations, full bandlimited classes and rough-symbol/full-domain versions used by the interfaces. These are separate input predicates, not one assumed theorem.

6. General real-variable estimates and the independent prime maximal input

The real-variable inputs comprise one-sided Hardy–Littlewood bounds, scalar Hörmander convolution bounds, Young's inequality and Riesz–Thorin interpolation in the domains used by the code. In particular,

$$
||M^+f||_p\lesssim(p-1)^{-1}||f||_p,
\qquad
||K*f||_p\lesssim\frac{A+H}{p-1}||f||_p,
\quad 1<p\le2,
$$

under the stated Fourier $L^2$ bound $A$ and Hörmander integral bound $H$. The sparse open triangle additionally uses a complementary-exponent restricted prime maximal estimate in the actual von-Mangoldt annular normalization.

References: Stein93, Chapters I–II, for maximal and singular-integral theory; SW71, Chapters I and V, for convolution and interpolation. For the prime polynomial maximal theorem underlying the complementary-exponent input: Mehlhop24, Theorem 1.

Unproved passage: the precise quantitative Fourier-realization/full-domain formulations, and the prime-to-von-Mangoldt, prime-power and annular normalization. The finite signed maximal inequality used by the final exports is proved internally and is no longer an assumption.

7. Ergodic transference and bounded-class convergence

We assume strong transference with the same norm constant, and modular transference of the form

$$
\left|\left\lbrace x^*g(x)>\lambda\right\rbrace\right|\le K\sum_m\Phi(|g(m)|/\lambda)
\quad\Longrightarrow\quad
\mu\left(\left\lbrace x^*f(x)>\lambda\right\rbrace\right)\le K\int\Phi(|f|/\lambda) d\mu.
$$

We also assume almost-everywhere convergence for bounded functions for the three square-average families on the stated invertible probability systems.

References: Calderon68 for transference; B89 for ordinary polynomial averages; Nair91, Theorem 1, for prime-power polynomial averages in $L^2$ (hence bounded functions on a probability space); MS24, Theorem 1 and Corollary 2(ii), for prime polynomial jump/oscillation inequalities and pointwise convergence.

Unproved passage: modular transference for the exact general gauges, general probability-space conventions, and the one-dimensional cutoff/von-Mangoldt/prime-power normalization. Convergence for the unbounded Orlicz classes is a deduction in the project, not an input.

8. LaVictoire's criterion, Sawyer's principle and Conze's principle

Under the general cyclic arithmetic hypotheses, LaVictoire's criterion supplies failure of a universal weak-$(1,1)$ maximal constant along every infinite set of cutoffs. Sawyer's principle turns almost-everywhere finiteness for every $L^1$ function into a weak bound, and Conze's principle transfers the bound with the same constant to other systems.

References: LaV11, Theorem 3.1 and §1; Sawyer66; Conze73, §1, Lemma 2 and the following Theorem 1. No unverified Sawyer theorem number is supplied.

Unproved passage: the exact complex-function, cutoff and general probability-space formulations. In particular, Conze's original automorphism/standard-space presentation is not asserted to verbatim cover the code's noninvertible and general-type interfaces. The project proves the persistent-divergence adaptation and the arithmetic hypotheses for prime squares.

9. Split quadratic Weil bound

For odd primes $p$ and nonempty finite sets $S\subset\mathbb F_p$, we assume

$$
\left|\sum_{t\in\mathbb F_p}
\left(\frac{\prod_{h\in S}(t+h)}p\right)\right|
\le |S|\sqrt p.
$$

Reference: IK04, Theorem 11.23; see the coauthor-hosted Chapter 11 PDF. The quadratic character and a product of distinct linear factors give the required weaker bound as a mathematical specialization. The general Weil theorem itself is not proved in this project; the residue-correlation applications are deductions.

10. Optional Granville–Kurlberg spacing theorem

Under CRT compatibility, the stated uniform local-correlation estimates and subpower density conditions, the assumed general theorem yields joint Poisson limits for normalized cyclic gaps:

$$
\frac{\left|\left\lbrace a\in\Lambda_{q_j}(a)>\theta_i,\quad 1\le i\le k\right\rbrace\right|}
{|\Lambda_{q_j}|}
\longrightarrow e^{-\sum_i\theta_i}.
$$

Reference: GK08, Theorem 1; §1, footnote 3 discusses the cyclic wraparound convention.

Unproved passage: the exact cyclic joint-gap formulation and its source-to-interface bridge. The unit-square application hypotheses are proved from Weil. This optional input is not used by Theorem 1.5(i).

11. Ordinary-count Siegel–Walfisz and Bombieri–Vinogradov

The ordinary prime-count inputs are Siegel–Walfisz in logarithmic moduli, uniformly over endpoints, and the unweighted-modulus-sum Bombieri–Vinogradov estimate

$$
\sum_{q\le X^{1/2}(\log X)^{-B}}
\max_{(a,q)=1}\sup_{2\le y\le X}
\left|\pi(y;q,a)-\frac{\mathrm{Li}(y)}{\phi(q)}\right|
\ll_A X(\log X)^{-A}.
$$

References: IK04, Chapters 5 and 17 (especially §17.3 for BV); Tao14, Exercise 64 (Siegel–Walfisz); Tao15, Theorem 17 and Exercises 20 and 24 (BV, endpoint maximum, and prime-indicator versions).

Unproved passage: the precise prime-count/endpoint interface and partial-summation conventions. The paper-specific coefficient sums, lcm reindexing and circle-method estimate are internal deductions.

12. General one-stage sieve weights and sieve-function data

With $V(z)=\prod_{p<z}(1-g(p))$ and $s=\log D/\log z$, the assumed one-stage weights are chosen before the supported density, have the required squarefree level support and pointwise sieve sandwich, and give

$$
\sum_d\lambda_d^-g(d)\ge V(z)(f_\kappa(s)-o(1)),
\qquad
\sum_d\lambda_d^+g(d)\le V(z)(F_\kappa(s)+o(1)),
$$

with the specified uniform quantitative errors and refined dimension hypothesis. The package also assumes continuity at the required arguments and

$$
f_{1/2}(9/8)=\sqrt{\frac{8e^\gamma}{9\pi}}\log2,
\qquad F_1(2)=e^\gamma.
$$

References: Iwaniec80 for Rosser's sieve; Suzuki23, Definition 8.2, Proposition 11.8, Lemma 14.7 and Theorem 14.8, for an accessible account of the refined dimension, sieve-function and coefficient theory.

Unproved passage: the exact uniform weight interfaces and classical function data. The old locator “Iwaniec (1.8)–(1.10)” is not used here as an independently verified locator. The signed two-stage combination, applications and final numerical comparison are proved in the project.

13. Mertens estimates and an effective half-dimensional mean theorem

We assume the stated bounded-error logarithmic prime sums, ordinary/fixed-progression relative Euler-product estimates, and refined interval bounds for the particular universal sieve factors. The effective mean input is a uniform nonnegative strongly multiplicative upper theorem with $r(p)\le6$ and prime balance near density $1/2$, giving

$$
\sum_{n\le x}r(n)
\le\left(\frac{e^{-\gamma/2}}{\sqrt\pi}+K\varepsilon^\delta\right)
\frac{x}{\log x}\prod_{p\le x}\left(1+\frac{r(p)}{p-1}\right).
$$

References: MV06, §2.2 and Chapter 11; Williams74 for Mertens products in fixed progressions; Tenenbaum17, corrected author version arXiv:1709.01315v13, Theorem 1.2, equation (1.18), together with Tenenbaum20.

Unproved passage: Euler-factor comparisons, uniform interval and endpoint reductions, and the general $\rho=1/2$ upper-corollary reduction/normalization from Tenenbaum's theorem. The special factors $1-2/(p-3)$ and $1-1/(p-1)$ are not claimed to be verbatim statements of Williams's paper. The application to our varying weights and the weighted main-term comparison are proved.

Bibliography for the conditional inputs

IK04. H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, American Mathematical Society, 2004. DOI.

Tao14. T. Tao, 254A, Notes 2: Complex-analytic multiplicative number theory, 9 December 2014. Author's notes.

Tao15. T. Tao, 254A, Notes 3: The large sieve and the Bombieri–Vinogradov theorem, 10 January 2015. Author's notes.

Ren05. X. Ren, “On exponential sums over primes and application in Waring–Goldbach problem,” Science in China Series A: Mathematics 48(6) (2005), 785–797. DOI.

Ghosh81. A. Ghosh, “The Distribution of $\alpha p^2$ Modulo 1,” Proceedings of the London Mathematical Society (3) 42(2) (1981), 252–269. DOI.

FJK77. H. Fiedler, W. Jurkat and O. Körner, “Asymptotic expansions of finite theta series,” Acta Arithmetica 32(2) (1977), 129–146. DOI.

HLY21. R. Han, M. T. Lacey and F. Yang, “Averages along the square integers: $\ell^p$-improving and sparse inequalities,” Tunisian Journal of Mathematics 3(3) (2021), 517–550. DOI; arXiv v2.

B89. J. Bourgain, “Pointwise ergodic theorems for arithmetic sets,” Publications Mathématiques de l'IHÉS 69 (1989), 5–41. DOI; Numdam.

L97. M. Lacey, “On an inequality due to Bourgain,” Illinois Journal of Mathematics 41(2) (1997), 231–236. DOI.

Tao21. T. Tao, “The Ionescu–Wainger multiplier theorem and the adeles,” Mathematika 67 (2021), 647–677. DOI; arXiv v2.

Stein93. E. M. Stein, Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory Integrals, Princeton Mathematical Series 43, Princeton University Press, 1993. Publisher ebook DOI.

SW71. E. M. Stein and G. Weiss, Introduction to Fourier Analysis on Euclidean Spaces, Princeton Mathematical Series 32, Princeton University Press, 1971. Publisher ebook DOI.

Mehlhop24. N. Mehlhop, “Vector-Valued Maximal Inequalities and Multiparameter Oscillation Inequalities for the Polynomial Ergodic Averages Along Multi-dimensional Subsets of Primes,” Journal of Fourier Analysis and Applications 30 (2024), article 61. DOI.

Calderon68. A. P. Calderón, “Ergodic theory and translation-invariant operators,” Proceedings of the National Academy of Sciences USA 59(2) (1968), 349–353. DOI.

Nair91. R. Nair, “On polynomials in primes and J. Bourgain's circle method approach to ergodic theorems,” Ergodic Theory and Dynamical Systems 11(3) (1991), 485–499. DOI.

MS24. N. Mehlhop and W. Słomian, “Oscillation and jump inequalities for the polynomial ergodic averages along multi-dimensional subsets of primes,” Mathematische Annalen 388 (2024), 2807–2842. DOI; arXiv.

LaV11. P. LaVictoire, “Universally $L^1$-bad arithmetic sequences,” Journal d'Analyse Mathématique 113 (2011), 241–263. DOI; arXiv.

Sawyer66. S. Sawyer, “Maximal inequalities of weak type,” Annals of Mathematics (2) 84(2) (1966), 157–174. DOI.

Conze73. J.-P. Conze, “Convergence des moyennes ergodiques pour des sous-suites,” Mémoires de la Société Mathématique de France 35 (1973), 7–15. DOI; Numdam.

GK08. A. Granville and P. Kurlberg, “Poisson statistics via the Chinese remainder theorem,” Advances in Mathematics 218(6) (2008), 2013–2042. DOI; author PDF.

Iwaniec80. H. Iwaniec, “Rosser's sieve,” Acta Arithmetica 36 (1980), 171–202. DOI.

Suzuki23. Y. Suzuki, The Rosser–Iwaniec sieve, lecture notes, 14 March 2023. Author PDF.

MV06. H. L. Montgomery and R. C. Vaughan, Multiplicative Number Theory I: Classical Theory, Cambridge University Press, 2006. DOI.

Williams74. K. S. Williams, “Merten's theorem for arithmetic progressions,” Journal of Number Theory 6(5) (1974), 353–359. DOI.

Tenenbaum17. G. Tenenbaum, “Moyennes effectives de fonctions multiplicatives complexes,” The Ramanujan Journal 44 (2017), 641–701. DOI. Use the corrected author version, arXiv v13, 22 July 2025.

Tenenbaum20. G. Tenenbaum, “Correction to: Moyennes effectives de fonctions multiplicatives complexes,” The Ramanujan Journal 53 (2020), 243–244. DOI.

Blueprint and implementation

The public blueprint has 52 nodes: 39 mathematical groups and 13 groups of independent inputs. It covers every numbered result and definition, with a DAG, uses / proves tags and exact Lean targets. Small calculations remain in the proof implementation, not in the public graph.

The implementation retains its 1,382 existing modules and the PrimeSquares namespace. These files have not been merged or renamed: doing so would be a separate refactor and would require a fresh build. The module index supplies the compact subject navigation. The complete original notes are now included under blueprint/full_unedited/, with an index and original hashes. Historical notes are preserved unedited and do not override the current scope ledger.

Reproduce the Lean checks

Install Lean via elan, then run from this directory:

lake exe cache get
lake build
python3 scripts/check_source.py
python3 scripts/check_axioms.py
lake env lean scripts/CheckBlueprint.lean
lake env lean scripts/CheckHeadlines.lean
python3 scripts/verify_release.py

The Lean version and Mathlib revision are pinned in lean-toolchain and lake-manifest.json. CheckHeadlines.lean exposes the actual types and axioms; this package does not claim an independent Comparator certification.

The archived full build at proof checkpoint 1265 covered 1,382 project modules, 4,517 named theorem axiom audits and 973 evidence declaration signatures. The publication package preserves the corresponding Lean sources byte-for-byte. Subsequent title, archive and reference updates checked source identities and documentation; they did not run a new Lean build. See verification/ for the recorded evidence. A GitHub Actions workflow is supplied; its current run status should be checked in the repository’s Actions tab.

Build the blueprint

Install TeX Live with pdfLaTeX, latexmk and the usual AMS packages. For HTML also install Graphviz and pip install -r blueprint/requirements.txt.

python3 scripts/render_blueprint.py
cd blueprint/src
latexmk -output-directory=../print
plastex -c plastex.cfg web.tex

The standard leanblueprint pdf and leanblueprint web commands also work after git init at the project root. Use the supplied lake env lean scripts/CheckBlueprint.lean for declaration checking; no extra checkdecls dependency is added. The generated content_web.tex only omits empty leaf dependency commands and adapts two literal command names for plasTeX; mathematical content is shared with content.tex.

To view the generated web blueprint locally:

python3 -m http.server --directory blueprint/web 8000

Open http://localhost:8000/. MathJax rendering requires internet access.

Files

PrimeSquares/, PrimeSquares.lean: unchanged checked proof implementation.

paper/: manuscript and PDF under the updated title, plus the supplied bibliography; exact original source/PDF preserved in paper/archive/.

blueprint/src/: standard leanblueprint LaTeX sources and generated web variant.

blueprint/nodes.json: curated graph and proof-architecture summaries.

blueprint/full_unedited/: all 1,303 original blueprint artifacts, with topic/checkpoint navigation.

blueprint/full_unedited_manifest.json: byte-for-byte preservation record.

blueprint/web/: compiled HTML and interactive dependency graph.

docs/: compact blueprint PDF, paper/module maps, scope, conditional-input references, reference-audit notes and author note.

scripts/: source, axiom, declaration and release checks.

verification/: saved proof evidence and current packaging checks.

Manuscript and reference notes

The exact conditional inputs are documented above and in the input catalogue. REFERENCE_AUDIT_NOTES.md records citation corrections and source-matching qualifications. AUTHOR_ACTIONS.tex supplies acknowledgement wording that accurately describes the conditional formalization.

The unedited blueprint archive preserves earlier titles, intermediate errors and historical status reports. Use the current paper map, input catalogue and verification record for present claims.
