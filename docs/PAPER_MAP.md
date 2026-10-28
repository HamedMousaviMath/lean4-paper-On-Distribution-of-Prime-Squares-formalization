# Paper-to-Lean map

Numbers come from the newly compiled current manuscript. Nodes group related results; exact statements and all supporting anchors are in PAPER_MAP.json.

| Paper | Statement | Blueprint node | Status | Selected Lean targets |
| --- | --- | --- | --- | --- |
| Theorem 8.6 | Quoted Granville-Kurlberg spacing theorem | `input_gk` | external_candidate | `PrimeSquares.RawGranvilleKurlbergInput` |
| Definition (unnumbered) | Actual quadratic exponential sums | `QuadraticSums` | formalized | `PrimeSquares.twistedSquareSum`, `PrimeSquares.principalSquareSum`, `PrimeSquares.upsilon` |
| Definition (unnumbered) | Actual normalized progression sum Upsilon | `QuadraticSums` | formalized | `PrimeSquares.twistedSquareSum`, `PrimeSquares.principalSquareSum`, `PrimeSquares.upsilon` |
| Definition 2.8 | Sparse families and their major subsets | `SparseData` | formalized | `PrimeSquares.IntegerSparseCollection`, `PrimeSquares.SourceLinearAdmissible` |
| Definition 2.9 | Admissible stopping maps | `SparseData` | formalized | `PrimeSquares.IntegerSparseCollection`, `PrimeSquares.SourceLinearAdmissible` |
| Lemma 3.1 | Quadratic Cohen identity and uniform bound | `cohen_identities` | proved | `PrimeSquares.quadratic_cohen_identity`, `PrimeSquares.progression_cohen_identity_int` |
| Lemma 3.11 | Progression-restricted Cohen identity | `cohen_identities` | proved | `PrimeSquares.quadratic_cohen_identity`, `PrimeSquares.progression_cohen_identity_int` |
| Lemma 3.12 | Normalized progression correlation and factorization | `progression_euler_products` | proved | `PrimeSquares.sum_upsilon_square_prime_factorization`, `PrimeSquares.progression_euler_product_real`, `PrimeSquares.general_progression_euler_product_real` |
| Lemma 3.14 | Corrected progression Euler product | `progression_euler_products` | proved | `PrimeSquares.sum_upsilon_square_prime_factorization`, `PrimeSquares.progression_euler_product_real`, `PrimeSquares.general_progression_euler_product_real` |
| Corollary 3.16 | Corrected multiplier Euler product | `progression_euler_products` | proved | `PrimeSquares.sum_upsilon_square_prime_factorization`, `PrimeSquares.progression_euler_product_real`, `PrimeSquares.general_progression_euler_product_real` |
| Lemma 3.20 | Uniform logarithmic Cohen bound | `cohen_log_bound` | proved | `PrimeSquares.low_ramanujan_uniform_bound` |
| Lemma 3.21 | Sharp principal quadratic Gauss bound | `gauss_bounds` | conditional | `PrimeSquares.principalSquareSum_two_add_o_one`, `PrimeSquares.twistedSquareSum_uniform_bound_int` |
| Lemma 3.24 | Uniform character-twisted quadratic Gauss bound | `gauss_bounds` | proved | `PrimeSquares.principalSquareSum_two_add_o_one`, `PrimeSquares.twistedSquareSum_uniform_bound_int` |
| Lemma 3.27 | Conductor-sensitive exceptional arithmetic | `conductor_refinement` | proved | `PrimeSquares.conductor_sensitive_refinement` |
| Theorem 4.1 | Abstract endpoint improving theorem | `abstract_improving` | proved | `PrimeSquares.highLow_AB_endpoint`, `PrimeSquares.highLow_AB_strong_improving` |
| Corollary 4.15 | Abstract strong improving corollary | `abstract_improving` | proved | `PrimeSquares.highLow_AB_endpoint`, `PrimeSquares.highLow_AB_strong_improving` |
| Lemma 6.5 | Major- and minor-arc prime-square inputs | `prime_arc_approximation` | conditional | `PrimeSquares.source_corrected_prime_square_input`, `PrimeSquares.source_approximation_all_exponents` |
| Lemma 6.10 | Full approximation error with arbitrary logarithmic decay | `prime_arc_approximation` | conditional | `PrimeSquares.source_corrected_prime_square_input`, `PrimeSquares.source_approximation_all_exponents` |
| Proposition 6.16 | Pointwise low contribution and its L1-to-Linfinity bound | `prime_low` | conditional | `PrimeSquares.source_low_local_and_norm`, `PrimeSquares.selectedPrimeLow_source_bounds` |
| Lemma 6.18 | Printed annular multifrequency maximum | `annular_multifrequency` | conditional | `PrimeSquares.source_rational_annular_maximum`, `PrimeSquares.source_fixed_annular_truncation_maximum` |
| Corollary 6.21 | Denominator-truncated annular multifrequency maximum | `annular_multifrequency` | conditional | `PrimeSquares.source_rational_annular_maximum`, `PrimeSquares.source_fixed_annular_truncation_maximum` |
| Proposition 6.23 | Sharp high contribution and countable maximum | `prime_high` | conditional | `PrimeSquares.proposition621_source`, `PrimeSquares.proposition621` |
| Proposition 4.19 | Prime-square high-low decomposition | `prime_decomposition` | conditional | `PrimeSquares.proposition419` |
| Theorem 1.1 | Main prime-square improving theorem | `prime_improving` | conditional | `PrimeSquares.theorem_1_1`, `PrimeSquares.theorem_1_1_strong_sum` |
| Lemma 5.1 | Abstract localized stopping-time estimate | `sparse_recursion` | proved | `PrimeSquares.source_abstract_local_stopping_estimate`, `PrimeSquares.accepted_general_dyadic_sparse_recursion` |
| Lemma 5.10 | Sparse recursion from local estimates | `sparse_recursion` | proved | `PrimeSquares.source_abstract_local_stopping_estimate`, `PrimeSquares.accepted_general_dyadic_sparse_recursion` |
| Lemma 5.17 | Prime-square local endpoint estimate | `prime_local_endpoint` | conditional | `PrimeSquares.source_prime_local_endpoint_from_independent_inputs` |
| Theorem 1.3 | Main sparse domination theorem | `prime_sparse` | conditional | `PrimeSquares.theorem_1_3`, `PrimeSquares.theorem_1_3_open_pq` |
| Proposition 7.8 | Quantitative Ionescu-Wainger application | `iw_application` | conditional | `PrimeSquares.proposition_quantitative_IW_full` |
| Lemma 7.16 | Uniform continuous annular increment and maximal estimates | `continuous_annuli` | conditional | `PrimeSquares.source_continuous_annular_estimates` |
| Proposition 7.22 | Quantitative Orlicz low estimate | `iw_low_high` | conditional | `PrimeSquares.real_iw_source_construction_and_low`, `PrimeSquares.real_iw_source_high_low` |
| Proposition 7.30 | Quantitative Orlicz high-low estimate | `iw_low_high` | conditional | `PrimeSquares.real_iw_source_construction_and_low`, `PrimeSquares.real_iw_source_high_low` |
| Theorem 7.2 | Quantitative Orlicz maximal theorem | `orlicz_maximal` | conditional | `PrimeSquares.theorem_7_2_closed_signed_maximal`, `PrimeSquares.theorem_7_2_finitely_supported` |
| Corollary 7.6 | Quantitative lp maximal bounds near p=1 | `near_one_lp` | conditional | `PrimeSquares.corollary_7_6_closed_signed_maximal` |
| Corollary 7.46 | Ergodic transfer and quantitative endpoint conclusions | `ergodic_orlicz` | conditional | `PrimeSquares.corollary_7_46_closed_signed_maximal` |
| Lemma 8.8 | Quadratic-residue correlation input for spacing | `quadratic_correlations` | conditional | `PrimeSquares.quadratic_GK_uniform_correlation`, `PrimeSquares.quadratic_GK_tuple` |
| Theorem 8.1 | The paper-specific persistent badness criterion | `persistent_criterion` | conditional | `PrimeSquares.source_lavictoire_persistent_criterion`, `PrimeSquares.primeSquare_lavictoire_arithmetic` |
| Theorem 1.5 | Persistent L1 badness and near-L1 maximal bound | `prime_square_ergodic_theorem` | conditional | `PrimeSquares.theorem_1_5_i_literal`, `PrimeSquares.theorem_1_5_ii_closed_signed_maximal` |
| Lemma 9.2 | Reduction from a sifted set to prime-square representations | `goldbach_reductions` | proved | `PrimeSquares.goldbach_primitive_two_squares_criterion`, `PrimeSquares.goldbach_from_sifted_to_primes_complete`, `PrimeSquares.goldbach_truncation_complete`, `PrimeSquares.goldbach_master_sieve_complete` |
| Lemma 9.3 | Truncation identity and the residual set T | `goldbach_reductions` | proved | `PrimeSquares.goldbach_primitive_two_squares_criterion`, `PrimeSquares.goldbach_from_sifted_to_primes_complete`, `PrimeSquares.goldbach_truncation_complete`, `PrimeSquares.goldbach_master_sieve_complete` |
| Lemma 9.7 | Upper reduction of T to the family of sifted sets | `goldbach_reductions` | proved | `PrimeSquares.goldbach_primitive_two_squares_criterion`, `PrimeSquares.goldbach_from_sifted_to_primes_complete`, `PrimeSquares.goldbach_truncation_complete`, `PrimeSquares.goldbach_master_sieve_complete` |
| Corollary 9.9 | Combined lower and upper sieve reduction | `goldbach_reductions` | proved | `PrimeSquares.goldbach_primitive_two_squares_criterion`, `PrimeSquares.goldbach_from_sifted_to_primes_complete`, `PrimeSquares.goldbach_truncation_complete`, `PrimeSquares.goldbach_master_sieve_complete` |
| Lemma 10.11 | Positivity and truncation of the singular integral | `goldbach_singular_integral` | proved | `PrimeSquares.goldbach_positive_singular_integral_complete`, `PrimeSquares.goldbach_smooth_seed_exists` |
| Lemma 10.2 | Hybrid minor-arc mean-square estimate | `goldbach_minor` | conditional | `PrimeSquares.goldbach_hybrid_minor_complete` |
| Lemma 10.14 | Replacement by the major-arc models | `goldbach_major` | conditional | `PrimeSquares.goldbach_major_approximation_complete` |
| Lemma 10.19 | Goldbach arithmetic coefficients and Euler series | `goldbach_euler` | proved | `PrimeSquares.goldbach_arithmetic_euler_complete` |
| Lemma 10.23 | Completion of the major-arc contribution | `goldbach_major_completion` | proved | `PrimeSquares.goldbach_major_completion_complete` |
| Lemma 9.10 | Weighted Bombieri-Vinogradov circle-method approximation | `goldbach_circle_method` | conditional | `PrimeSquares.goldbach_circle_method_source_complete` |
| Lemma 11.2 | Comparison with fixed sieve prime sets | `sieve_local_data` | proved | `PrimeSquares.goldbach_fixed_sieve_sets`, `PrimeSquares.goldbach_lower_local_density_formula`, `PrimeSquares.goldbach_upper_local_density` |
| Lemma 11.6 | Lower-sieve local density formula | `sieve_local_data` | proved | `PrimeSquares.goldbach_fixed_sieve_sets`, `PrimeSquares.goldbach_lower_local_density_formula`, `PrimeSquares.goldbach_upper_local_density` |
| Lemma 11.8 | Upper-sieve local density and multiplicativity | `sieve_local_data` | proved | `PrimeSquares.goldbach_fixed_sieve_sets`, `PrimeSquares.goldbach_lower_local_density_formula`, `PrimeSquares.goldbach_upper_local_density` |
| Lemma 11.13 | Two-range presieving deduction | `two_range_presieve` | conditional | `PrimeSquares.goldbach_presieving_from_classical_coefficients`, `PrimeSquares.goldbach_presieve_uniform_assembly` |
| Proposition 9.17 | Lower sieve application | `lower_sieve` | conditional | `PrimeSquares.goldbach_lower_bounds_complete` |
| Lemma 9.22 | Uniform lower bound for the sieve main term | `lower_sieve` | conditional | `PrimeSquares.goldbach_lower_bounds_complete` |
| Proposition 9.20 | Upper sieve application and summed weights | `upper_sieve` | conditional | `PrimeSquares.goldbach_upper_sieve_complete`, `PrimeSquares.goldbach_weighted_upper_main_term_complete` |
| Lemma 11.18 | Weighted upper main-term comparison | `upper_sieve` | conditional | `PrimeSquares.goldbach_upper_sieve_complete`, `PrimeSquares.goldbach_weighted_upper_main_term_complete` |
| Lemma 9.24 | Strict positivity of the sieve comparison | `sieve_positivity` | conditional | `PrimeSquares.goldbach_sieve_numerical_comparison` |
| Theorem 1.6 | Quantitative Goldbach-type exceptional set | `goldbach_exceptional_set` | conditional | `PrimeSquares.goldbach_section9_headline_complete`, `PrimeSquares.goldbach_section9_exceptional_density_zero` |
