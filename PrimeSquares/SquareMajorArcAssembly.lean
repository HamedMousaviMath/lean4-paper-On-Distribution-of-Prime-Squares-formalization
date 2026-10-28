import PrimeSquares.MangoldtResidueReduction

/-!
# Exact finite assembly and error accounting for Lemma 6.5

The residue errors below are defined from the actual finite sums. Their
Gauss-sum assembly is an identity, not a hypothesis about the paper's
approximation. Estimating those residue errors by partial summation and
published prime-distribution inputs remains a separate obligation.
-/

open Finset

namespace PrimeSquares

theorem unitSquareGauss_model_identity (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) (M E : ℂ) :
    (∑ u : (ZMod q)ˣ, ZMod.stdAddChar (-(a*(u : ZMod q)^2)) *
      ((q.totient : ℂ)⁻¹ * (M - χ u * E))) =
      principalSquareSum q a * M - twistedSquareSum q χ a * E := by
  unfold principalSquareSum twistedSquareSum twistedUnitQuadraticGaussSum
  simp only [neg_mul]
  calc
    _ = (∑ u : (ZMod q)ˣ,
          ((q.totient : ℂ)⁻¹ * ZMod.stdAddChar (-(a*(u : ZMod q)^2))) * M) -
        ∑ u : (ZMod q)ˣ,
          ((q.totient : ℂ)⁻¹ * (χ u * ZMod.stdAddChar (-(a*(u : ZMod q)^2)))) * E := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro u _
      ring
    _ = _ := by rw [← sum_mul, ← sum_mul, ← mul_sum, ← mul_sum]

noncomputable def squareResidueModelError (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (M E : ℂ) (θ : PrimeCircle) (r : ZMod q) : ℂ :=
  (c : ℂ) * squareResidueSum S q r w θ - (q.totient : ℂ)⁻¹ * (M - χ r * E)

theorem finiteSquareSymbol_majorArc_error_identity (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a : ℤ)
    (M E : ℂ) (θ : PrimeCircle) :
    finiteSquareSymbol S c w ((((a : ℝ) / q : ℝ) : PrimeCircle)+θ) -
        (principalSquareSum q (a : ZMod q) * M - twistedSquareSum q χ (a : ZMod q) * E) =
      finiteSquareSymbol (S.filter (fun n => ¬n.Coprime q)) c w
          ((((a : ℝ) / q : ℝ) : PrimeCircle)+θ) +
        ∑ u : (ZMod q)ˣ, ZMod.stdAddChar (-((a : ZMod q)*(u : ZMod q)^2)) *
          squareResidueModelError S c w q χ M E θ (u : ZMod q) := by
  rw [finiteSquareSymbol_reduced_residues]
  have hs : (c : ℂ) * ∑ u : (ZMod q)ˣ,
        ZMod.stdAddChar (-((a : ZMod q)*(u : ZMod q)^2)) * squareResidueSum S q u w θ =
      (∑ u : (ZMod q)ˣ, ZMod.stdAddChar (-((a : ZMod q)*(u : ZMod q)^2)) *
        ((q.totient : ℂ)⁻¹ * (M - χ u * E))) +
      ∑ u : (ZMod q)ˣ, ZMod.stdAddChar (-((a : ZMod q)*(u : ZMod q)^2)) *
        squareResidueModelError S c w q χ M E θ u := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro u _
    unfold squareResidueModelError
    ring
  rw [hs, unitSquareGauss_model_identity]
  ring

theorem finiteSquareSymbol_majorArc_error_norm (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a : ℤ)
    (M E : ℂ) (θ : PrimeCircle) :
    ‖finiteSquareSymbol S c w ((((a : ℝ) / q : ℝ) : PrimeCircle)+θ) -
        (principalSquareSum q (a : ZMod q) * M - twistedSquareSum q χ (a : ZMod q) * E)‖ ≤
      ‖finiteSquareSymbol (S.filter (fun n => ¬n.Coprime q)) c w
          ((((a : ℝ) / q : ℝ) : PrimeCircle)+θ)‖ +
        ∑ u : (ZMod q)ˣ, ‖squareResidueModelError S c w q χ M E θ (u : ZMod q)‖ := by
  rw [finiteSquareSymbol_majorArc_error_identity]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ u : (ZMod q)ˣ, ‖ZMod.stdAddChar (-((a : ZMod q)*(u : ZMod q)^2)) *
        squareResidueModelError S c w q χ M E θ (u : ZMod q)‖ := norm_sum_le _ _
    _ = _ := by
      apply sum_congr rfl
      intro u _
      rw [norm_mul, norm_stdAddChar, one_mul]

theorem annularMangoldt_majorArc_error_bound {N q : ℕ} (hN : 1 ≤ N) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ℤ) (M E : ℂ) (θ : PrimeCircle) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt
        ((((a : ℝ) / q : ℝ) : PrimeCircle)+θ) -
        (principalSquareSum q (a : ZMod q) * M - twistedSquareSum q χ (a : ZMod q) * E)‖ ≤
      (Real.log q + 2 * Real.sqrt N * Real.log N) / N +
        ∑ u : (ZMod q)ˣ, ‖squareResidueModelError (Ioc (N/2) N) (N : ℝ)⁻¹
          ArithmeticFunction.vonMangoldt q χ M E θ (u : ZMod q)‖ := by
  apply (finiteSquareSymbol_majorArc_error_norm (Ioc (N/2) N) (N : ℝ)⁻¹
    ArithmeticFunction.vonMangoldt q χ a M E θ).trans
  refine add_le_add ?_ le_rfl
  simpa only [div_eq_inv_mul] using
    mangoldt_nonunit_symbol_norm_le hN (NeZero.pos q) (Ioc (N/2) N)
      (annularIndices_subset N) (inv_nonneg.mpr (Nat.cast_nonneg N))
      ((((a : ℝ) / q : ℝ) : PrimeCircle)+θ)

theorem annularMangoldt_majorArc_error_bound_uniform {N q : ℕ} (hN : 1 ≤ N) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ℤ) (M E : ℂ) (θ : PrimeCircle)
    {δ : ℝ} (hδ : ∀ u : (ZMod q)ˣ,
      ‖squareResidueModelError (Ioc (N/2) N) (N : ℝ)⁻¹
        ArithmeticFunction.vonMangoldt q χ M E θ (u : ZMod q)‖ ≤ δ) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt
        ((((a : ℝ) / q : ℝ) : PrimeCircle)+θ) -
        (principalSquareSum q (a : ZMod q) * M - twistedSquareSum q χ (a : ZMod q) * E)‖ ≤
      (Real.log q + 2 * Real.sqrt N * Real.log N) / N + (q.totient : ℝ) * δ := by
  apply (annularMangoldt_majorArc_error_bound hN χ a M E θ).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _u : (ZMod q)ˣ, δ := sum_le_sum fun u _ => hδ u
    _ = _ := by simp [ZMod.card_units_eq_totient]

end PrimeSquares
