import PrimeSquares.MajorArcErrorBudget

/-! # Explicit sufficient inequalities for the inverse-fifth major-arc error -/

namespace PrimeSquares

theorem exponential_majorArc_absorption {R t : ℝ} (hR : 0 < R)
    (ht : 7 * Real.log R ≤ t) : R^2 * Real.exp (-t) ≤ (R^5)⁻¹ := by
  have hp2 : Real.exp (2 * Real.log R) = R^2 := by
    simpa [Real.exp_log hR] using Real.exp_nat_mul (Real.log R) 2
  have hp5 : Real.exp (5 * Real.log R) = R^5 := by
    simpa [Real.exp_log hR] using Real.exp_nat_mul (Real.log R) 5
  have hleft : R^2 * Real.exp (-t) = Real.exp (2 * Real.log R - t) := by
    rw [Real.exp_sub, hp2, Real.exp_neg, div_eq_mul_inv]
  have hright : (R^5)⁻¹ = Real.exp (-(5 * Real.log R)) := by
    rw [Real.exp_neg, hp5]
  rw [hleft, hright, Real.exp_le_exp]
  linarith

theorem nonunit_majorArc_absorption {N : ℕ} (hN : 1 ≤ N) {R : ℝ} (hR : 0 < R)
    (hlog : Real.log R ≤ Real.log N)
    (hbudget : R^5 * Real.log N ≤ Real.sqrt N) :
    (2 * Real.log R + 2 * Real.sqrt N * Real.log N) / N ≤ 4 / R^5 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (N : ℝ))^2 = N := Real.sq_sqrt hNr.le
  have hsN : Real.sqrt (N : ℝ) ≤ N := Real.sqrt_le_self_iff.mpr (Or.inr hN1)
  have h1 : R^5 * Real.log R ≤ (N : ℝ) :=
    (mul_le_mul_of_nonneg_left hlog (by positivity)).trans (hbudget.trans hsN)
  have h2 : R^5 * Real.sqrt N * Real.log N ≤ (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hbudget hs
    nlinarith
  apply (le_div_iff₀ (pow_pos hR 5)).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hNr).mpr
  nlinarith

theorem majorArc_combined_absorption {N : ℕ} (hN : 1 ≤ N) {R C c : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hlog : Real.log R ≤ Real.log N)
    (hbudget : R^5 * Real.log N ≤ Real.sqrt N)
    (hexp : 7 * Real.log R ≤ c * Real.sqrt (Real.log N)) :
    (2 * Real.log R + 2 * Real.sqrt N * Real.log N) / N +
      (2 + 4 * Real.pi) * R^2 * (C * Real.exp (-c * Real.sqrt (Real.log N))) ≤
      (4 + (2 + 4 * Real.pi) * C) / R^5 := by
  have h := exponential_majorArc_absorption hR hexp
  calc
    _ = (2 * Real.log R + 2 * Real.sqrt N * Real.log N) / N +
        ((2 + 4 * Real.pi) * C) * (R^2 * Real.exp (-(c * Real.sqrt (Real.log N)))) := by simp only [neg_mul]; ring
    _ ≤ 4 / R^5 + ((2 + 4 * Real.pi) * C) * (R^5)⁻¹ := by
      exact add_le_add (nonunit_majorArc_absorption hN hR hlog hbudget)
        (mul_le_mul_of_nonneg_left h (by positivity))
    _ = _ := by ring

theorem annularMangoldt_majorArc_inverse_fifth {N q : ℕ} (hN : 1 ≤ N) [NeZero q]
    (χ : DirichletCharacter ℂ q) (κ : ℂ) {β : ℝ} (hβ : 0 < β)
    (a : ℤ) (θ : ℝ) {R C c : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hq : (q : ℝ) ≤ R^(11/10 : ℝ)) (hθ : |θ| ≤ R / ((q : ℝ) * (N : ℝ)^2))
    (hlog : Real.log R ≤ Real.log N) (hbudget : R^5 * Real.log N ≤ Real.sqrt N)
    (hexp : 7 * Real.log R ≤ c * Real.sqrt (Real.log N))
    (hprefix : ∀ u : (ZMod q)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix q u t - progressionPowerModel q (κ * χ u) β t‖ ≤
        (N : ℝ) * (C * Real.exp (-c * Real.sqrt (Real.log N)))) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt
        ((((a : ℝ)/q : ℝ) : PrimeCircle) + (θ : PrimeCircle)) -
      (principalSquareSum q (a : ZMod q) * annularOscillatoryModel N 1 θ -
        twistedSquareSum q χ (a : ZMod q) * (κ * annularOscillatoryModel N β θ))‖ ≤
      (4 + (2 + 4 * Real.pi) * C) / R^5 := by
  exact (annularMangoldt_majorArc_source_R_budget hN χ κ hβ a θ hR
    (by positivity) hq hθ hprefix).trans
    (majorArc_combined_absorption hN (by linarith) hC hlog hbudget hexp)

end PrimeSquares
