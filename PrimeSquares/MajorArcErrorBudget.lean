import PrimeSquares.PrimeSquarePartialSummation

/-! # Explicit reduction of the major-arc error to one R-budget -/

namespace PrimeSquares

theorem majorArc_phase_budget {N q : ℕ} (hN : 1 ≤ N) [NeZero q]
    {R θ : ℝ} (hθ : |θ| ≤ R / ((q : ℝ) * (N : ℝ)^2)) :
    (q : ℝ) * |θ| * (N : ℝ)^2 ≤ R := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hqr : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  have h := (le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * (N : ℝ)^2)).mp hθ
  nlinarith

theorem majorArc_rpow_denominator_le_square {R : ℝ} (hR : 1 ≤ R) :
    R ^ (11/10 : ℝ) ≤ R^2 := by
  simpa only [Real.rpow_two] using
    Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (11/10 : ℝ) ≤ 2)

theorem majorArc_totient_error_budget {N q : ℕ} {R θ δ : ℝ}
    (hR : 1 ≤ R) (hδ : 0 ≤ δ) (hq : (q : ℝ) ≤ R^2)
    (hphase : (q : ℝ) * |θ| * (N : ℝ)^2 ≤ R) :
    (q.totient : ℝ) * (δ * (2 + 4 * Real.pi * |θ| * (N : ℝ)^2)) ≤
      (2 + 4 * Real.pi) * R^2 * δ := by
  have hφ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hrr : R ≤ R^2 := by nlinarith
  have hp2 : (q : ℝ) * |θ| * (N : ℝ)^2 ≤ R^2 := hphase.trans hrr
  calc
    _ ≤ (q : ℝ) * (δ * (2 + 4 * Real.pi * |θ| * (N : ℝ)^2)) := by
      gcongr
    _ = δ * (2 * (q : ℝ) + 4 * Real.pi * ((q : ℝ) * |θ| * (N : ℝ)^2)) := by ring
    _ ≤ δ * (2 * R^2 + 4 * Real.pi * R^2) := by gcongr
    _ = _ := by ring

theorem majorArc_log_modulus_budget {q : ℕ} [NeZero q] {R : ℝ}
    (hq : (q : ℝ) ≤ R^2) : Real.log q ≤ 2 * Real.log R := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  calc
    Real.log q ≤ Real.log (R^2) := Real.log_le_log hqr hq
    _ = _ := by rw [Real.log_pow]; norm_num

theorem annularMangoldt_majorArc_R_budget {N q : ℕ} (hN : 1 ≤ N) [NeZero q]
    (χ : DirichletCharacter ℂ q) (κ : ℂ) {β : ℝ} (hβ : 0 < β)
    (a : ℤ) (θ : ℝ) {R δ : ℝ} (hR : 1 ≤ R) (hδ : 0 ≤ δ)
    (hq : (q : ℝ) ≤ R^2) (hθ : |θ| ≤ R / ((q : ℝ) * (N : ℝ)^2))
    (hprefix : ∀ u : (ZMod q)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix q u t - progressionPowerModel q (κ * χ u) β t‖ ≤ (N : ℝ)*δ) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt
        ((((a : ℝ)/q : ℝ) : PrimeCircle) + (θ : PrimeCircle)) -
      (principalSquareSum q (a : ZMod q) * annularOscillatoryModel N 1 θ -
        twistedSquareSum q χ (a : ZMod q) * (κ * annularOscillatoryModel N β θ))‖ ≤
      (2 * Real.log R + 2 * Real.sqrt N * Real.log N) / N +
        (2 + 4 * Real.pi) * R^2 * δ := by
  have h := annularMangoldt_majorArc_from_prefix_bound hN χ κ hβ a θ hδ hprefix
  refine h.trans (add_le_add ?_ (majorArc_totient_error_budget hR hδ hq (majorArc_phase_budget hN hθ)))
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  linarith [majorArc_log_modulus_budget hq]

theorem annularMangoldt_majorArc_source_R_budget {N q : ℕ} (hN : 1 ≤ N) [NeZero q]
    (χ : DirichletCharacter ℂ q) (κ : ℂ) {β : ℝ} (hβ : 0 < β)
    (a : ℤ) (θ : ℝ) {R δ : ℝ} (hR : 1 ≤ R) (hδ : 0 ≤ δ)
    (hq : (q : ℝ) ≤ R^(11/10 : ℝ)) (hθ : |θ| ≤ R / ((q : ℝ) * (N : ℝ)^2))
    (hprefix : ∀ u : (ZMod q)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix q u t - progressionPowerModel q (κ * χ u) β t‖ ≤ (N : ℝ)*δ) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt
        ((((a : ℝ)/q : ℝ) : PrimeCircle) + (θ : PrimeCircle)) -
      (principalSquareSum q (a : ZMod q) * annularOscillatoryModel N 1 θ -
        twistedSquareSum q χ (a : ZMod q) * (κ * annularOscillatoryModel N β θ))‖ ≤
      (2 * Real.log R + 2 * Real.sqrt N * Real.log N) / N +
        (2 + 4 * Real.pi) * R^2 * δ :=
  annularMangoldt_majorArc_R_budget hN χ κ hβ a θ hR hδ
    (hq.trans (majorArc_rpow_denominator_le_square hR)) hθ hprefix

end PrimeSquares
