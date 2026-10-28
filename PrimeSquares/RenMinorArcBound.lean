import PrimeSquares.RenSumCompatibility

namespace PrimeSquares

noncomputable def renEffectiveDenominator (q : ℕ) (x θ : ℝ) : ℝ :=
  (q : ℝ) * (1 + |θ| * x^2)

noncomputable def renQuadraticBracket (x T : ℝ) : ℝ :=
  Real.sqrt x * Real.sqrt T + x^(4/5 : ℝ) + x / Real.sqrt T

theorem annularMangoldt_from_Ren_bound (N : ℕ) (ξ B T : ℝ)
    (hRen : ‖renQuadraticSum ((N : ℝ)/2) ξ‖ ≤ B * renQuadraticBracket ((N : ℝ)/2) T) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle)‖ ≤
      B * renQuadraticBracket ((N : ℝ)/2) T / N := by
  rw [annularMangoldtSymbol_norm_Ren]
  calc
    _ ≤ (N : ℝ)⁻¹ * (B * renQuadraticBracket ((N : ℝ)/2) T) :=
      mul_le_mul_of_nonneg_left hRen (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = _ := by ring

theorem ren_bracket_central_bound {x R T : ℝ} (hx : 0 < x) (hR : 0 < R)
    (hTlow : R ≤ T) (hThigh : T ≤ x/R) (hRsize : R ≤ x^(2/5 : ℝ)) :
    renQuadraticBracket x T ≤ 3*x / Real.sqrt R := by
  have hRs : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hT : 0 < T := hR.trans_le hTlow
  have hTR : T*R ≤ x := (le_div_iff₀ hR).mp hThigh
  have hm : Real.sqrt T * Real.sqrt R ≤ Real.sqrt x := by
    rw [← Real.sqrt_mul hT.le]
    exact Real.sqrt_le_sqrt hTR
  have h1 : Real.sqrt x * Real.sqrt T ≤ x / Real.sqrt R := by
    apply (le_div_iff₀ hRs).mpr
    have h := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg x)
    nlinarith [Real.sq_sqrt hx.le]
  have hrhalf : Real.sqrt R ≤ x^(1/5 : ℝ) := by
    have h := Real.sqrt_le_sqrt hRsize
    rw [Real.sqrt_eq_rpow (x^(2/5 : ℝ)), ← Real.rpow_mul hx.le] at h
    norm_num at h
    exact h
  have hpow : x^(4/5 : ℝ) * x^(1/5 : ℝ) = x := by
    rw [← Real.rpow_add hx]
    norm_num
  have h2 : x^(4/5 : ℝ) ≤ x / Real.sqrt R := by
    apply (le_div_iff₀ hRs).mpr
    have h := mul_le_mul_of_nonneg_left hrhalf (Real.rpow_nonneg hx.le (4/5 : ℝ))
    rwa [hpow] at h
  have h3 : x / Real.sqrt T ≤ x / Real.sqrt R :=
    div_le_div_of_nonneg_left hx.le hRs (Real.sqrt_le_sqrt hTlow)
  calc
    _ ≤ x / Real.sqrt R + x / Real.sqrt R + x / Real.sqrt R :=
      add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

theorem annularMangoldt_Ren_central_bound {N : ℕ} (hN : 1 ≤ N)
    (ξ : ℝ) {B R T : ℝ} (hB : 0 ≤ B) (hR : 0 < R)
    (hTlow : R ≤ T) (hThigh : T ≤ ((N : ℝ)/2)/R)
    (hRsize : R ≤ ((N : ℝ)/2)^(2/5 : ℝ))
    (hRen : ‖renQuadraticSum ((N : ℝ)/2) ξ‖ ≤ B * renQuadraticBracket ((N : ℝ)/2) T) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle)‖ ≤
      3*B / (2 * Real.sqrt R) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := ren_bracket_central_bound (by positivity : (0 : ℝ) < (N : ℝ)/2)
    hR hTlow hThigh hRsize
  calc
    _ ≤ B * renQuadraticBracket ((N : ℝ)/2) T / N := annularMangoldt_from_Ren_bound N ξ B T hRen
    _ ≤ B * (3*((N : ℝ)/2) / Real.sqrt R) / N :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hB) hNr.le
    _ = _ := by field_simp [hNr.ne', (Real.sqrt_pos.mpr hR).ne']

theorem annularMangoldt_Ren_central_source {N : ℕ} (hN : 4 ≤ N)
    (q : ℕ) (ξ θ A : ℝ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hTlow : R ≤ renEffectiveDenominator q ((N : ℝ)/2) θ)
    (hThigh : renEffectiveDenominator q ((N : ℝ)/2) θ ≤ ((N : ℝ)/2)/R)
    (hRsize : R ≤ ((N : ℝ)/2)^(2/5 : ℝ))
    (hRen : ‖renQuadraticSum ((N : ℝ)/2) ξ‖ ≤
      (C * (q.divisors.card : ℝ)^(3/2 : ℝ) * (Real.log ((N : ℝ)/2))^A) *
        renQuadraticBracket ((N : ℝ)/2) (renEffectiveDenominator q ((N : ℝ)/2) θ)) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle)‖ ≤
      3 * (C * (q.divisors.card : ℝ)^(3/2 : ℝ) * (Real.log ((N : ℝ)/2))^A) /
        (2 * Real.sqrt R) := by
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log ((N : ℝ)/2) := Real.log_nonneg (by linarith)
  exact annularMangoldt_Ren_central_bound (by omega) ξ (by positivity) hR hTlow hThigh hRsize hRen

theorem ren_first_term_diagonal {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * Real.sqrt x / x = 1 := by
  rw [Real.mul_self_sqrt hx.le, div_self hx.ne']

end PrimeSquares
