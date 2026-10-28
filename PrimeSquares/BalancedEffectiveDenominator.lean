import PrimeSquares.RenMinorArcBound

namespace PrimeSquares

theorem renEffectiveDenominator_ge (q : ℕ) (x θ : ℝ) :
    (q : ℝ) ≤ renEffectiveDenominator q x θ := by
  dsimp [renEffectiveDenominator]
  nlinarith [mul_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    (mul_nonneg (abs_nonneg θ) (sq_nonneg x))]

theorem renEffectiveDenominator_balanced_upper {x θ : ℝ} (hx : 0 < x)
    (q : ℕ) (hq : 0 < q) (hql : (q : ℝ) ≤ x^(1/2 : ℝ))
    (hθ : |θ| ≤ 1/((q : ℝ)*x^(3/2 : ℝ))) :
    renEffectiveDenominator q x θ ≤ 2*x^(1/2 : ℝ) := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hhalf := Real.rpow_pos_of_pos hx (1/2 : ℝ)
  have hthree := Real.rpow_pos_of_pos hx (3/2 : ℝ)
  have hm := (le_div_iff₀ (mul_pos hqp hthree)).mp hθ
  have he : x^2 = x^(3/2 : ℝ)*x^(1/2 : ℝ) := by
    rw [←Real.rpow_add hx]
    norm_num
  have hb : (q : ℝ)* |θ| *x^2 ≤ x^(1/2 : ℝ) := by
    calc
      _ = (|θ| *((q : ℝ)*x^(3/2 : ℝ)))*x^(1/2 : ℝ) := by rw [he];ring
      _ ≤ 1*x^(1/2 : ℝ) := mul_le_mul_of_nonneg_right hm hhalf.le
      _ = _ := one_mul _
  dsimp [renEffectiveDenominator]
  nlinarith only [hql,hb]

theorem renEffectiveDenominator_lower_from_arc {x θ R : ℝ}
    (hx : 0 < x) (_hR : 0 ≤ R) (q : ℕ) (hq : 0 < q)
    (hout : R ≤ (q : ℝ) ∨ R/(4*(q : ℝ)*x^2) ≤ |θ|) :
    R/4 ≤ renEffectiveDenominator q x θ := by
  rcases hout with h | h
  · exact (by linarith : R/4 ≤ (q : ℝ)).trans (renEffectiveDenominator_ge q x θ)
  · have hqp : (0 : ℝ) < q := by exact_mod_cast hq
    have hm := (div_le_iff₀ (by positivity : 0 < 4*(q : ℝ)*x^2)).mp h
    dsimp [renEffectiveDenominator]
    nlinarith only [hm,hqp]

end PrimeSquares
