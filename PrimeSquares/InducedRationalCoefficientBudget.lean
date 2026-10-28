import PrimeSquares.ConductorEstimates
import PrimeSquares.ConductorDecay
import PrimeSquares.SourceInducedCharacters
import PrimeSquares.RationalGaussCoefficientBounds

namespace PrimeSquares

theorem induced_twistedSquareSum_div_bound (q₀ q : ℕ) [NeZero q₀] [NeZero q]
    (hdiv : q₀ ∣ q) (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    (a : ZMod q) (ha : IsUnit a) :
    ‖twistedSquareSum q (DirichletCharacter.changeLevel hdiv χ₀) a‖ ≤
      (32*conductorSigma q₀ χ₀)*(q/q₀ : ℕ)^(-(1/2 : ℝ))*conductorRho (q/q₀) := by
  obtain ⟨d,rfl⟩ := hdiv
  have hd : d ≠ 0 := by
    intro hz
    exact (NeZero.ne (q₀*d)) (by simp only [hz,mul_zero])
  have : NeZero d := ⟨hd⟩
  have he : q₀*d/q₀=d := Nat.mul_div_cancel_left d (NeZero.pos q₀)
  have h := induced_twistedSquareSum_conductor_bound q₀ d χ₀ hχ a ha
  rw [he,Real.rpow_neg (Nat.cast_nonneg d),←Real.sqrt_eq_rpow]
  simpa only [div_eq_mul_inv] using h

theorem sourceInduced_rationalGauss_div_bound (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic) (r : ℚ) (hdiv : q₀ ∣ r.den) :
    ‖rationalTwistedGauss r (sourceInducedCharacter q₀ χ₀ r)‖ ≤
      (32*conductorSigma q₀ χ₀)*(r.den/q₀ : ℕ)^(-(1/2 : ℝ))*conductorRho (r.den/q₀) := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  have ha : IsUnit (r.num : ZMod r.den) :=
    (ZMod.coe_int_isUnit_iff_isCoprime r.num r.den).mpr r.isCoprime_num_den.symm
  rw [sourceInducedCharacter_of_dvd q₀ χ₀ r hdiv]
  exact induced_twistedSquareSum_div_bound q₀ r.den hdiv χ₀ hχ _ ha

theorem conductorSigma_majorant_uniform : ∃ S : ℝ,0 < S ∧
    ∀ (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀),
      conductorSigma q₀ χ₀*(conductorMajorant q₀)^(1/2 : ℝ) ≤ S := by
  obtain ⟨S,hS,h⟩ := conductorSigma_majorant_decay
  refine ⟨S,hS,?_⟩
  intro q₀ inst χ₀
  rw [←Real.sqrt_eq_rpow]
  exact (h q₀ χ₀).trans (by
    have hq : (1 : ℝ) ≤ q₀ := by exact_mod_cast NeZero.pos q₀
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hq (by norm_num : (-(1/25 : ℝ)) ≤ 0)) hS.le)

end PrimeSquares
