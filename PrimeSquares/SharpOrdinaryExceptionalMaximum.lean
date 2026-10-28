import PrimeSquares.SharpThresholdCountableMaximum
import PrimeSquares.CenteredHighThresholdProfile

open Finset
open scoped lp
namespace PrimeSquares

theorem sharpOrdinary_source_maximum {C : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C)
    {M : ℕ} (hM : 2 ≤ M) {Q : ℝ} (hQ : 16 ≤ Q) (hL : 2 ≤ Real.log Q)
    (hSlope : gaussThresholdSlope (Real.log Q) ≤ 1/4)
    (R : ℕ → ℝ) (hR : ∀ j,0 ≤ R j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (thresholdAnnularBlock (sourceRationalCenters (R j)) ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) 1 Q rationalPrincipalGauss) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (sharpThresholdMaximalConstant C*sharpThresholdAmplitude 4 1 Q*(1+Real.log Q)^3)*‖f‖ := by
  classical
  simpa only [filter_true] using sharpThreshold_countable_maximum hC hBourgain hM (fun _ => True)
    (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (1 : ℝ) ≤ 1) (by linarith : 0<Q) hQ hL hSlope
    Rat.den (fun r _ _ => r.den_pos) (fun r _ _ => by ring) rationalPrincipalGauss
    (fun r _ _ => principal_rationalGauss_rho_bound r) (fun _ => (1 : ℝ)) (fun _ => by norm_num)
    (fun _ => by norm_num) R hR f

theorem sharpExceptional_source_maximum {C : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C)
    {M : ℕ} (hM : 2 ≤ M) {Q : ℝ} (hQ : 0<Q) (hL : 2 ≤ Real.log Q)
    (hSlope : gaussThresholdSlope (Real.log Q) ≤ 1/4)
    (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic)
    (hW : 16 ≤ Q*(q₀ : ℝ)/conductorMajorant q₀)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (R : ℕ → ℝ) (hR : ∀ j,0 ≤ R j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (thresholdAnnularBlock
        ((sourceRationalCenters (R j)).filter (fun r => q₀ ∣ r.den)) ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) (β j) (Q*(q₀ : ℝ)/conductorMajorant q₀)
        (fun r => rationalTwistedGauss r (sourceInducedCharacter q₀ χ₀ r))) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (sharpThresholdMaximalConstant C*sharpThresholdAmplitude (32*conductorSigma q₀ χ₀)
        (conductorMajorant q₀) Q*(1+Real.log (Q*(q₀ : ℝ)/conductorMajorant q₀))^3)*‖f‖ := by
  classical
  have hBp : 0<conductorMajorant q₀ := lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le q₀ (NeZero.pos q₀))
  have hqp : (0 : ℝ)<q₀ := by exact_mod_cast NeZero.pos q₀
  apply sharpThreshold_countable_maximum hC hBourgain hM (fun r => q₀ ∣ r.den)
    (mul_nonneg (by norm_num) (conductorSigma_nonneg _ _))
    (conductorMajorant_one_le q₀ (NeZero.pos q₀)) hQ hW hL hSlope (fun r => r.den/q₀)
  · intro r _ hd
    exact Nat.div_pos (Nat.le_of_dvd r.den_pos hd) (NeZero.pos q₀)
  · intro r _ hd
    have he : (q₀ : ℝ)*(r.den/q₀ : ℕ)=(r.den : ℝ) := by exact_mod_cast Nat.mul_div_cancel' hd
    rw [←he]
    field_simp
  · intro r _ hd
    exact sourceInduced_rationalGauss_div_bound q₀ χ₀ hχ r hd
  · exact hβ0
  · exact hβ1
  · exact hR

theorem thresholdAnnularBlock_mask (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (β W : ℝ)
    (q₀ : ℕ) (c : ℚ → ℂ) (active : Bool) :
    thresholdAnnularBlock Γ N hN β W (fun r => sourceExceptionalSelector q₀ active r*c r)=
      if active then thresholdAnnularBlock (Γ.filter (fun r => q₀ ∣ r.den)) N hN β W c else 0 := by
  classical
  cases active
  · ext θ
    simp only [thresholdAnnularBlock,sourceExceptionalSelector,Bool.false_eq_true,false_and,ite_false,
      zero_mul,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,ContinuousMap.zero_apply]
    simp only [sum_const_zero]
  · simp only [ite_true,thresholdAnnularBlock,sum_filter]
    apply sum_congr rfl
    intro r _
    simp only [sourceExceptionalSelector,true_and]
    split_ifs
    · rw [one_mul]
    · rw [zero_mul]
      ext θ
      simp only [ContinuousMap.smul_apply,smul_eq_mul,zero_mul,ContinuousMap.zero_apply]

end PrimeSquares
