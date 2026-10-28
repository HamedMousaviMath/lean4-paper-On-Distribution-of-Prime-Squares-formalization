import PrimeSquares.SharpOrdinaryExceptionalMaximum
import PrimeSquares.ConductorLogarithmicAbsorption

open scoped lp
namespace PrimeSquares

noncomputable def sharpHighMaximalRate (Q : ℝ) : ℝ :=
  Q^(-(1/2 : ℝ))*Real.exp (gaussAnalyticMajorant (Real.log Q))*(1+Real.log Q)^3

theorem sharpHighMaximalRate_nonneg {Q : ℝ} (hQ : 1 ≤ Q) : 0 ≤ sharpHighMaximalRate Q := by
  have hl := Real.log_nonneg hQ
  unfold sharpHighMaximalRate
  positivity

theorem sharpOrdinary_rate_maximum {C : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C)
    {M : ℕ} (hM : 2 ≤ M) {Q : ℝ} (hQ : 16 ≤ Q) (hL : 2 ≤ Real.log Q)
    (hSlope : gaussThresholdSlope (Real.log Q) ≤ 1/4)
    (R : ℕ → ℝ) (hR : ∀ j,0 ≤ R j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (thresholdAnnularBlock (sourceRationalCenters (R j)) ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) 1 Q rationalPrincipalGauss) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (4*sharpThresholdMaximalConstant C*sharpHighMaximalRate Q)*‖f‖ := by
  obtain ⟨g,hg,ht,hn⟩ := sharpOrdinary_source_maximum hC hBourgain hM hQ hL hSlope R hR f
  refine ⟨g,hg,ht,hn.trans_eq ?_⟩
  unfold sharpThresholdAmplitude sharpHighMaximalRate
  rw [Real.one_rpow]
  ring

theorem sharpExceptional_conductor_rate {C : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C) :
    ∃ Q₀ H : ℝ,16 ≤ Q₀ ∧ 0<H ∧ ∀ Q : ℝ,Q₀ ≤ Q → 2 ≤ Real.log Q →
    gaussThresholdSlope (Real.log Q) ≤ 1/4 → ∀ (M : ℕ) (hM : 2 ≤ M)
      (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀),χ₀.IsQuadratic →
    ∀ (β : ℕ → ℝ),(∀ j,0 ≤ β j) → (∀ j,β j ≤ 1) →
    ∀ (R : ℕ → ℝ),(∀ j,0 ≤ R j) → ∀ f : ℓ²(ℤ,ℂ),
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (thresholdAnnularBlock
        ((sourceRationalCenters (R j)).filter (fun r => q₀ ∣ r.den)) ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) (β j) (Q*(q₀ : ℝ)/conductorMajorant q₀)
        (fun r => rationalTwistedGauss r (sourceInducedCharacter q₀ χ₀ r))) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (H*(q₀ : ℝ)^(-(1/50 : ℝ))*sharpHighMaximalRate Q)*‖f‖ := by
  obtain ⟨L,hL,hdec⟩ := conductor_logarithmic_decay
  obtain ⟨T,hT,hthresh⟩ := effective_threshold_large_uniform
  have hK := sharpThresholdMaximalConstant_nonneg hC
  let H := 1+32*sharpThresholdMaximalConstant C*L
  refine ⟨max 16 (16*T),H,le_max_left _ _,by dsimp [H];positivity,?_⟩
  intro Q hQ hLQ hSlope M hM q₀ inst χ₀ hχ β hβ0 hβ1 R hR f
  have hQ16 : 16 ≤ Q := (le_max_left _ _).trans hQ
  have hQ1 : 1 ≤ Q := by linarith
  have hQp : 0<Q := by linarith
  have hW := hthresh Q ((le_max_right _ _).trans hQ) q₀ (NeZero.pos q₀)
  have hB := conductorMajorant_one_le q₀ (NeZero.pos q₀)
  have hqp : (0 : ℝ)<q₀ := by exact_mod_cast NeZero.pos q₀
  have hupper : Q*(q₀ : ℝ)/conductorMajorant q₀ ≤ Q*(q₀ : ℝ) :=
    div_le_self (mul_nonneg hQp.le hqp.le) hB
  have hlog := effective_threshold_logarithmic_bound hQ1 (by linarith : 1 ≤ Q*(q₀ : ℝ)/conductorMajorant q₀)
    q₀ (NeZero.pos q₀) hupper
  obtain ⟨g,hg,ht,hn⟩ := sharpExceptional_source_maximum hC hBourgain hM hQp hLQ hSlope q₀ χ₀ hχ hW β hβ0 hβ1 R hR f
  refine ⟨g,hg,ht,hn.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  have hσ := conductorSigma_nonneg q₀ χ₀
  have hQlog := Real.log_nonneg hQ1
  have hfac : 0 ≤ sharpThresholdMaximalConstant C*sharpThresholdAmplitude (32*conductorSigma q₀ χ₀)
      (conductorMajorant q₀) Q := by
    apply mul_nonneg hK
    exact sharpThresholdAmplitude_nonneg (mul_nonneg (by norm_num) hσ) (by linarith) hQp.le
  have hlogstep := mul_le_mul_of_nonneg_left hlog hfac
  have hdecstep := mul_le_mul_of_nonneg_left (hdec q₀ χ₀)
    (show 0 ≤ (32*sharpThresholdMaximalConstant C)*sharpHighMaximalRate Q by
      exact mul_nonneg (mul_nonneg (by norm_num) hK) (sharpHighMaximalRate_nonneg hQ1))
  have hH : 32*sharpThresholdMaximalConstant C*L ≤ H := by dsimp [H];linarith
  calc
    _ ≤ sharpThresholdMaximalConstant C*sharpThresholdAmplitude (32*conductorSigma q₀ χ₀)
        (conductorMajorant q₀) Q*((1+Real.log Q)^3*(1+Real.log q₀)^3) := hlogstep
    _ = (32*sharpThresholdMaximalConstant C)*sharpHighMaximalRate Q*
        (conductorSigma q₀ χ₀*(conductorMajorant q₀)^(1/2 : ℝ)*(1+Real.log q₀)^3) := by
      unfold sharpThresholdAmplitude sharpHighMaximalRate;ring
    _ ≤ (32*sharpThresholdMaximalConstant C)*sharpHighMaximalRate Q*(L*(q₀ : ℝ)^(-(1/50 : ℝ))) := hdecstep
    _ = (32*sharpThresholdMaximalConstant C*L)*(q₀ : ℝ)^(-(1/50 : ℝ))*sharpHighMaximalRate Q := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hH (by positivity))
      (sharpHighMaximalRate_nonneg hQ1)

end PrimeSquares
