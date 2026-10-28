import PrimeSquares.SummableCutoffHighMaximum

open Finset
open scoped lp
namespace PrimeSquares

theorem actualSource_restricted_pairing {η P C B d c A : ℝ} (hη0 : 0 < η) (hηhalf : η < 1/2)
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ d) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ H : ℝ,0 < H ∧ ∃ N₀ : ℕ,4 ≤ N₀ ∧ ∀ N : ℕ,N₀ ≤ N → ∀ Q : ℝ,2 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log N) →
    ∀ (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀),χ₀.IsQuadratic →
    ∀ (active : Bool) (β : ℝ),
      CircleAnalyticInputs N Q (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β P C B d c →
    ∀ F G : Finset ℤ,
      ‖restrictedKernelPairing (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F G‖ ≤
        (2*realLowAmplitude N Q)*(F.card : ℝ)*(G.card : ℝ)+
        H*Q^(-η)*Real.sqrt (F.card : ℝ)*Real.sqrt (G.card : ℝ) := by
  obtain ⟨H,hH,N₀,hN₀,h⟩ := actualSource_low_remainder_uniform hη0 hηhalf hP hC hB hd hc hA
  refine ⟨H,hH,N₀,hN₀,?_⟩
  intro N hn Q hQ hQl q₀ inst χ₀ hχ active β hi F G
  have hN : 1 ≤ N := by omega
  let Γ := sourceRationalCenters (sourceMajorArcScale N Q)
  let χ := sourceInducedCharacter q₀ χ₀
  let κ := sourceExceptionalSelector q₀ active
  let Lo := circleLowOperator Γ N hN q₀ Q (conductorMajorant q₀) χ κ β
  let T := sourceRemainderOperator Γ N hN q₀ Q (conductorMajorant q₀) χ κ β
  obtain ⟨hl,ht⟩ := h N hn Q hQ hQl q₀ χ₀ hχ active β hi hN
  have hlF : ‖Lo (finiteIndicatorLp F 1)‖ ≤ (2*realLowAmplitude N Q)*(F.card : ℝ) := by
    have hb := Lo.le_of_opNorm_le hl (finiteIndicatorLp F 1)
    simpa only [finiteIndicatorLp_one_norm] using hb
  have htF : ‖T (finiteIndicatorLp F 2)‖ ≤ H*Q^(-η)*Real.sqrt (F.card : ℝ) := by
    have hb := T.le_of_opNorm_le ht (finiteIndicatorLp F 2)
    simpa only [finiteIndicatorLp_two_norm] using hb
  have heq : ∀ x ∈ G,indicatorConvolution (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F x=
      Lo (finiteIndicatorLp F 1) x+T (finiteIndicatorLp F 2) x := by
    intro x _
    have hh := annularKernel_low_remainder Γ N hN q₀ Q (conductorMajorant q₀) χ κ β F (fun _ => 1) x
    simpa only [finiteConvolution_indicator,finiteInputLp_one] using hh
  have hb := finite_highLow_pairing_bound G _ (fun x => Lo (finiteIndicatorLp F 1) x)
    (T (finiteIndicatorLp F 2)) ((2*realLowAmplitude N Q)*(F.card : ℝ)) heq
    (fun x _ => (lp.norm_apply_le_norm ENNReal.top_ne_zero (Lo (finiteIndicatorLp F 1)) x).trans hlF)
  calc
    _ ≤ (G.card : ℝ)*((2*realLowAmplitude N Q)*(F.card : ℝ))+
        ‖T (finiteIndicatorLp F 2)‖*Real.sqrt (G.card : ℝ) := hb
    _ ≤ (G.card : ℝ)*((2*realLowAmplitude N Q)*(F.card : ℝ))+
        (H*Q^(-η)*Real.sqrt (F.card : ℝ))*Real.sqrt (G.card : ℝ) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right htF (Real.sqrt_nonneg _))
    _ = _ := by ring

end PrimeSquares
