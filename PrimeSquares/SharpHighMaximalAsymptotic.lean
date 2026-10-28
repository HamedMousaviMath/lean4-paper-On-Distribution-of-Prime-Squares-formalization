import PrimeSquares.SharpConductorMaximalRate
import PrimeSquares.SourceHighOrliczUniform
import PrimeSquares.SharpHighSourceLogLoss

open Filter Topology
namespace PrimeSquares

theorem sharpHighMaximalRate_asymptotic (HP : PrimeAsymptoticInputs) {ε : ℝ} (hε : 0<ε) :
    ∃ Q₀ D : ℝ,16 ≤ Q₀ ∧ 0<D ∧ ∀ Q : ℝ,Q₀ ≤ Q →
      2 ≤ Real.log Q ∧ gaussThresholdSlope (Real.log Q) ≤ 1/4 ∧
      sharpHighMaximalRate Q ≤ D*Q^(-(1/2 : ℝ))*
        Real.exp ((2+ε)*sharpHighExponentWeight (Real.log Q)) := by
  obtain ⟨L,hL⟩ := ((gaussAnalyticMajorant_unregularized_eventually HP
    (by linarith : (2 : ℝ)<2+ε/2)).and gaussThresholdSlope_eventually_quarter).exists_forall_of_atTop
  obtain ⟨D,hD,hpoly⟩ := sharpHigh_source_log_loss (by linarith : (0 : ℝ)<ε/2) 3 (2+ε/2)
  let Y := max (Real.log 16) (max 2 L)
  refine ⟨Real.exp Y,D,?_,hD,?_⟩
  · exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ)<16)).mp (le_max_left _ _)
  intro Q hQ
  have hQp : 0<Q := (Real.exp_pos Y).trans_le hQ
  have hY : Y ≤ Real.log Q := by
    have h := Real.log_le_log (Real.exp_pos Y) hQ
    simpa only [Real.log_exp] using h
  have h2 : 2 ≤ Real.log Q := ((le_max_left _ _).trans (le_max_right _ _)).trans hY
  have hlow : L ≤ Real.log Q := ((le_max_right _ _).trans (le_max_right _ _)).trans hY
  have hg := hL (Real.log Q) hlow
  refine ⟨h2,hg.2.2,?_⟩
  have hG : gaussAnalyticMajorant (Real.log Q) ≤ (2+ε/2)*sharpHighExponentWeight (Real.log Q) := by
    simpa only [gaussAsymptoticScale,sharpHighExponentWeight] using hg.1
  have hpoly' : (1+Real.log Q)^3*Real.exp ((2+ε/2)*sharpHighExponentWeight (Real.log Q)) ≤
      D*Real.exp ((2+ε)*sharpHighExponentWeight (Real.log Q)) := by
    have h := hpoly Q h2
    rw [show 2+ε/2+ε/2=2+ε by ring] at h
    exact h
  have hlQ : 0 ≤ Real.log Q := by linarith
  calc
    _ ≤ Q^(-(1/2 : ℝ))*((1+Real.log Q)^3*
        Real.exp ((2+ε/2)*sharpHighExponentWeight (Real.log Q))) := by
      unfold sharpHighMaximalRate
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hG)
        (by positivity : (0 : ℝ) ≤ Q^(-(1/2 : ℝ)))) (by positivity : (0 : ℝ) ≤ (1+Real.log Q)^3)
      convert h using 1;ring
    _ ≤ Q^(-(1/2 : ℝ))*(D*Real.exp ((2+ε)*sharpHighExponentWeight (Real.log Q))) :=
      mul_le_mul_of_nonneg_left hpoly' (by positivity)
    _ = _ := by ring

end PrimeSquares
