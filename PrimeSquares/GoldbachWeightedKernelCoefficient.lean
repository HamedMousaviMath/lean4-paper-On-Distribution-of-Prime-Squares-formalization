import PrimeSquares.GoldbachWeightedScaleLimits
import PrimeSquares.GoldbachWeightedMeanAbel

set_option autoImplicit false
open Filter
namespace PrimeSquares

noncomputable def goldbachWeightedKernelCoefficient (q P A K δ K₀ K₁ ε L : ℝ) : ℝ :=
  (goldbachHalfMeanConstant+K*ε^δ)*(1+K₁/q)*
    Real.sqrt (1+Real.log 2/Real.sqrt L)*goldbachWeightedW (9/8)+
  (2*P*Real.sqrt q*q^6/Real.sqrt L+2*A*(1+Real.sqrt L)/(Real.sqrt q*Real.sqrt L))+
  6*(K₀+1)*(goldbachHalfMeanConstant+K*ε^δ)*(1+K₁/q)/
    (Real.sqrt (Real.sqrt L)*Real.sqrt L)

theorem goldbach_weighted_kernel_coefficient_limit (C P A K δ K₀ K₁ ε : ℝ)
    (hC : 0<C) (hP : 0≤P) (hA : 0≤A) :
    Tendsto (fun L : ℝ=>goldbachWeightedKernelCoefficient (C*Real.log L) P A K δ K₀ K₁ ε L)
      atTop (nhds ((goldbachHalfMeanConstant+K*ε^δ)*goldbachWeightedW (9/8))) := by
  have hh := ((goldbach_weighted_main_coefficient_limit C K δ K₁ ε hC).add
    (goldbach_weighted_small_coefficient_limit C P A hC hP hA)).add
      (goldbach_weighted_endpoint_coefficient_limit C K K₁ δ ε K₀ hC)
  simpa only [goldbachWeightedKernelCoefficient,add_zero] using hh

theorem goldbach_weighted_coefficient_factor (L q ratio P A K δ K₀ K₁ ε : ℝ)
    (hL : 0<L) (hq : 0<q) :
    2*(ratio*(P*q^6+A*(1+Real.sqrt L)/q))/L^2+
      ((goldbachHalfMeanConstant+K*ε^δ)*(1+K₁/q)*ratio/Real.sqrt q)*
        Real.sqrt (1+Real.log 2/Real.sqrt L)*goldbachWeightedW (9/8)/(L*Real.sqrt L)+
      6*(K₀+1)*((goldbachHalfMeanConstant+K*ε^δ)*(1+K₁/q)*ratio/Real.sqrt q)/
        (Real.sqrt (Real.sqrt L)*L^2)=
      (ratio/(Real.sqrt q*L*Real.sqrt L))*
        goldbachWeightedKernelCoefficient q P A K δ K₀ K₁ ε L := by
  have hsL : Real.sqrt L≠0 := (Real.sqrt_pos.mpr hL).ne'
  have hsq : Real.sqrt q≠0 := (Real.sqrt_pos.mpr hq).ne'
  have hs₂ : Real.sqrt (Real.sqrt L)≠0 := (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hL)).ne'
  dsimp only [goldbachWeightedKernelCoefficient]
  field_simp
  ring_nf
  simp only [Real.sq_sqrt hq.le,Real.sq_sqrt hL.le]
  rw [show (Real.sqrt L)^3=Real.sqrt L*L by rw [pow_succ,Real.sq_sqrt hL.le];ring]
  ring

theorem goldbach_weighted_mean_interval (hT : ClassicalHalfMeanValueInput)
    (K₀ K₁ : ℝ) (hK₀ : 0≤K₀) (hK₁ : 0≤K₁)
    (hM : ClassicalPrimeLogMertens K₀) (hV : ClassicalPrimeMertensRatios K₁) :
    ∃ K δ : ℝ,0<K ∧ 0<δ ∧ ∀ R : ℝ,3≤R→∀ n : ℤ,∀ a ε : ℝ,
      Real.exp 16<a→1/Real.sqrt (Real.log a)<ε→ε≤1/2→R≤a^ε→
      6*Real.log R+10*K₀≤ε^2*Real.log a→∀ t : ℝ,a≤t→
      goldbachRealSummatory (goldbachWeightedMultiplicative R n) t≤
        goldbachWeightedMeanAmplitude K δ K₁ R n ε*t/Real.sqrt (Real.log t) := by
  obtain ⟨K,δ,hK,hδ,hbound⟩ := goldbach_weighted_mean_normalized hT K₀ K₁ hK₀ hK₁ hM hV
  refine ⟨K,δ,hK,hδ,?_⟩
  intro R hR n a ε ha hε hεB hRa hbudget t hat
  have ha1 : 1<a := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<16)).trans ha
  have hloga : 0<Real.log a := Real.log_pos ha1
  have hε0 : 0<ε := (one_div_pos.mpr (Real.sqrt_pos.mpr hloga)).trans hε
  have hlogt := Real.log_le_log (by linarith : 0<a) hat
  have hεt : 1/Real.sqrt (Real.log t)<ε :=
    (one_div_le_one_div_of_le (Real.sqrt_pos.mpr hloga) (Real.sqrt_le_sqrt hlogt)).trans_lt hε
  have hRt : R≤t^ε := hRa.trans (Real.rpow_le_rpow (by linarith : 0≤a) hat hε0.le)
  have hbudgett : 6*Real.log R+10*K₀≤ε^2*Real.log t :=
    hbudget.trans (mul_le_mul_of_nonneg_left hlogt (sq_nonneg ε))
  have hh := hbound R hR n t ε (ha.trans_le hat) hεt hεB hRt hbudgett
  rw [goldbachRealSummatory,←Nat.range_succ_eq_Icc_zero]
  apply hh.trans_eq
  dsimp only [goldbachWeightedMeanAmplitude]
  ring

end PrimeSquares
