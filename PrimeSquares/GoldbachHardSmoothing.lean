import PrimeSquares.GoldbachCompletionParameters

set_option autoImplicit false
open MeasureTheory
open scoped SchwartzMap
namespace PrimeSquares

noncomputable def goldbachHardCutoff (N : ℕ) (R γ : ℝ) : ℂ :=
  {x : ℝ | |x|≤R/(N:ℝ)^2}.indicator (fun _=>1) γ

noncomputable def goldbachHardSingularIntegral (N ℓ : ℕ) (R n U W : ℝ) : ℂ :=
  (ℓ:ℂ)*∫ γ in {γ : ℝ | |γ|≤R/(N:ℝ)^2},
    goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ*realFourierPhase (-n*γ)

theorem goldbach_hard_cutoff_measurable (N : ℕ) (R : ℝ) : Measurable (goldbachHardCutoff N R) :=
  measurable_const.indicator (measurableSet_le (show Measurable (fun γ : ℝ=>|γ|) by fun_prop) measurable_const)

theorem goldbach_hard_cutoff_norm (N : ℕ) (R γ : ℝ) : ‖goldbachHardCutoff N R γ‖≤1 := by
  by_cases h : |γ|≤R/(N:ℝ)^2 <;> simp [goldbachHardCutoff,h]

theorem goldbach_euclidean_product_phase_integrable (N ℓ : ℕ) (hN : 0<N) (hℓ : 0<ℓ)
    {U W : ℝ} (hU : 2≤U) (hUN : U≤N) (hW : 2≤W) (n : ℝ) :
    Integrable (fun γ : ℝ=>goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ*realFourierPhase (-n*γ)) := by
  by_cases hX : 2≤(N:ℝ)^2/ℓ
  · have hi := (goldbach_euclidean_product_integrable N ℓ hN hℓ hU hUN hW hX).1
    have hsm : StronglyMeasurable (fun γ : ℝ=>goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ*realFourierPhase (-n*γ)) := ((goldbachSquareIntegral_stronglyMeasurable U).mul
      (goldbachLinearSourceIntegral_stronglyMeasurable N ℓ hℓ W)).mul
      (realFourierPhase_continuous.comp (by fun_prop)).stronglyMeasurable
    apply hi.norm.mono' hsm.aestronglyMeasurable
    filter_upwards with γ
    simp only [norm_mul,realFourierPhase_norm,mul_one]
    exact le_rfl
  · simp only [goldbach_linear_source_integral_empty N ℓ hℓ (le_of_not_ge hX),mul_zero,zero_mul]
    exact MeasureTheory.integrable_zero ℝ ℂ volume

theorem goldbach_frequency_tail_norm (f : ℝ→ℂ) (hf : StronglyMeasurable f) {c D : ℝ}
    (hc : 0<c) (hD : 0≤D) (hdecay : ∀ γ : ℝ,c < |γ| →‖f γ‖≤D*|γ|^(-(3/2:ℝ))) :
    ‖∫ γ in {γ : ℝ | c < |γ|},f γ‖≤4*D/Real.sqrt c := by
  let s := {γ : ℝ | c < |γ|}
  have hs : MeasurableSet s := measurableSet_lt measurable_const (show Measurable (fun γ : ℝ=>|γ|) by fun_prop)
  have hi := goldbach_two_sided_integrable_decay (s.indicator f) (hf.indicator hs) hc hD
    (M:=0) (fun γ hγ=>by
      rw [Set.indicator_of_notMem (show γ∉s from fun h=>not_lt_of_ge hγ h),norm_zero])
    (fun γ hγ=>by rw [Set.indicator_of_mem (show γ∈s from hγ)];exact hdecay γ hγ)
  rw [←integral_indicator hs]
  exact (norm_integral_le_integral_norm _).trans (by simpa only [mul_zero,zero_mul,zero_add] using hi.2)

theorem goldbach_euclidean_product_phase_tail (N ℓ : ℕ) (hℓ : 0<ℓ)
    {U W c : ℝ} (hU : 2≤U) (hW : 2≤W) (hc : 0<c) (n : ℝ) :
    ‖∫ γ in {γ : ℝ | c < |γ|},goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ*realFourierPhase (-n*γ)‖≤
      (4*goldbachEuclideanDecayConstant/(ℓ:ℝ))/Real.sqrt c := by
  have hl : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  have hsm : StronglyMeasurable (fun γ : ℝ=>goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ*realFourierPhase (-n*γ)) := ((goldbachSquareIntegral_stronglyMeasurable U).mul
    (goldbachLinearSourceIntegral_stronglyMeasurable N ℓ hℓ W)).mul
    (realFourierPhase_continuous.comp (by fun_prop)).stronglyMeasurable
  have hd (γ : ℝ) (hγ : c < |γ|) :
      ‖goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ*realFourierPhase (-n*γ)‖≤
        (goldbachEuclideanDecayConstant/(ℓ:ℝ))*|γ|^(-(3/2:ℝ)) := by
    by_cases hX : 2≤(N:ℝ)^2/ℓ
    · simpa only [norm_mul,realFourierPhase_norm,mul_one] using
        goldbach_euclidean_product_decay N ℓ hℓ hU hW hX (abs_pos.mp (hc.trans hγ))
    · simp only [goldbach_linear_source_integral_empty N ℓ hℓ (le_of_not_ge hX),mul_zero,zero_mul,norm_zero]
      have := goldbachEuclideanDecayConstant_pos
      positivity
  exact (goldbach_frequency_tail_norm _ hsm hc (by have := goldbachEuclideanDecayConstant_pos;positivity) hd).trans_eq (by ring)

theorem goldbach_hard_unsmoothed_comparison (N ℓ : ℕ) (hN : 0<N) (hℓ : 0<ℓ)
    {R U W : ℝ} (hR : 0<R) (hU : 2≤U) (hUN : U≤N) (hW : 2≤W) (n : ℝ) :
    ‖goldbachHardSingularIntegral N ℓ R n U W-goldbachUnsmoothedSingularIntegral N ℓ n U W‖≤
      4*goldbachEuclideanDecayConstant*(N:ℝ)/Real.sqrt R := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hl : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  let c := R/(N:ℝ)^2
  let f := fun γ : ℝ=>goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ*realFourierPhase (-n*γ)
  have hc : 0<c := by dsimp [c];positivity
  have hs : MeasurableSet {γ : ℝ | |γ|≤c} := measurableSet_le (show Measurable (fun γ : ℝ=>|γ|) by fun_prop) measurable_const
  have hfi : Integrable f := goldbach_euclidean_product_phase_integrable N ℓ hN hℓ hU hUN hW n
  have heS : {γ : ℝ | |γ|≤c}ᶜ={γ : ℝ | c < |γ|} := by
    ext γ
    simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,not_le]
  have hsplit := integral_add_compl hs hfi
  rw [heS] at hsplit
  have he : goldbachHardSingularIntegral N ℓ R n U W-goldbachUnsmoothedSingularIntegral N ℓ n U W=
      -(ℓ:ℂ)*(∫ γ in {γ : ℝ | c < |γ|},f γ) := by
    unfold goldbachHardSingularIntegral goldbachUnsmoothedSingularIntegral
    change (ℓ:ℂ)*(∫ γ in {γ : ℝ | |γ|≤c},f γ)-(ℓ:ℂ)*(∫ γ : ℝ,f γ)=_
    rw [←hsplit]
    ring
  have htail := goldbach_euclidean_product_phase_tail N ℓ hℓ hU hW hc n
  have hroot : Real.sqrt c=Real.sqrt R/(N:ℝ) := by
    dsimp [c]
    rw [Real.sqrt_div hR.le,Real.sqrt_sq_eq_abs,abs_of_pos hn]
  rw [he,norm_mul,norm_neg,Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left htail hl.le).trans_eq
  rw [hroot]
  field_simp

theorem goldbach_hard_singular_smoothing_uniform (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0) :
    ∃ K : ℝ,0<K ∧ ∀ N ℓ : ℕ,0<N →0<ℓ →∀ R U W n : ℝ,
      0<R →2≤U →U≤N →2≤W →
      ‖goldbachHardSingularIntegral N ℓ R n U W-goldbachSingularIntegral ψ N ℓ R n U W‖≤
        K*(N:ℝ)/Real.sqrt R := by
  obtain ⟨K,hK,hSmooth⟩ := goldbach_singular_smoothing_uniform ψ hψ
  refine ⟨4*goldbachEuclideanDecayConstant+K,by have := goldbachEuclideanDecayConstant_pos;positivity,?_⟩
  intro N ℓ hN hℓ R U W n hR hU hUN hW
  have hHard := goldbach_hard_unsmoothed_comparison N ℓ hN hℓ hR hU hUN hW n
  have hSoft := hSmooth N ℓ hN hℓ R U W n hR hU hUN hW
  calc
    _=‖(goldbachHardSingularIntegral N ℓ R n U W-goldbachUnsmoothedSingularIntegral N ℓ n U W)+
        (goldbachUnsmoothedSingularIntegral N ℓ n U W-goldbachSingularIntegral ψ N ℓ R n U W)‖ := by congr 1;ring
    _≤‖goldbachHardSingularIntegral N ℓ R n U W-goldbachUnsmoothedSingularIntegral N ℓ n U W‖+
        ‖goldbachUnsmoothedSingularIntegral N ℓ n U W-goldbachSingularIntegral ψ N ℓ R n U W‖ := norm_add_le _ _
    _≤4*goldbachEuclideanDecayConstant*(N:ℝ)/Real.sqrt R+K*(N:ℝ)/Real.sqrt R := by
      rw [norm_sub_rev (goldbachUnsmoothedSingularIntegral N ℓ n U W)]
      exact add_le_add hHard hSoft
    _=_ := by ring

end PrimeSquares
