import PrimeSquares.GoldbachDisjointArcBessel

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

noncomputable def goldbachMajorEnvelope (N : ℕ) (γ : ℝ) : ℝ :=
  if γ=0 then (N:ℝ)^3/(Real.log 2)^2 else
    min ((N:ℝ)^3/(Real.log 2)^2) (goldbachEuclideanDecayConstant*|γ|^(-(3/2:ℝ)))

theorem goldbach_major_envelope_nonnegative (N : ℕ) (γ : ℝ) : 0≤goldbachMajorEnvelope N γ := by
  have := goldbachEuclideanDecayConstant_pos
  unfold goldbachMajorEnvelope
  split_ifs <;> positivity

theorem goldbach_major_envelope_bound (N : ℕ) (γ : ℝ) :
    goldbachMajorEnvelope N γ≤(N:ℝ)^3/(Real.log 2)^2 := by
  unfold goldbachMajorEnvelope
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem goldbach_major_envelope_decay (N : ℕ) {γ : ℝ} (hγ : γ≠0) :
    goldbachMajorEnvelope N γ≤goldbachEuclideanDecayConstant*|γ|^(-(3/2:ℝ)) := by
  rw [goldbachMajorEnvelope,ite_eq_right hγ]
  exact min_le_right _ _

theorem goldbach_major_envelope_measurable (N : ℕ) : Measurable (goldbachMajorEnvelope N) := by
  unfold goldbachMajorEnvelope
  apply Measurable.ite (measurableSet_singleton (0:ℝ)) measurable_const
  exact measurable_const.min (by fun_prop)

theorem goldbach_major_envelope_integrable (N : ℕ) (hN : 0<N) :
    Integrable (goldbachMajorEnvelope N) ∧ (∫ γ : ℝ,goldbachMajorEnvelope N γ)≤goldbachEuclideanL1Constant*(N:ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  let c := 1/(N:ℝ)^2
  have hc : 0<c := by dsimp [c];positivity
  have hs : Real.sqrt c=1/(N:ℝ) := by
    dsimp [c]
    rw [Real.sqrt_div zero_le_one,Real.sqrt_one,Real.sqrt_sq_eq_abs,abs_of_pos hn]
  have hnorm (γ : ℝ) : ‖(goldbachMajorEnvelope N γ:ℂ)‖=goldbachMajorEnvelope N γ := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (goldbach_major_envelope_nonnegative N γ)]
  have hi := goldbach_two_sided_integrable_decay (fun γ : ℝ=>(goldbachMajorEnvelope N γ:ℂ))
    (Complex.continuous_ofReal.measurable.comp (goldbach_major_envelope_measurable N)).stronglyMeasurable
    hc goldbachEuclideanDecayConstant_pos.le
    (fun γ _=>by rw [hnorm];exact goldbach_major_envelope_bound N γ)
    (fun γ hγ=>by rw [hnorm];exact goldbach_major_envelope_decay N (abs_pos.mp (hc.trans hγ)))
  refine ⟨?_,?_⟩
  · simpa only [Complex.reCLM_apply,Complex.ofReal_re] using Complex.reCLM.integrable_comp hi.1
  · simp only [hnorm] at hi
    apply hi.2.trans_eq
    rw [hs]
    dsimp only [c,goldbachEuclideanL1Constant]
    field_simp

theorem goldbach_major_envelope_energy (N : ℕ) (hN : 0<N) :
    Integrable (fun γ : ℝ=>(goldbachMajorEnvelope N γ)^2) ∧
      (∫ γ : ℝ,(goldbachMajorEnvelope N γ)^2)≤
        (goldbachEuclideanL1Constant/(Real.log 2)^2)*(N:ℝ)^4 := by
  have hi := goldbach_major_envelope_integrable N hN
  have hm : 0≤(N:ℝ)^3/(Real.log 2)^2 := by positivity
  have hb (γ : ℝ) : (goldbachMajorEnvelope N γ)^2≤
      ((N:ℝ)^3/(Real.log 2)^2)*goldbachMajorEnvelope N γ := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (goldbach_major_envelope_bound N γ)
      (goldbach_major_envelope_nonnegative N γ)
  have hpow : Integrable (fun γ : ℝ=>(goldbachMajorEnvelope N γ)^2) :=
    (hi.1.const_mul ((N:ℝ)^3/(Real.log 2)^2)).mono' ((goldbach_major_envelope_measurable N).pow_const 2).aestronglyMeasurable (by
      filter_upwards with γ
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (goldbachMajorEnvelope N γ))] using hb γ)
  refine ⟨hpow,?_⟩
  calc
    _≤∫ γ : ℝ,((N:ℝ)^3/(Real.log 2)^2)*goldbachMajorEnvelope N γ :=
      integral_mono hpow (hi.1.const_mul _) hb
    _≤((N:ℝ)^3/(Real.log 2)^2)*(goldbachEuclideanL1Constant*(N:ℝ)) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hi.2 hm
    _=_ := by ring

theorem goldbach_major_envelope_dominated_energy (N : ℕ) (hN : 0<N)
    (f : ℝ→ℂ) (hf : StronglyMeasurable f) {B : ℝ} (_hB : 0≤B)
    (hbound : ∀ γ : ℝ,‖f γ‖≤B*goldbachMajorEnvelope N γ) :
    Integrable (fun γ : ℝ=>‖f γ‖^2) ∧
      (∫ γ : ℝ,‖f γ‖^2)≤B^2*(goldbachEuclideanL1Constant/(Real.log 2)^2)*(N:ℝ)^4 := by
  have hi := goldbach_major_envelope_energy N hN
  have hb (γ : ℝ) : ‖f γ‖^2≤B^2*(goldbachMajorEnvelope N γ)^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (f γ)) (hbound γ) 2
  have hsq : Integrable (fun γ : ℝ=>‖f γ‖^2) :=
    (hi.1.const_mul (B^2)).mono' (hf.norm.pow 2).aestronglyMeasurable (by
      filter_upwards with γ
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖f γ‖)] using hb γ)
  refine ⟨hsq,?_⟩
  calc
    _≤∫ γ : ℝ,B^2*(goldbachMajorEnvelope N γ)^2 := integral_mono hsq (hi.1.const_mul _) hb
    _≤B^2*((goldbachEuclideanL1Constant/(Real.log 2)^2)*(N:ℝ)^4) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hi.2 (sq_nonneg B)
    _=_ := by ring

theorem goldbach_linear_source_integral_empty (N ℓ : ℕ) (hℓ : 0<ℓ)
    {W : ℝ} (hX : (N:ℝ)^2/ℓ≤2) (γ : ℝ) : goldbachLinearSourceIntegral N ℓ W γ=0 := by
  rw [goldbach_linear_source_integral N ℓ hℓ,goldbachLinearIntegral,
    Set.Ioc_eq_empty_of_le ((min_le_right _ _).trans hX)]
  simp only [Measure.restrict_empty,integral_zero_measure]

theorem goldbach_euclidean_product_envelope (N ℓ : ℕ) (hℓ : 0<ℓ) {U W : ℝ}
    (hU : 2≤U) (hUN : U≤N) (hW : 2≤W) (γ : ℝ) :
    (ℓ:ℝ)*‖goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ‖≤goldbachMajorEnvelope N γ := by
  have hl : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  by_cases hX : 2≤(N:ℝ)^2/ℓ
  · have hb : (ℓ:ℝ)*‖goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ‖≤
        (N:ℝ)^3/(Real.log 2)^2 := by
      apply (mul_le_mul_of_nonneg_left (goldbach_euclidean_product_flat N ℓ hℓ hU hUN hW hX γ) hl.le).trans_eq
      field_simp
    by_cases hγ : γ=0
    · rw [goldbachMajorEnvelope,ite_eq_left hγ]
      exact hb
    · rw [goldbachMajorEnvelope,ite_eq_right hγ]
      apply le_min hb
      apply (mul_le_mul_of_nonneg_left (goldbach_euclidean_product_decay N ℓ hℓ hU hW hX hγ) hl.le).trans_eq
      field_simp
  · rw [goldbach_linear_source_integral_empty N ℓ hℓ (le_of_not_ge hX),mul_zero,norm_zero,mul_zero]
    exact goldbach_major_envelope_nonnegative N γ

end PrimeSquares
