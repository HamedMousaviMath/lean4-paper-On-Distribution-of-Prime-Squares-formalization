import PrimeSquares.GoldbachSmallSmoothing

set_option autoImplicit false
open Finset MeasureTheory Metric
open scoped ENNReal
namespace PrimeSquares

theorem goldbach_arc_model_zero_off_major (N : ℕ) {R : ℝ} (hR : 0≤R)
    (f : ℚ→ℝ→ℂ) (θ : PrimeCircle) (hθ : θ∉GoldbachMajorArcs N R) :
    goldbachArcModel N R f θ=0 := by
  classical
  apply sum_eq_zero
  intro r hr
  apply Set.indicator_of_notMem
  intro hh
  exact hθ ((mem_goldbachMajorArcs N hR θ).mpr ⟨r,hr,hh⟩)

theorem goldbach_major_model_product (N : ℕ) (hN : 1≤N) {R : ℝ} (hR : 1≤R)
    (hsep : 2*R^3<(N:ℝ)^2) (I : Finset (ℕ×ℕ)) (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ)
    (U W : ℝ) (θ : PrimeCircle) :
    goldbachSquareMajorModel N R U θ*goldbachWeightedProgressionMajorModel N I a d R W θ=
      goldbachArcModel N R (goldbachMajorFamilyIntegrand N I (fun i=>(a i:ℤ)) d U W) θ := by
  by_cases hθ : θ∈GoldbachMajorArcs N R
  · obtain ⟨r,hr,hb⟩ := (mem_goldbachMajorArcs N (by linarith : 0≤R) θ).mp hθ
    simp only [goldbachSquareMajorModel,goldbachWeightedProgressionMajorModel,goldbachProgressionMajorModel,
      goldbachArcModel_on_arc N hN hR hsep _ r hr θ hb]
    simp only [goldbachMajorFamilyIntegrand,goldbachLinearMajorModel,neg_mul,mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  · rw [goldbachSquareMajorModel,goldbach_arc_model_zero_off_major N (by linarith) _ θ hθ,
      goldbach_arc_model_zero_off_major N (by linarith) _ θ hθ,zero_mul]

theorem goldbach_arc_model_fourier_identity (N : ℕ) {R : ℝ} (hR : 0≤R)
    (hc : R/(N:ℝ)^2<1/2) (f : ℚ→ℝ→ℂ)
    (hf : ∀ r∈sourceRationalCenters R,StronglyMeasurable (f r))
    (B : ℚ→ℝ) (hB : ∀ r∈sourceRationalCenters R,∀ γ,‖f r γ‖≤B r) (n : ℤ) :
    (∫ θ : PrimeCircle in GoldbachMajorArcs N R,goldbachArcModel N R f θ*fourier (-n) θ ∂AddCircle.haarAddCircle)=
      ∑ r∈sourceRationalCenters R,realFourierPhase (-(n:ℝ)*(r:ℝ))*
        (∫ γ : ℝ,goldbachHardCutoff N R γ*f r γ*realFourierPhase (-(n:ℝ)*γ)) := by
  classical
  let F := fun (r : ℚ) (γ : ℝ)=>goldbachHardCutoff N R γ*f r γ
  have hF (r : ℚ) (hr : r∈sourceRationalCenters R) : StronglyMeasurable (F r) :=
    (goldbach_hard_cutoff_measurable N R).stronglyMeasurable.mul (hf r hr)
  have hFB (r : ℚ) (hr : r∈sourceRationalCenters R) (γ : ℝ) : ‖F r γ‖≤B r := by
    change ‖goldbachHardCutoff N R γ*f r γ‖≤B r
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (goldbach_hard_cutoff_norm N R γ) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hB r hr γ)
  have he (θ : PrimeCircle) : goldbachArcModel N R f θ=
      ∑ r∈sourceRationalCenters R,goldbachArcLift r (F r) θ := by
    unfold goldbachArcModel
    apply sum_congr rfl
    intro r _
    simp only [goldbachArcLift,F,goldbachHardCutoff]
    by_cases hh : dist θ ((r:ℝ):PrimeCircle)≤R/(N:ℝ)^2
    · simp [Set.indicator,mem_closedBall,goldbachArcCoordinate_abs,hh]
    · simp [Set.indicator,mem_closedBall,goldbachArcCoordinate_abs,hh]
  have hφ : MemLp ((fourier (-n)) : PrimeCircle→ℂ) ∞ AddCircle.haarAddCircle :=
    ContinuousMap.memLp AddCircle.haarAddCircle ℂ _
  have hi (r : ℚ) (hr : r∈sourceRationalCenters R) :
      Integrable (fun θ : PrimeCircle=>goldbachArcLift r (F r) θ*fourier (-n) θ) AddCircle.haarAddCircle :=
    by
    have hm : MemLp (fun θ : PrimeCircle=>goldbachArcLift r (F r) θ*fourier (-n) θ) 1 AddCircle.haarAddCircle :=
      (goldbach_arc_lift_memLp r (F r) (hF r hr) (hFB r hr) 1).mul hφ
    exact hm.integrable (by norm_num)
  calc
    _=∫ θ : PrimeCircle,goldbachArcModel N R f θ*fourier (-n) θ ∂AddCircle.haarAddCircle :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun θ hθ=>by rw [goldbach_arc_model_zero_off_major N hR f θ hθ,zero_mul])
    _=∑ r∈sourceRationalCenters R,∫ θ : PrimeCircle,goldbachArcLift r (F r) θ*fourier (-n) θ ∂AddCircle.haarAddCircle := by
      simp only [he,sum_mul]
      exact integral_finsetSum _ hi
    _=_ := by
      apply sum_congr rfl
      intro r _
      apply goldbach_arc_lift_fourier_integral
      intro γ hγ
      have hh : ¬|γ|≤R/(N:ℝ)^2 := by linarith
      simp [F,goldbachHardCutoff,hh]

theorem goldbach_hard_radial_kernel_integral (N ℓ : ℕ) (hℓ : 0<ℓ) (R U W : ℝ) (n : ℤ) :
    (∫ γ : ℝ,goldbachRadialProductKernel N ℓ (goldbachHardCutoff N R) U W n γ)=
      goldbachHardSingularIntegral N ℓ R (n:ℝ) U W/(ℓ:ℂ) := by
  have he : goldbachHardSingularIntegral N ℓ R (n:ℝ) U W=
      (ℓ:ℂ)*(∫ γ : ℝ,goldbachRadialProductKernel N ℓ (goldbachHardCutoff N R) U W n γ) := by
    unfold goldbachHardSingularIntegral
    congr 1
    rw [←integral_indicator (measurableSet_le (show Measurable (fun γ : ℝ=>|γ|) by fun_prop) measurable_const)]
    apply integral_congr_ae
    filter_upwards with γ
    by_cases hh : |γ|≤R/(N:ℝ)^2 <;> simp [goldbachRadialProductKernel,goldbachHardCutoff,hh]
  rw [he]
  have hl : (ℓ:ℂ)≠0 := by exact_mod_cast hℓ.ne'
  field_simp

theorem goldbach_hard_major_family_identity (N : ℕ) (hN : 0<N) (I : Finset (ℕ×ℕ))
    (hI : ∀ i∈I,0 < i.1) (b : ℕ×ℕ→ℤ) (d : ℕ×ℕ→ℂ) {U W : ℝ}
    (hU : 2≤U) (hUN : U≤N) (hW : 2≤W) (R : ℝ) (n : ℤ) :
    (∑ r∈sourceRationalCenters R,realFourierPhase (-(n:ℝ)*(r:ℝ))*
      (∫ γ : ℝ,goldbachHardCutoff N R γ*goldbachMajorFamilyIntegrand N I b d U W r γ*realFourierPhase (-(n:ℝ)*γ)))=
      ∑ i∈I,(d i*goldbachHardSingularIntegral N i.1 R (n:ℝ) U W)/((i.1:ℂ)*(i.2.totient:ℂ))*
        (∑ q∈Icc 1 ⌊R⌋₊,generalCoefficient q i.2 (i.1:ℤ) (b i) n) := by
  have hK (i : ℕ×ℕ) (hi : i∈I) : Integrable (goldbachRadialProductKernel N i.1 (goldbachHardCutoff N R) U W n) := by
    have hs : MeasurableSet {γ : ℝ | |γ|≤R/(N:ℝ)^2} :=
      measurableSet_le (show Measurable (fun γ : ℝ=>|γ|) by fun_prop) measurable_const
    have ht := (goldbach_euclidean_product_phase_integrable N i.1 hN (hI i hi) hU hUN hW (n:ℝ)).indicator hs
    convert ht using 1
    funext γ
    by_cases hh : |γ|≤R/(N:ℝ)^2 <;> simp [goldbachRadialProductKernel,goldbachHardCutoff,hh]
  have h := goldbach_radial_major_family_identity N I b d (goldbachHardCutoff N R) U W R (fun _=>1) n hK
  simp only [one_mul] at h
  rw [h]
  apply sum_congr rfl
  intro i hi
  rw [goldbach_hard_radial_kernel_integral N i.1 (hI i hi)]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

noncomputable def goldbachMajorModelCoefficient (N : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (R U W : ℝ) (n : ℤ) : ℂ :=
  ∫ θ : PrimeCircle in GoldbachMajorArcs N R,
    goldbachSquareMajorModel N R U θ*goldbachWeightedProgressionMajorModel N I a d R W θ*
      fourier (-n) θ ∂AddCircle.haarAddCircle

theorem goldbach_actual_major_model_identity (N : ℕ) (hN : 1≤N) (hlog : 1≤Real.log N)
    (L B : ℝ) (V : ℕ→ℝ) (hB : 0≤B) (hL : L≤(N:ℝ)^2)
    (hV : ∀ ℓ : ℕ,0<ℓ →(ℓ:ℝ)<L →V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B))
    (a : ℕ×ℕ→ℕ) (ha : ∀ i∈goldbachCoefficientIndices L V,IsCoprime (i.2:ℤ) (a i:ℤ))
    (d : ℕ×ℕ→ℂ) (hd : ∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1)
    {R U W : ℝ} (hR : 1≤R) (hsep : 2*R^3<(N:ℝ)^2) (hc : R/(N:ℝ)^2<1/2)
    (hU : 2≤U) (hUN : U≤N) (hW : 2≤W) (n : ℤ) :
    goldbachMajorModelCoefficient N (goldbachCoefficientIndices L V) a d R U W n=
      ∑ i∈goldbachCoefficientIndices L V,
        (d i*goldbachHardSingularIntegral N i.1 R (n:ℝ) U W)/((i.1:ℂ)*(i.2.totient:ℂ))*
          (∑ q∈Icc 1 ⌊R⌋₊,generalCoefficient q i.2 (i.1:ℤ) (a i:ℤ) n) := by
  let I := goldbachCoefficientIndices L V
  have hI : ∀ i∈I,0 < i.1 := fun i hi=>((mem_goldbachCoefficientIndices L V i.1 i.2).mp hi).1
  let f := goldbachMajorFamilyIntegrand N I (fun i=>(a i:ℤ)) d U W
  have hf : ∀ r∈sourceRationalCenters R,StronglyMeasurable (f r) :=
    fun r _=>goldbach_major_family_integrand_measurable N I hI (fun i=>(a i:ℤ)) d U W r
  have hb (r : ℚ) (_hr : r∈sourceRationalCenters R) (γ : ℝ) :
      ‖f r γ‖≤goldbachMajorArithmeticPrefactor N r.den*((N:ℝ)^3/(Real.log 2)^2) :=
    (goldbach_major_family_integrand_bound N hN hlog L B V hB hL hV (fun i=>(a i:ℤ)) ha d hd hU hUN hW r γ).trans
      (mul_le_mul_of_nonneg_left (goldbach_major_envelope_bound N γ) (goldbach_major_arithmetic_prefactor_nonnegative N r.den))
  unfold goldbachMajorModelCoefficient
  simp only [goldbach_major_model_product N hN hR hsep]
  rw [goldbach_arc_model_fourier_identity N (by linarith) hc f hf _ hb]
  exact goldbach_hard_major_family_identity N (by omega) I hI (fun i=>(a i:ℤ)) d hU hUN hW R n

end PrimeSquares
