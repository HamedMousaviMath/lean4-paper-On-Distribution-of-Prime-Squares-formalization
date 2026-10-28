import PrimeSquares.GoldbachPrimeCountingModel

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

noncomputable def goldbachCountingSum (c : ℕ→ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Icc 0 ⌊x⌋₊,c n

/-- Quantitative Abel conversion for actual counts and a differentiable model.
The lower model value is zero and the prime at2 remains in the sum. -/
theorem goldbach_counting_model_error_identity (c : ℕ→ℂ) (hc0 : c 0=0) (hc1 : c 1=0)
    {U : ℝ} (hU : 2≤U) (f f' H H' : ℝ→ℂ)
    (hf : ∀ t,HasDerivAt f (f' t) t) (hf' : Continuous f')
    (hH : ∀ t∈Set.Icc 2 U,HasDerivAt H (H' t) t)
    (hH' : IntervalIntegrable H' volume 2 U) (hH2 : H 2=0) :
    (∑ n∈Icc 0 ⌊U⌋₊,f n*c n)-(∫ t in Set.Ioc 2 U,f t*H' t)=
      f U*(goldbachCountingSum c U-H U)-
        ∫ t in Set.Ioc 2 U,f' t*(goldbachCountingSum c t-H t) := by
  have hd : deriv f=f' := funext (fun t => (hf t).deriv)
  have ha := sum_mul_eq_sub_integral_mul₁ c hc0 hc1 U
    (fun t _ => (hf t).differentiableAt) (by rw [hd];exact hf'.integrableOn_Icc)
  rw [hd] at ha
  have hHc : ContinuousOn H (Set.uIcc 2 U) := by
    rw [Set.uIcc_of_le hU]
    exact fun t ht => (hH t ht).continuousAt.continuousWithinAt
  have hm : IntegrableOn (fun t => f' t*H t) (Set.Ioc 2 U) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hU).mp
      ((hf'.intervalIntegrable 2 U).mul_continuousOn hHc)
  have hc : IntegrableOn (fun t => f' t*goldbachCountingSum c t) (Set.Ioc 2 U) :=
    (integrableOn_mul_sum_Icc c (m:=0) (b:=U) (by norm_num : (0:ℝ)≤2)
      hf'.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t _ => hf t)
    (fun t ht => hH t (by simpa only [Set.uIcc_of_le hU] using ht))
    (hf'.intervalIntegrable 2 U) hH'
  rw [intervalIntegral.integral_of_le hU,intervalIntegral.integral_of_le hU,hH2,mul_zero,sub_zero] at hi
  have he : (∫ t in Set.Ioc 2 U,f' t*(goldbachCountingSum c t-H t))=
      (∫ t in Set.Ioc 2 U,f' t*goldbachCountingSum c t)-
        ∫ t in Set.Ioc 2 U,f' t*H t := by
    simp_rw [mul_sub]
    exact integral_sub hc hm
  rw [ha,hi,he]
  unfold goldbachCountingSum
  ring

theorem goldbach_counting_partial_error_bound {U B D : ℝ}
    (hU : 2≤U) (hB : 0≤B) (hD : 0≤D) (f f' E : ℝ→ℂ)
    (hf : ‖f U‖≤1) (hf' : ∀ t∈Set.Icc 2 U,‖f' t‖≤D)
    (hE : ∀ t∈Set.Icc 2 U,‖E t‖≤B) :
    ‖f U*E U-(∫ t in Set.Ioc 2 U,f' t*E t)‖≤B*(1+D*(U-2)) := by
  have hi : ‖∫ t in Set.Ioc 2 U,f' t*E t‖≤D*B*(U-2) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=2) (b:=U) (f:=fun t => f' t*E t) (C:=D*B) (fun t ht => by
        have ht' : t∈Set.Ioc 2 U := by simpa only [Set.uIoc_of_le hU] using ht
        rw [norm_mul]
        exact mul_le_mul (hf' t ⟨ht'.1.le,ht'.2⟩) (hE t ⟨ht'.1.le,ht'.2⟩)
          (norm_nonneg _) hD)
    simpa only [intervalIntegral.integral_of_le hU,abs_of_nonneg (sub_nonneg.mpr hU)] using hh
  have hb : ‖f U*E U‖≤B := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hE U ⟨hU,le_rfl⟩) (norm_nonneg _)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hf hB)
  calc
    _≤‖f U*E U‖+‖∫ t in Set.Ioc 2 U,f' t*E t‖ := norm_sub_le _ _
    _≤B+D*B*(U-2) := add_le_add hb hi
    _=B*(1+D*(U-2)) := by ring

theorem goldbach_prime_weighted_count_sum (k a : ℕ) (U : ℝ) (f : ℝ→ℂ) :
    (∑ n∈goldbachPrimeProgressionCutoff k a U,f n)=
      ∑ n∈Icc 0 ⌊U⌋₊,f n*goldbachPrimeProgressionCoeff k a n := by
  classical
  simp only [goldbachPrimeProgressionCutoff,goldbachPrimeCutoff,filter_filter,sum_filter,
    Nat.range_succ_eq_Icc_zero,goldbachPrimeProgressionCoeff]
  apply sum_congr rfl
  intro n _
  by_cases h : n.Prime ∧ n%k=a%k <;> simp [h]

theorem goldbach_prime_progression_partial_error (k a : ℕ) {U B D : ℝ}
    (hU : 2≤U) (hB : 0≤B) (hD : 0≤D) (f f' : ℝ→ℂ)
    (hf : ∀ t,HasDerivAt f (f' t) t) (hf' : Continuous f')
    (hnorm : ‖f U‖≤1) (hderiv : ∀ t∈Set.Icc 2 U,‖f' t‖≤D)
    (herr : ∀ t∈Set.Icc 2 U,
      ‖(goldbachPrimeProgressionCount k a t:ℂ)-goldbachPrimeProgressionModel k t‖≤B) :
    ‖(∑ n∈goldbachPrimeProgressionCutoff k a U,f n)-
      (∫ t in Set.Ioc 2 U,f t*goldbachPrimeProgressionDensity k t)‖≤B*(1+D*(U-2)) := by
  rw [goldbach_prime_weighted_count_sum,
    goldbach_counting_model_error_identity (goldbachPrimeProgressionCoeff k a)
      (goldbachPrimeProgressionCoeff_zero k a) (goldbachPrimeProgressionCoeff_one k a)
      hU f f' (goldbachPrimeProgressionModel k) (goldbachPrimeProgressionDensity k)
      hf hf' (fun t ht => goldbachPrimeProgressionModel_hasDerivAt k ht.1)
      ((goldbachPrimeProgressionDensity_continuousOn k).mono (by
        rw [Set.uIcc_of_le hU];exact Set.Icc_subset_Ici_self)).intervalIntegrable
      (goldbachPrimeProgressionModel_two k)]
  apply goldbach_counting_partial_error_bound hU hB hD f f' _ hnorm hderiv
  intro t ht
  simpa only [goldbachCountingSum,←goldbach_prime_progression_count_sum] using herr t ht

end PrimeSquares
