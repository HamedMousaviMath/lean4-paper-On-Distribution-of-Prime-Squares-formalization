import PrimeSquares.GoldbachMajorStrictEndpoint
import PrimeSquares.ProgressionModelError

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

noncomputable def goldbachPrimeProgressionCoeff (k a n : ℕ) : ℂ :=
  if n.Prime ∧ n%k=a%k then 1 else 0

noncomputable def goldbachPrimeProgressionCount (k a : ℕ) (x : ℝ) : ℝ :=
  ((goldbachPrimeProgressionCutoff k a x).card:ℝ)

noncomputable def goldbachLi (x : ℝ) : ℝ :=
  ∫ t in (2:ℝ)..x,(Real.log t)⁻¹

noncomputable def goldbachPrimeProgressionModel (k : ℕ) (x : ℝ) : ℂ :=
  (k.totient:ℂ)⁻¹*(goldbachLi x:ℂ)

noncomputable def goldbachPrimeProgressionDensity (k : ℕ) (x : ℝ) : ℂ :=
  (k.totient:ℂ)⁻¹*((Real.log x)⁻¹:ℝ)

theorem goldbachPrimeProgressionCoeff_zero (k a : ℕ) :
    goldbachPrimeProgressionCoeff k a 0=0 := by
  simp [goldbachPrimeProgressionCoeff,Nat.not_prime_zero]

theorem goldbachPrimeProgressionCoeff_one (k a : ℕ) :
    goldbachPrimeProgressionCoeff k a 1=0 := by
  simp [goldbachPrimeProgressionCoeff,Nat.not_prime_one]

theorem goldbach_prime_progression_count_sum (k a : ℕ) (x : ℝ) :
    (goldbachPrimeProgressionCount k a x:ℂ)=
      ∑ n∈Icc 0 ⌊x⌋₊,goldbachPrimeProgressionCoeff k a n := by
  classical
  simp only [goldbachPrimeProgressionCount,goldbachPrimeProgressionCutoff,
    goldbachPrimeCutoff,filter_filter,card_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero,Nat.range_succ_eq_Icc_zero,goldbachPrimeProgressionCoeff]
  push_cast
  apply sum_congr rfl
  intro n _
  by_cases h : n.Prime ∧ n%k=a%k <;> simp [h]

theorem goldbach_log_density_continuousOn :
    ContinuousOn (fun x : ℝ => (Real.log x)⁻¹) (Set.Ici 2) := by
  intro x hx
  have hx0 : 0<x := by linarith [hx.out]
  have hl0 : 0<Real.log x := Real.log_pos (by linarith [hx.out])
  exact ((Real.continuousAt_log hx0.ne').inv₀ hl0.ne').continuousWithinAt

theorem goldbachLi_hasDerivAt {x : ℝ} (hx : 2≤x) :
    HasDerivAt goldbachLi ((Real.log x)⁻¹) x := by
  have hcont : ContinuousAt (fun t : ℝ => (Real.log t)⁻¹) x :=
    (Real.continuousAt_log (by linarith : x≠0)).inv₀
      (Real.log_pos (by linarith : 1<x)).ne'
  exact intervalIntegral.integral_hasDerivAt_right
    (goldbach_log_density_continuousOn.mono (by
      rw [Set.uIcc_of_le hx]
      exact Set.Icc_subset_Ici_self)).intervalIntegrable
    Real.measurable_log.inv.aestronglyMeasurable.stronglyMeasurableAtFilter hcont

theorem goldbachLi_two : goldbachLi 2=0 := by
  simp [goldbachLi]

theorem goldbachPrimeProgressionModel_two (k : ℕ) :
    goldbachPrimeProgressionModel k 2=0 := by
  simp [goldbachPrimeProgressionModel,goldbachLi_two]

theorem goldbachPrimeProgressionModel_hasDerivAt (k : ℕ) {x : ℝ} (hx : 2≤x) :
    HasDerivAt (goldbachPrimeProgressionModel k) (goldbachPrimeProgressionDensity k x) x :=
  (goldbachLi_hasDerivAt hx).ofReal_comp.const_mul _

theorem goldbachPrimeProgressionDensity_continuousOn (k : ℕ) :
    ContinuousOn (goldbachPrimeProgressionDensity k) (Set.Ici 2) :=
  continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn goldbach_log_density_continuousOn)

end PrimeSquares
