import PrimeSquares.FiniteStrongMaximalNorm
import PrimeSquares.FiniteInputMaximalExtension
import PrimeSquares.FiniteSquareOperators

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal lp
namespace PrimeSquares

noncomputable def positiveAverageL2 (A : PositiveAverageFamily) (n : ℕ) : ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ) :=
  ∑ j ∈ A.indices n, (A.weight n j : ℂ) • integerTranslate (P := 2) (by norm_num) (A.shift j)

theorem positiveAverageL2_apply (A : PositiveAverageFamily) (n : ℕ) (f : ℓ²(ℤ,ℂ)) (x : ℤ) :
    positiveAverageL2 A n f x = positiveAverage A n (f : ℤ → ℂ) x := by
  simp only [positiveAverageL2, positiveAverage, _root_.smul_apply, _root_.sum_apply,
    lp.coeFn_smul, lp.coeFn_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, integerTranslate_apply]

set_option maxHeartbeats 800000 in
theorem positiveAverage_finite_strong_extension (A : PositiveAverageFamily) {p B : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hB : 0 ≤ B)
    (H : ∀ (F : Finset ℤ) (f : ℤ → ℂ), (∀ x, x ∉ F → f x = 0) →
      MemLp (positiveMaximal A f) (ENNReal.ofReal p) Measure.count ∧
      eLpNorm (positiveMaximal A f) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal B*eLpNorm f (ENNReal.ofReal p) Measure.count)
    (f : ℓ^(ENNReal.ofReal p)(ℤ,ℂ)) :
    ∃ g : ℓ^(ENNReal.ofReal p)(ℤ,ℝ), (g : ℤ → ℝ) = positiveMaximal A (f : ℤ → ℂ) ∧
      ‖g‖ ≤ B*‖f‖ := by
  have hp0 : 0 < p := by linarith
  have hP : 0 < (ENNReal.ofReal p).toReal := by simpa only [ENNReal.toReal_ofReal hp0.le] using hp0
  have hP0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hP2 : ENNReal.ofReal p ≤ 2 := by exact_mod_cast hp2
  have hfinite : FiniteInputLpMaximalBound (positiveAverageL2 A) (ENNReal.ofReal p) B := by
    intro F a
    let v := (finiteInputLp F a 2 : ℤ → ℂ)
    have hv : ∀ x, x ∉ F → v x = 0 := by
      intro x hx
      simp only [v, finiteInputLp_apply, ite_eq_right hx]
    obtain ⟨hm, hn⟩ := H F v hv
    refine ⟨positiveMaximal A v, ?_, hm, ?_, hn⟩
    · exact positiveMaximal_nonneg A (by positivity : 0 ≤ ‖finiteInputLp F a 2‖)
        (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (finiteInputLp F a 2))
    · intro n x
      rw [positiveAverageL2_apply]
      exact positiveMaximal_dominates A (by positivity : 0 ≤ ‖finiteInputLp F a 2‖)
        (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (finiteInputLp F a 2)) n x
  have hall := finite_input_maximal_extension (positiveAverageL2 A) hP hfinite
  obtain ⟨G, hG0, hGdom, hGn⟩ := allInputLpMaximalBound_integerLp (positiveAverageL2 A) hP hP2 hB hall f
  have hmax : ∀ x, positiveMaximal A (f : ℤ → ℂ) x ≤ G x := by
    intro x
    apply ciSup_le
    intro n
    have h := hGdom n x
    rw [positiveAverageL2_apply] at h
    exact h
  have hmax0 := positiveMaximal_nonneg A (lp.norm_nonneg' f) (lp.norm_apply_le_norm hP0 f)
  have hmem : MemLp (positiveMaximal A (f : ℤ → ℂ)) (ENNReal.ofReal p) Measure.count := by
    apply (count_memLp_of_memℓp hP (lp.memℓp G)).mono' AEStronglyMeasurable.of_discrete
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hmax0 x)]
      exact hmax x)
  let g : ℓ^(ENNReal.ofReal p)(ℤ,ℝ) :=
    ⟨positiveMaximal A (f : ℤ → ℂ), memℓp_of_count_memLp hP hmem⟩
  refine ⟨g, rfl, (lp.norm_mono hP0 ?_).trans hGn⟩
  intro x
  change ‖positiveMaximal A (f : ℤ → ℂ) x‖ ≤ ‖G x‖
  rw [Real.norm_eq_abs, abs_of_nonneg (hmax0 x), Real.norm_eq_abs, abs_of_nonneg (hG0 x)]
  exact hmax x

end PrimeSquares
