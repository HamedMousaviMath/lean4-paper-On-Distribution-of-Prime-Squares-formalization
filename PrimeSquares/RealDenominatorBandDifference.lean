import PrimeSquares.SourceExceptionalRealPrefix
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem rationalCircle_real_band (Γ : Finset ℚ) (M : ℕ)
    (hΓ : ∀ r ∈ Γ,r.den ≤ M) {Q R : ℝ} (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (F : ℚ → C(PrimeCircle,ℂ)) :
    (∑ r ∈ Γ.filter (fun r => (r.den : ℝ) ≤ R ∧ Q < (r.den : ℝ)),F r)=
      realTruncatedCircleSymbol (M+1) R (rationalCircleDenominatorBlock Γ F)-
      realTruncatedCircleSymbol (M+1) (min Q R) (rationalCircleDenominatorBlock Γ F) := by
  classical
  rw [←rationalCircle_real_prefix Γ M hΓ hR F,
    ←rationalCircle_real_prefix Γ M hΓ (le_min hQ hR) F]
  simp only [sum_filter,le_min_iff]
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro r _
  by_cases hr : (r.den : ℝ) ≤ R <;> by_cases hq : Q < (r.den : ℝ)
  · simp [hr,hq,not_le.mpr hq]
  · simp [hr,hq,le_of_not_gt hq]
  · simp [hr,hq]
  · simp [hr,hq]
end PrimeSquares
