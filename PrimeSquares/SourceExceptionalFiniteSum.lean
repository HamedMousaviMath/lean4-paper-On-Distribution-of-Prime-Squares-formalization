import PrimeSquares.ExceptionalUnitCutoffFilter

open Finset
namespace PrimeSquares

theorem canonicalExceptionalSum (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) {Q : ℝ} (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (M : ℕ) :
    (∑ r ∈ canonicalRationalCenters M,if (r.den : ℝ)/(q₀ : ℝ) ≤ Q/conductorMajorant q₀
      then exceptionalRationalCircleLow N hN q₀ χ₀ Q hQ hb β r else 0)=
      realExceptionalLowModel N hN q₀ χ₀ Q hQ hb β M := by
  classical
  rw [canonicalCenters_sum_units]
  calc
    _ = ∑ q ∈ Icc 1 M,if q₀ ∣ q ∧ conductorMajorant q₀*((q/q₀ : ℕ) : ℝ) ≤ Q
        then realExceptionalCircleTerm N hN q₀ χ₀ Q hQ hb β q else 0 := by
      apply sum_congr rfl
      intro q hq
      have : NeZero q := ⟨by have h := (mem_Icc.mp hq).1;omega⟩
      exact exceptionalUnitSum_divisor_filter N hN q₀ χ₀ hQ hb β q
    _ = ∑ q ∈ (Icc 1 M).filter (fun q => q₀ ∣ q ∧ conductorMajorant q₀*((q/q₀ : ℕ) : ℝ) ≤ Q),
        realExceptionalCircleTerm N hN q₀ χ₀ Q hQ hb β q := (sum_filter ..).symm
    _ = _ := conductor_multiple_reindex (NeZero.pos q₀) Q _

theorem canonicalExceptionalSum_active (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) {Q : ℝ} (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (M : ℕ) (active : Bool) :
    (∑ r ∈ canonicalRationalCenters M,if active=true ∧ (r.den : ℝ)/(q₀ : ℝ) ≤ Q/conductorMajorant q₀
      then exceptionalRationalCircleLow N hN q₀ χ₀ Q hQ hb β r else 0)=
      if active=true then realExceptionalLowModel N hN q₀ χ₀ Q hQ hb β M else 0 := by
  classical
  by_cases ha : active=true
  · simpa only [ha,true_and,ite_true] using canonicalExceptionalSum N hN q₀ χ₀ hQ hb β M
  · simp [ha]

end PrimeSquares
