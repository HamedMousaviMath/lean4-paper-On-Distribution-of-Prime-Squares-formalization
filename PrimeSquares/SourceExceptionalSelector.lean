import PrimeSquares.UnitRationalSourceCoordinates

namespace PrimeSquares

noncomputable def sourceExceptionalSelector (q₀ : ℕ) (active : Bool) (r : ℚ) : ℂ :=
  if active=true ∧ q₀ ∣ r.den then 1 else 0

theorem sourceExceptionalSelector_norm (q₀ : ℕ) (active : Bool) (r : ℚ) :
    ‖sourceExceptionalSelector q₀ active r‖ ≤ 1 := by
  classical
  unfold sourceExceptionalSelector
  split_ifs <;> norm_num

theorem sourceExceptionalSelector_inactive (q₀ : ℕ) (r : ℚ) :
    sourceExceptionalSelector q₀ false r=0 := by
  simp only [sourceExceptionalSelector,Bool.false_eq_true,false_and,ite_false]

theorem sourceExceptionalSelector_active (q₀ : ℕ) (r : ℚ) :
    sourceExceptionalSelector q₀ true r=if q₀ ∣ r.den then 1 else 0 := by
  simp only [sourceExceptionalSelector,true_and]

end PrimeSquares
