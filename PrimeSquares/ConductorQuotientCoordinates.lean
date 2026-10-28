import PrimeSquares.SourceExceptionalUnitData
import PrimeSquares.RealCutoffFloorBudget

namespace PrimeSquares

theorem conductor_quotient_real {q₀ q : ℕ} (hq₀ : 0 < q₀) (h : q₀ ∣ q) :
    ((q/q₀ : ℕ) : ℝ)=(q : ℝ)/(q₀ : ℝ) := by
  exact Nat.cast_div h (by exact_mod_cast hq₀.ne')

theorem conductor_quotient_positive {q₀ q : ℕ} (hq₀ : 0 < q₀) (hq : 0 < q) (h : q₀ ∣ q) :
    0 < q/q₀ := Nat.div_pos (Nat.le_of_dvd hq h) hq₀

theorem conductor_quotient_cutoff {q₀ q : ℕ} (hq₀ : 0 < q₀) (h : q₀ ∣ q)
    {Q B : ℝ} (hB : 0 < B) :
    (q : ℝ)/(q₀ : ℝ) ≤ Q/B ↔ B*((q/q₀ : ℕ) : ℝ) ≤ Q := by
  rw [←conductor_quotient_real hq₀ h,le_div_iff₀ hB]
  rw [mul_comm]

end PrimeSquares
