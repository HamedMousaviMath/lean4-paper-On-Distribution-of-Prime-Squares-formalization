import PrimeSquares.SourceCircleBlockPrefix
namespace PrimeSquares
theorem conductor_multiple_prefix {q₀ : ℕ} (hq₀ : 0 < q₀) (d : ℕ) (R : ℝ) :
    ((q₀*d : ℕ) : ℝ) ≤ R ↔ (d : ℝ) ≤ R/(q₀ : ℝ) := by
  rw [Nat.cast_mul,mul_comm]
  exact (le_div_iff₀ (by exact_mod_cast hq₀ : (0 : ℝ) < q₀)).symm
end PrimeSquares
