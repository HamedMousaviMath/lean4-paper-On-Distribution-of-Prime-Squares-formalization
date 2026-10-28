import PrimeSquares.DyadicAnnularSquareTail
import PrimeSquares.AnnularHighFactor

namespace PrimeSquares

theorem dyadic_annular_scale_lower {M : ℕ} (hM : 2 ≤ M) (j : ℕ) : 2 ≤ (2 : ℕ)^j*M := by
  have hh : 1 ≤ (2 : ℕ)^j := one_le_pow₀ (by norm_num)
  exact hM.trans (by simpa only [one_mul] using Nat.mul_le_mul_right M hh)

theorem dyadic_annular_scale_shift (M i j : ℕ) :
    (2 : ℕ)^(i+j)*M=(2 : ℕ)^j*((2 : ℕ)^i*M) := by
  rw [pow_add]
  ring

theorem dyadic_annular_scale_mono {i j M : ℕ} (hij : i ≤ j) :
    (2 : ℕ)^i*M ≤ (2 : ℕ)^j*M :=
  Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by norm_num) hij)

end PrimeSquares
