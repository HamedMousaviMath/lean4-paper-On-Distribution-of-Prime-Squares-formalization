import PrimeSquares.FiniteDyadicPartition
import PrimeSquares.DyadicLocalMassBounds

open Finset
namespace PrimeSquares

theorem finite_dyadic_shell_mass {H : ℝ} (hH : 0 < H) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ y ∈ F, 0 ≤ f y) (x : ℤ) (j : ℕ) :
    (∑ y ∈ F.filter (fun y => dyadicRadiusLevel H hH ((x-y : ℤ) : ℝ)=j),f y) ≤
      ((2 : ℝ)^j*H)*dyadicLocalMass H F f x := by
  apply le_trans _ (dyadic_ball_sum_le_local hH F f hf x j)
  apply sum_le_sum_of_subset_of_nonneg
  · intro y hy
    obtain ⟨hy,hj⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨hy,by simpa only [hj] using dyadicRadiusLevel_upper H hH ((x-y : ℤ) : ℝ)⟩
  · intro y hy _
    exact hf y (mem_filter.mp hy).1

theorem finite_dyadic_core_mass {H : ℝ} (hH : 0 < H) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ y ∈ F, 0 ≤ f y) (x : ℤ) :
    (∑ y ∈ F.filter (fun y => dyadicRadiusLevel H hH ((x-y : ℤ) : ℝ)=0),f y) ≤
      H*dyadicLocalMass H F f x := by
  simpa only [pow_zero,one_mul] using finite_dyadic_shell_mass hH F f hf x 0

end PrimeSquares
