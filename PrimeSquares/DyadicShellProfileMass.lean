import PrimeSquares.DyadicShellMass
import PrimeSquares.DyadicShellBudget

open Finset
namespace PrimeSquares

theorem finite_dyadic_core_profile {H : ℝ} (hH : 0 < H) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ y ∈ F, 0 ≤ f y) (x : ℤ) (k : ℕ) :
    (∑ y ∈ F.filter (fun y => dyadicRadiusLevel H hH ((x-y : ℤ) : ℝ)=0),
      decayProfile H k ((x-y : ℤ) : ℝ)*f y) ≤ H*dyadicLocalMass H F f x := by
  apply le_trans _ (finite_dyadic_core_mass hH F f hf x)
  apply sum_le_sum
  intro y hy
  exact (mul_le_mul_of_nonneg_right (decayProfile_le_one hH k _) (hf y (mem_filter.mp hy).1)).trans_eq (one_mul _)

theorem finite_dyadic_shell_profile {H : ℝ} (hH : 0 < H) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ y ∈ F, 0 ≤ f y) (x : ℤ) (j : ℕ) :
    (∑ y ∈ F.filter (fun y => dyadicRadiusLevel H hH ((x-y : ℤ) : ℝ)=j+1),
      decayProfile H 10 ((x-y : ℤ) : ℝ)*f y) ≤
        (2*H*dyadicLocalMass H F f x)*(1/512 : ℝ)^j := by
  have hL := dyadicLocalMass_nonneg hH F f hf x
  calc
    _ ≤ ∑ y ∈ F.filter (fun y => dyadicRadiusLevel H hH ((x-y : ℤ) : ℝ)=j+1),
        ((2 : ℝ)^(j*10))⁻¹*f y := by
      apply sum_le_sum
      intro y hy
      obtain ⟨hy,hj⟩ := mem_filter.mp hy
      exact mul_le_mul_of_nonneg_right
        (decayProfile_dyadic_shell hH j 10 (dyadicRadiusLevel_succ_bounds H hH _ j hj).1.le) (hf y hy)
    _ = ((2 : ℝ)^(j*10))⁻¹*∑ y ∈ F.filter (fun y => dyadicRadiusLevel H hH ((x-y : ℤ) : ℝ)=j+1),f y := (mul_sum ..).symm
    _ ≤ ((2 : ℝ)^(j*10))⁻¹*(((2 : ℝ)^(j+1)*H)*dyadicLocalMass H F f x) :=
      mul_le_mul_of_nonneg_left (finite_dyadic_shell_mass hH F f hf x (j+1)) (by positivity)
    _ = _ := by rw [←mul_assoc,←mul_assoc,tenth_order_shell_identity];ring

end PrimeSquares
