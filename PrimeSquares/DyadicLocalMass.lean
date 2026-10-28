import PrimeSquares.DecayProfile
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset
namespace PrimeSquares

noncomputable def dyadicBallMass (H : ℝ) (F : Finset ℤ) (f : ℤ → ℝ) (x : ℤ) (j : ℕ) : ℝ :=
  ((2 : ℝ)^j*H)⁻¹*∑ y ∈ F.filter (fun y => |((x-y : ℤ) : ℝ)| ≤ (2 : ℝ)^j*H), f y

noncomputable def dyadicLocalMass (H : ℝ) (F : Finset ℤ) (f : ℤ → ℝ) (x : ℤ) : ℝ :=
  ⨆ j : ℕ, dyadicBallMass H F f x j

theorem dyadicBallMass_nonneg {H : ℝ} (hH : 0 < H) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ y ∈ F, 0 ≤ f y) (x : ℤ) (j : ℕ) : 0 ≤ dyadicBallMass H F f x j := by
  unfold dyadicBallMass
  apply mul_nonneg (by positivity)
  exact sum_nonneg (fun y hy => hf y (mem_filter.mp hy).1)

theorem dyadicBallMass_uniform {H : ℝ} (hH : 0 < H) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ y ∈ F, 0 ≤ f y) (x : ℤ) (j : ℕ) :
    dyadicBallMass H F f x j ≤ H⁻¹*∑ y ∈ F, f y := by
  have hp : 1 ≤ (2 : ℝ)^j := one_le_pow₀ (by norm_num)
  have hden : H ≤ (2 : ℝ)^j*H := by nlinarith
  have hi : ((2 : ℝ)^j*H)⁻¹ ≤ H⁻¹ := inv_anti₀ hH hden
  have hs : (∑ y ∈ F.filter (fun y => |((x-y : ℤ) : ℝ)| ≤ (2 : ℝ)^j*H),f y) ≤ ∑ y ∈ F,f y :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun y hy _ => hf y hy)
  exact mul_le_mul hi hs (sum_nonneg (fun y hy => hf y (mem_filter.mp hy).1)) (by positivity)

theorem dyadicLocalMass_bddAbove {H : ℝ} (hH : 0 < H) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ y ∈ F, 0 ≤ f y) (x : ℤ) : BddAbove (Set.range (dyadicBallMass H F f x)) :=
  ⟨H⁻¹*∑ y ∈ F,f y,by rintro _ ⟨j,rfl⟩;exact dyadicBallMass_uniform hH F f hf x j⟩

end PrimeSquares
