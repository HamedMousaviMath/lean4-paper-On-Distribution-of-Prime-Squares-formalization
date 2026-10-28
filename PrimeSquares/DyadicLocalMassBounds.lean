import PrimeSquares.DyadicLocalMass

open Finset
namespace PrimeSquares

theorem dyadicBallMass_le_local {H : ℝ} (hH : 0 < H) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ y ∈ F, 0 ≤ f y) (x : ℤ) (j : ℕ) :
    dyadicBallMass H F f x j ≤ dyadicLocalMass H F f x :=
  le_ciSup (dyadicLocalMass_bddAbove hH F f hf x) j

theorem dyadicLocalMass_nonneg {H : ℝ} (hH : 0 < H) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ y ∈ F, 0 ≤ f y) (x : ℤ) : 0 ≤ dyadicLocalMass H F f x :=
  (dyadicBallMass_nonneg hH F f hf x 0).trans (dyadicBallMass_le_local hH F f hf x 0)

theorem dyadicLocalMass_uniform {H : ℝ} (hH : 0 < H) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ y ∈ F, 0 ≤ f y) (x : ℤ) :
    dyadicLocalMass H F f x ≤ H⁻¹*∑ y ∈ F,f y :=
  ciSup_le (fun j => dyadicBallMass_uniform hH F f hf x j)

theorem dyadic_ball_sum_le_local {H : ℝ} (hH : 0 < H) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ y ∈ F, 0 ≤ f y) (x : ℤ) (j : ℕ) :
    (∑ y ∈ F.filter (fun y => |((x-y : ℤ) : ℝ)| ≤ (2 : ℝ)^j*H),f y) ≤
      ((2 : ℝ)^j*H)*dyadicLocalMass H F f x := by
  have h := mul_le_mul_of_nonneg_left (dyadicBallMass_le_local hH F f hf x j)
    (by positivity : (0 : ℝ) ≤ (2 : ℝ)^j*H)
  have hz : (2 : ℝ)^j*H ≠ 0 := by positivity
  simpa only [dyadicBallMass,←mul_assoc,mul_inv_cancel₀ hz,one_mul] using h

end PrimeSquares
