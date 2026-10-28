import PrimeSquares.DyadicShellProfileMass

open Finset
namespace PrimeSquares

theorem polynomial_profile_local_mass {H : ℝ} (hH : 0 < H) (F : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ y ∈ F, 0 ≤ f y) (x : ℤ) :
    (∑ y ∈ F,decayProfile H 10 ((x-y : ℤ) : ℝ)*f y) ≤ 4*H*dyadicLocalMass H F f x := by
  let J := finiteDyadicDepth H hH F x
  have hL := dyadicLocalMass_nonneg hH F f hf x
  rw [←finite_dyadic_partition H hH F x (fun y => decayProfile H 10 ((x-y : ℤ) : ℝ)*f y)]
  change (∑ j ∈ range (J+1),_) ≤ _
  rw [sum_range_succ']
  have hs : (∑ j ∈ range J,∑ y ∈ F.filter (fun y => dyadicRadiusLevel H hH ((x-y : ℤ) : ℝ)=j+1),decayProfile H 10 ((x-y : ℤ) : ℝ)*f y) ≤
      (2*H*dyadicLocalMass H F f x)*(512/511) := by
    calc
      _ ≤ ∑ j ∈ range J,(2*H*dyadicLocalMass H F f x)*(1/512 : ℝ)^j :=
        sum_le_sum (fun j _ => finite_dyadic_shell_profile hH F f hf x j)
      _ = (2*H*dyadicLocalMass H F f x)*∑ j ∈ range J,(1/512 : ℝ)^j := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (dyadic_ninth_partial_bound J) (by positivity)
  have hc := finite_dyadic_core_profile hH F f hf x 10
  nlinarith [mul_nonneg hH.le hL]

end PrimeSquares
