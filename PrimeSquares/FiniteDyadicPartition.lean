import PrimeSquares.DyadicRadiusShells
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset
namespace PrimeSquares

noncomputable def finiteDyadicDepth (H : ℝ) (hH : 0 < H) (F : Finset ℤ) (x : ℤ) : ℕ :=
  F.sup (fun y => dyadicRadiusLevel H hH ((x-y : ℤ) : ℝ))

theorem finiteDyadicDepth_covers (H : ℝ) (hH : 0 < H) (F : Finset ℤ) (x y : ℤ)
    (hy : y ∈ F) : dyadicRadiusLevel H hH ((x-y : ℤ) : ℝ) < finiteDyadicDepth H hH F x+1 := by
  exact Nat.lt_succ_of_le (Finset.le_sup (f := fun y => dyadicRadiusLevel H hH ((x-y : ℤ) : ℝ)) hy)

theorem finite_dyadic_partition (H : ℝ) (hH : 0 < H) (F : Finset ℤ) (x : ℤ) (g : ℤ → ℝ) :
    (∑ j ∈ range (finiteDyadicDepth H hH F x+1),
      ∑ y ∈ F.filter (fun y => dyadicRadiusLevel H hH ((x-y : ℤ) : ℝ)=j),g y)=∑ y ∈ F,g y := by
  classical
  exact sum_fiberwise_of_maps_to
    (fun y hy => mem_range.mpr (finiteDyadicDepth_covers H hH F x y hy)) g

end PrimeSquares
