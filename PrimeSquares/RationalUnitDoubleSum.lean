import PrimeSquares.RationalDenominatorPartition

open Finset
namespace PrimeSquares

noncomputable def denominatorUnitSum {A : Type*} [AddCommMonoid A] (q : ℕ) (F : ℚ → A) : A :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ u : (ZMod q)ˣ,F (unitRational q u)

theorem denominatorUnitSum_pos {A : Type*} [AddCommMonoid A] (q : ℕ) [NeZero q] (F : ℚ → A) :
    denominatorUnitSum q F=∑ u : (ZMod q)ˣ,F (unitRational q u) := by
  simp only [denominatorUnitSum,dite_eq_right (NeZero.ne q)]

theorem canonicalCenters_sum_units {A : Type*} [AddCommMonoid A] (M : ℕ) (F : ℚ → A) :
    (∑ r ∈ canonicalRationalCenters M,F r)=∑ q ∈ Icc 1 M,denominatorUnitSum q F := by
  rw [canonicalCenters_sum_fibers]
  apply sum_congr rfl
  intro q hq
  have : NeZero q := ⟨by have h := (mem_Icc.mp hq).1;omega⟩
  rw [denominatorUnitSum_pos,canonicalDenominatorFiber_sum]

end PrimeSquares
