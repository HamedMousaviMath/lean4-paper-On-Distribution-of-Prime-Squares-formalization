import PrimeSquares.CanonicalFiberTruncation

open Finset
namespace PrimeSquares

theorem canonicalCenters_sum_fibers {A : Type*} [AddCommMonoid A]
    (M : ℕ) (F : ℚ → A) :
    (∑ r ∈ canonicalRationalCenters M,F r)=∑ q ∈ Icc 1 M,∑ r ∈ canonicalDenominatorFiber q,F r := by
  classical
  have h := sum_fiberwise_of_maps_to (g := Rat.den)
    (s := canonicalRationalCenters M) (t := Icc 1 M)
    (fun r hr => mem_Icc.mpr ⟨r.den_pos,(mem_canonicalRationalCenters M r).mp hr |>.2⟩) F
  rw [←h]
  apply sum_congr rfl
  intro q hq
  rw [canonicalCenters_denominator_filter (mem_Icc.mp hq).2]

end PrimeSquares
