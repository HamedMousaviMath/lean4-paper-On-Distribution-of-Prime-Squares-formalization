import PrimeSquares.UnitFiberBijection

open Finset
namespace PrimeSquares

noncomputable def unitFiberEquiv (q : ℕ) [NeZero q] :
    (ZMod q)ˣ ≃ {r : ℚ // r ∈ canonicalDenominatorFiber q} :=
  Equiv.ofBijective (unitFiberMap q) (unitFiberMap_bijective q)

theorem canonicalDenominatorFiber_sum {A : Type*} [AddCommMonoid A]
    (q : ℕ) [NeZero q] (F : ℚ → A) :
    (∑ r ∈ canonicalDenominatorFiber q,F r)=∑ u : (ZMod q)ˣ,F (unitRational q u) := by
  classical
  rw [←sum_coe_sort]
  exact (Equiv.sum_comp (unitFiberEquiv q) (fun r => F r.val)).symm

end PrimeSquares
