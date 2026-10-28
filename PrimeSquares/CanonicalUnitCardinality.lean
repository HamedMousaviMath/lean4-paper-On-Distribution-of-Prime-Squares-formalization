import PrimeSquares.RationalUnitDoubleSum

open Finset
namespace PrimeSquares

theorem canonicalDenominatorFiber_card (q : ℕ) [NeZero q] :
    (canonicalDenominatorFiber q).card=q.totient := by
  classical
  have h := canonicalDenominatorFiber_sum q (fun _ => (1 : ℕ))
  simpa only [sum_const,smul_eq_mul,mul_one,sum_const,card_univ,ZMod.card_units_eq_totient] using h

theorem canonicalCenters_card_totient (M : ℕ) :
    (canonicalRationalCenters M).card=∑ q ∈ Icc 1 M,q.totient := by
  classical
  have h := canonicalCenters_sum_fibers M (fun _ => (1 : ℕ))
  simp only [sum_const,smul_eq_mul,mul_one] at h
  rw [h]
  apply sum_congr rfl
  intro q hq
  have : NeZero q := ⟨by have h := (mem_Icc.mp hq).1;omega⟩
  exact canonicalDenominatorFiber_card q

end PrimeSquares
