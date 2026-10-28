import PrimeSquares.ElementaryPrimeProduct
import Mathlib.Data.Nat.Squarefree

open Finset
namespace PrimeSquares

theorem subsetProduct_primeFactors (S t : Finset ℕ) (hS : ∀ p ∈ S,p.Prime) (ht : t ⊆ S) :
    (subsetProduct t).primeFactors=t :=
  Nat.primeFactors_prod (fun p hp => hS p (ht hp))

theorem subsetProduct_dvd_iff (S t : Finset ℕ) (hS : ∀ p ∈ S,p.Prime) (ht : t ⊆ S)
    {n : ℕ} (hn : n ≠ 0) : subsetProduct t ∣ n ↔ t ⊆ n.primeFactors := by
  have h := @Nat.prod_primeFactors_dvd_iff (subsetProduct t) n hn
  rw [subsetProduct_primeFactors S t hS ht] at h
  exact h

end PrimeSquares
