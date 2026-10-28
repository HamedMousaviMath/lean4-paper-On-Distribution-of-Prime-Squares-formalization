import PrimeSquares.CorrelationFactorExpansion
import PrimeSquares.PrimeSubsetDivisibility

open Finset
namespace PrimeSquares

theorem conductorCorrelationProduct_global_expansion (S : Finset ℕ) (hS : ∀ p ∈ S,p.Prime)
    {n : ℕ} (hn : n ≠ 0) (hnS : n.primeFactors ⊆ S) :
    conductorCorrelationProduct n=
      ∑ t ∈ S.powerset,if subsetProduct t ∣ n then subsetCorrelationExcess t else 0 := by
  classical
  have hsets : S.powerset.filter (fun t => subsetProduct t ∣ n)=n.primeFactors.powerset := by
    ext t
    simp only [mem_filter,mem_powerset]
    constructor
    · rintro ⟨ht,hd⟩
      exact (subsetProduct_dvd_iff S t hS ht hn).mp hd
    · intro ht
      have htS := ht.trans hnS
      exact ⟨htS,(subsetProduct_dvd_iff S t hS htS hn).mpr ht⟩
  rw [←sum_filter,hsets]
  exact conductorCorrelationProduct_subset_expansion n

theorem primeFactors_le_cutoff {n D : ℕ} (hn : 0 < n) (hnD : n ≤ D) :
    n.primeFactors ⊆ Nat.primesLE D := by
  intro p hp
  exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)).trans hnD,
    Nat.prime_of_mem_primeFactors hp⟩

end PrimeSquares
