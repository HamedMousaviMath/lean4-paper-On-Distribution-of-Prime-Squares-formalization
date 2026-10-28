import PrimeSquares.CohenLogBound

open Finset
namespace PrimeSquares

theorem smoothCohen_summable (Q : ℕ) (hQ : 3 ≤ Q) (x : ℤ) :
    Summable (fun q : ℕ => if ∀ p ∈ q.primeFactors, p < Q then cohenWeight q x else 0) := by
  classical
  apply summable_of_ne_finset_zero (s := (smoothEulerBound Q).divisors)
  intro q hq
  split_ifs with hs
  · by_contra hz
    exact hq (Nat.mem_divisors.mpr
      ⟨cohenWeight_nonzero_dvd_bound Q x hQ q hs hz, pow_ne_zero _ (Nat.factorial_ne_zero _)⟩)
  · rfl

theorem finite_cohen_sum_le_smooth (S : Finset ℕ) (Q : ℕ) (hQ : 3 ≤ Q) (x : ℤ)
    (hS : ∀ q ∈ S, ∀ p ∈ q.primeFactors, p < Q) :
    (∑ q ∈ S, cohenWeight q x) ≤ smoothCohenSeries Q x := by
  classical
  calc
    _ = ∑ q ∈ S, if ∀ p ∈ q.primeFactors, p < Q then cohenWeight q x else 0 := by
      apply sum_congr rfl
      intro q hq
      rw [ite_eq_left (hS q hq)]
    _ ≤ _ := (smoothCohen_summable Q hQ x).sum_le_tsum S (by
      intro q _
      split_ifs
      · exact cohenWeight_nonneg q x
      · exact le_rfl)

theorem truncated_cohen_log_bound (Q : ℕ) (hQ : 2 ≤ Q) (x : ℤ) :
    (∑ q ∈ Icc 1 Q, cohenWeight q x) ≤ (cohenLogConstant/2)*Real.log ((Q : ℝ)+1) := by
  have hQ' : 3 ≤ Q+1 := by omega
  have hs : ∀ q ∈ Icc 1 Q, ∀ p ∈ q.primeFactors, p < Q+1 := by
    intro q hq p hp
    obtain ⟨hqp,hqQ⟩ := mem_Icc.mp hq
    exact (Nat.le_of_dvd (by omega : 0 < q) (Nat.dvd_of_mem_primeFactors hp)).trans_lt
      (by omega : q < Q+1)
  simpa only [Nat.cast_add,Nat.cast_one] using
    (finite_cohen_sum_le_smooth (Icc 1 Q) (Q+1) hQ' x hs).trans
      (low_ramanujan_bound_integer (Q+1) hQ' x)

end PrimeSquares
