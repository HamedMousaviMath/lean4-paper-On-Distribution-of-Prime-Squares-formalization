import PrimeSquares.PrimeSquareAverages
import PrimeSquares.PrimeFactorEstimates

/-!
# Elementary control of the discarded non-unit terms in Lemma 6.5

Nonzero von Mangoldt weights outside the units modulo q are powers of
primes dividing q. The prime terms have total mass at most log q, while
all higher prime powers have mass at most 2 sqrt(N) log N, by the proved
Chebyshev psi-minus-theta inequality. No PNT input is assumed.
-/

open Finset

namespace PrimeSquares

theorem mangoldt_nonunit_prime_power {n q : ℕ}
    (hΛ : ArithmeticFunction.vonMangoldt n ≠ 0) (hcop : ¬n.Coprime q) :
    ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ p ∣ q ∧ p^k = n := by
  obtain ⟨p, k, hp, hk, he⟩ :=
    (isPrimePow_nat_iff n).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
  refine ⟨p, k, hp, hk, ?_, he⟩
  by_contra hd
  exact hcop (he ▸ (hp.coprime_iff_not_dvd.mpr hd).pow_left k)

theorem mangoldt_prime_nonunit_mass_le_log (S : Finset ℕ) {q : ℕ} (hq : 0 < q) :
    (∑ n ∈ S with n.Prime ∧ ¬n.Coprime q, ArithmeticFunction.vonMangoldt n) ≤
      Real.log q := by
  classical
  have hsub : S.filter (fun n => n.Prime ∧ ¬n.Coprime q) ⊆ q.primeFactors := by
    intro n hn
    obtain ⟨_, hp, hc⟩ := mem_filter.mp hn
    have hd : n ∣ q := by
      by_contra hnd
      exact hc (hp.coprime_iff_not_dvd.mpr hnd)
    exact Nat.mem_primeFactors.mpr ⟨hp, hd, hq.ne'⟩
  calc
    _ = ∑ n ∈ S with n.Prime ∧ ¬n.Coprime q, Real.log n := by
      apply sum_congr rfl
      intro n hn
      exact ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hn).2.1
    _ ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
        Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))
    _ ≤ _ := primeFactors_log_budget q hq

theorem mangoldt_nonprime_mass_bound {N : ℕ} (hN : 1 ≤ N)
    (S : Finset ℕ) (hS : S ⊆ Ioc 0 N) :
    (∑ n ∈ S with ¬n.Prime, ArithmeticFunction.vonMangoldt n) ≤
      2 * Real.sqrt N * Real.log N := by
  have hsub : S.filter (fun n => ¬n.Prime) ⊆ (Ioc 0 N).filter (fun n => ¬n.Prime) :=
    filter_subset_filter (fun n => ¬n.Prime) hS
  calc
    _ ≤ ∑ n ∈ Ioc 0 N with ¬n.Prime, ArithmeticFunction.vonMangoldt n :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Chebyshev.psi N - Chebyshev.theta N := by
      simp only [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hN)

noncomputable def mangoldtNonunitMass (S : Finset ℕ) (q : ℕ) : ℝ :=
  ∑ n ∈ S with ¬n.Coprime q, ArithmeticFunction.vonMangoldt n

theorem mangoldtNonunitMass_nonneg (S : Finset ℕ) (q : ℕ) :
    0 ≤ mangoldtNonunitMass S q :=
  sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)

theorem mangoldtNonunitMass_le {N q : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    (S : Finset ℕ) (hS : S ⊆ Ioc 0 N) :
    mangoldtNonunitMass S q ≤ Real.log q + 2 * Real.sqrt N * Real.log N := by
  classical
  let T := S.filter (fun n => ¬n.Coprime q)
  have hp : (∑ n ∈ T with n.Prime, ArithmeticFunction.vonMangoldt n) ≤ Real.log q := by
    have he : T.filter Nat.Prime = S.filter (fun n => n.Prime ∧ ¬n.Coprime q) := by
      ext n
      simp only [T, mem_filter]
      tauto
    rw [he]
    exact mangoldt_prime_nonunit_mass_le_log S hq
  have hn := mangoldt_nonprime_mass_bound hN T
    ((filter_subset (fun n => ¬n.Coprime q) S).trans hS)
  change (∑ n ∈ T, ArithmeticFunction.vonMangoldt n) ≤ _
  rw [← sum_filter_add_sum_filter_not T Nat.Prime]
  exact add_le_add hp hn

theorem mangoldtNonunitMass_one (S : Finset ℕ) : mangoldtNonunitMass S 1 = 0 := by
  simp [mangoldtNonunitMass]

end PrimeSquares
