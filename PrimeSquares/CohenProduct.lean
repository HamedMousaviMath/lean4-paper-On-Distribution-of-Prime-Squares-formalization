import PrimeSquares.RamanujanCRT
import PrimeSquares.TwoAdic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Induction

/-!
# The complete quadratic Cohen identity and uniform bound

Source: `sources/current/Draft5.tex`, Lemma 3.1 (`l:cohenquadratic`).
`quadratic_cohen_identity` proves equation `e:cohenquadratic`, with the same
Legendre-symbol factors and an explicit residue presentation of T_a.
`twoAdicCohenFactor_one` and `twoAdicCohenFactor_small` identify that presentation
with the parity and totient/Ramanujan expressions in `e:Ta`.
`quadratic_cohen_bound` proves the consequence `e:CohenQuadratic` with the
absolute constant 16. No optimal implied constant is claimed.

The proof applies checked CRT multiplicativity to prime factorization,
identifies the odd squarefree indicator with abs(mu), and combines the
checked local factors. The auxiliary `cohenCorrelation` gives the genuine
correlation at every positive modulus; its value at zero is an arbitrary
extension used only for the multiplicative-function interface.
-/


open Finset

namespace PrimeSquares

/-- The genuine integer-input correlation at q>0, extended by zero at q=0. -/
noncomputable def cohenCorrelation (q : ℕ) (n : ℤ) : ℂ :=
  if h : q = 0 then 0 else
    letI : NeZero q := ⟨h⟩
    quadraticRamanujanSum q (n : ZMod q)

/-- The extension agrees with the original exponential-sum definition. -/
theorem cohenCorrelation_eq (q : ℕ) [NeZero q] (n : ℤ) :
    cohenCorrelation q n = quadraticRamanujanSum q (n : ZMod q) := by
  simp [cohenCorrelation, NeZero.ne q]

/-- Multiplicativity, including the harmless zero-modulus extension. -/
theorem cohenCorrelation_mul (m n : ℕ) (h : m.Coprime n) (x : ℤ) :
    cohenCorrelation (m * n) x = cohenCorrelation m x * cohenCorrelation n x := by
  by_cases hm : m = 0
  · simp [hm, cohenCorrelation]
  by_cases hn : n = 0
  · simp [hn, cohenCorrelation]
  have : NeZero m := ⟨hm⟩
  have : NeZero n := ⟨hn⟩
  simp only [cohenCorrelation_eq]
  simpa only [map_intCast] using quadraticRamanujanSum_coprime_mul m n h (x : ZMod (m * n))

/-- Evaluate the correlation on the canonical prime-power factorization. -/
theorem cohenCorrelation_factorization (q : ℕ) (hq : q ≠ 0) (n : ℤ) :
    cohenCorrelation q n = ∏ p ∈ q.primeFactors,
      cohenCorrelation (p ^ q.factorization p) n := by
  have h1 : cohenCorrelation 1 n = 1 := by
    rw [cohenCorrelation_eq, quadraticRamanujanSum_one]
  exact Nat.multiplicative_factorization (fun q => cohenCorrelation q n)
    (fun a b h => cohenCorrelation_mul a b h n) h1 hq

/-- The Legendre factor in Lemma 3.1; nonprime values are unused. -/
noncomputable def oddCohenFactor (p : ℕ) (n : ℤ) : ℂ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    if legendreSym p n = 1 then (p : ℂ) + 1 else 1 - (p : ℂ)
  else 0

/-- The paper's T_a with every residue and sign case written explicitly. -/
noncomputable def twoAdicCohenFactor (a : ℕ) (n : ℤ) : ℂ :=
  if a = 0 then 1
  else if a = 1 then (if (n : ZMod 2) = 1 then 1 else -1)
  else if a = 2 then (if (n : ZMod 4) = 1 then 4 else if (n : ZMod 4) = 3 then -4 else 0)
  else if a = 3 then (if (n : ZMod 8) = 1 then 16 else if (n : ZMod 8) = 5 then -16 else 0)
  else 0

/-- The full local factor for every power of two, including exponent zero. -/
theorem cohenCorrelation_two_pow (a : ℕ) (n : ℤ) :
    cohenCorrelation (2 ^ a) n = twoAdicCohenFactor a n := by
  rcases a with _ | (_ | (_ | (_ | k)))
  · change cohenCorrelation 1 n = twoAdicCohenFactor 0 n
    rw [cohenCorrelation_eq, quadraticRamanujanSum_one]
    rfl
  · change cohenCorrelation 2 n = twoAdicCohenFactor 1 n
    rw [cohenCorrelation_eq, quadraticRamanujanSum_two]
    rfl
  · change cohenCorrelation 4 n = twoAdicCohenFactor 2 n
    rw [cohenCorrelation_eq, quadraticRamanujanSum_four_explicit]
    rfl
  · change cohenCorrelation 8 n = twoAdicCohenFactor 3 n
    rw [cohenCorrelation_eq, quadraticRamanujanSum_eight_explicit]
    rfl
  · change cohenCorrelation (2 ^ (k + 4)) n = twoAdicCohenFactor (k + 4) n
    rw [cohenCorrelation_eq, quadraticRamanujanSum_two_pow_ge_four]
    simp [twoAdicCohenFactor, show k + 4 ≠ 1 by omega,
      show k + 4 ≠ 2 by omega, show k + 4 ≠ 3 by omega]

/-- The parity presentation agrees with (-1)^(n+1), for all integers n. -/
theorem twoAdicCohenFactor_one (n : ℤ) :
    twoAdicCohenFactor 1 n = (-1 : ℂ) ^ (n + 1) := by
  simp [twoAdicCohenFactor, neg_one_zpow_eq_ite, even_add_one,
    ZMod.intCast_eq_one_iff_odd]

/-- At exponents two and three, T_a equals phi(2^a)*c_(2^a)(n-1). -/
theorem twoAdicCohenFactor_small (a : ℕ) (ha : a = 2 ∨ a = 3) (n : ℤ) :
    twoAdicCohenFactor a n =
      (Nat.totient (2 ^ a) : ℂ) * ramanujanSum (2 ^ a) ((n : ZMod (2 ^ a)) - 1) := by
  rcases ha with rfl | rfl
  · rw [← cohenCorrelation_two_pow, cohenCorrelation_eq]
    change quadraticRamanujanSum 4 (n : ZMod 4) =
      (Nat.totient 4 : ℂ) * ramanujanSum 4 ((n : ZMod 4) - 1)
    rw [quadraticRamanujanSum_four, show Nat.totient 4 = 2 by decide]
    norm_num
  · rw [← cohenCorrelation_two_pow, cohenCorrelation_eq]
    change quadraticRamanujanSum 8 (n : ZMod 8) =
      (Nat.totient 8 : ℂ) * ramanujanSum 8 ((n : ZMod 8) - 1)
    rw [quadraticRamanujanSum_eight, show Nat.totient 8 = 4 by decide]
    norm_num

/-- The odd local factor, with higher exponents forced to vanish. -/
theorem cohenCorrelation_odd_prime_pow (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (k : ℕ) (hk : 0 < k) (n : ℤ) :
    cohenCorrelation (p ^ k) n =
      (if k = 1 then (1 : ℂ) else 0) * oddCohenFactor p n := by
  have hp : p.Prime := Fact.out
  by_cases hk1 : k = 1
  · subst k
    simp only [pow_one, cohenCorrelation_eq, quadraticRamanujanSum_odd_prime p hp2]
    simp [oddCohenFactor, hp]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 2 := ⟨k - 2, by omega⟩
    rw [cohenCorrelation_eq, quadraticRamanujanSum_odd_prime_pow p hp2]
    simp only [hk1, ↓reduceIte, zero_mul]

/-- The product of exponent-one indicators is exactly abs(mu(d)). -/
theorem primeFactor_indicator_eq_abs_moebius (d : ℕ) (hd : d ≠ 0) :
    (∏ p ∈ d.primeFactors, if d.factorization p = 1 then (1 : ℂ) else 0) =
      ((|ArithmeticFunction.moebius d| : ℤ) : ℂ) := by
  classical
  by_cases hs : Squarefree d
  · rw [ArithmeticFunction.abs_moebius_eq_one_of_squarefree hs, Int.cast_one]
    apply prod_eq_one
    intro p hp
    have hfp : d.factorization p = 1 := Nat.factorization_eq_one_of_squarefree hs
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
    simp only [hfp, ↓reduceIte]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs, abs_zero, Int.cast_zero]
    have hnot : ¬∀ p, d.factorization p ≤ 1 :=
      fun h => hs (Nat.squarefree_of_factorization_le_one hd h)
    push Not at hnot
    obtain ⟨p, hp⟩ := hnot
    have hmem : p ∈ d.primeFactors := by
      change p ∈ d.factorization.support
      exact Finsupp.mem_support_iff.mpr (by omega)
    exact prod_eq_zero hmem (by simp [show d.factorization p ≠ 1 by omega])

/-- The full Cohen product at every positive odd modulus. -/
theorem cohenCorrelation_odd_modulus (d : ℕ) (hd : d ≠ 0) (hodd : ¬2 ∣ d) (n : ℤ) :
    cohenCorrelation d n = ((|ArithmeticFunction.moebius d| : ℤ) : ℂ) *
      ∏ p ∈ d.primeFactors, oddCohenFactor p n := by
  classical
  rw [cohenCorrelation_factorization d hd]
  calc
    _ = ∏ p ∈ d.primeFactors,
        (if d.factorization p = 1 then (1 : ℂ) else 0) * oddCohenFactor p n := by
      apply prod_congr rfl
      intro p hp
      have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      have hp2 : p ≠ 2 := fun h => hodd (h ▸ Nat.dvd_of_mem_primeFactors hp)
      have hk : 0 < d.factorization p := by
        have hmem : p ∈ d.factorization.support := hp
        exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmem)
      exact cohenCorrelation_odd_prime_pow p hp2 _ hk n
    _ = _ := by rw [prod_mul_distrib, primeFactor_indicator_eq_abs_moebius d hd]

/-- Lemma 3.1: the complete global product formula for every q>0 and n in Z. -/
theorem quadratic_cohen_identity (q : ℕ) (hq : q ≠ 0) (n : ℤ) :
    cohenCorrelation q n =
      ((|ArithmeticFunction.moebius (q / 2 ^ q.factorization 2)| : ℤ) : ℂ) *
      twoAdicCohenFactor (q.factorization 2) n *
      ∏ p ∈ q.primeFactors.filter (fun p => 2 < p), oddCohenFactor p n := by
  classical
  let a := q.factorization 2
  let d := q / 2 ^ a
  have hd : d ≠ 0 := (Nat.ordCompl_pos 2 hq).ne'
  have hodd : ¬2 ∣ d := Nat.not_dvd_ordCompl Nat.prime_two hq
  have hcop : (2 ^ a).Coprime d :=
    (Nat.coprime_ordCompl Nat.prime_two hq).pow_left a
  have hqd : 2 ^ a * d = q := Nat.ordProj_mul_ordCompl_eq_self q 2
  have hpf : d.primeFactors = q.primeFactors.filter (fun p => 2 < p) := by
    have he : d.primeFactors = q.primeFactors.erase 2 := by
      change (q / 2 ^ q.factorization 2).factorization.support =
        q.factorization.support.erase 2
      rw [Nat.factorization_ordCompl, Finsupp.support_erase]
    rw [he]
    ext p
    simp only [mem_erase, mem_filter]
    constructor
    · rintro ⟨hp2, hp⟩
      have hle := (Nat.prime_of_mem_primeFactors hp).two_le
      exact ⟨hp, by omega⟩
    · rintro ⟨hp, hgt⟩
      exact ⟨by omega, hp⟩
  calc
    cohenCorrelation q n = cohenCorrelation (2 ^ a * d) n := by rw [hqd]
    _ = cohenCorrelation (2 ^ a) n * cohenCorrelation d n :=
      cohenCorrelation_mul _ _ hcop n
    _ = _ := by
      rw [cohenCorrelation_two_pow, cohenCorrelation_odd_modulus d hd hodd, hpf]
      ring

/-- Uniform bound for the exceptional local factor at two. -/
theorem norm_twoAdicCohenFactor_le (a : ℕ) (n : ℤ) :
    ‖twoAdicCohenFactor a n‖ ≤ (16 : ℝ) := by
  unfold twoAdicCohenFactor
  split_ifs <;> norm_num

/-- Every odd local factor has norm at most p+1. -/
theorem norm_oddCohenFactor_le (p : ℕ) (n : ℤ) :
    ‖oddCohenFactor p n‖ ≤ (p : ℝ) + 1 := by
  classical
  unfold oddCohenFactor
  split_ifs with hp hχ
  · simpa only [norm_natCast, norm_one] using norm_add_le (p : ℂ) 1
  · calc
      ‖(1 : ℂ) - (p : ℂ)‖ ≤ 1 + (p : ℝ) := by
        simpa only [norm_one, norm_natCast] using norm_sub_le (1 : ℂ) (p : ℂ)
      _ = _ := add_comm _ _
  · simp only [norm_zero]
    positivity

/-- Lemma 3.1: the stated implied-constant bound, with absolute constant 16. -/
theorem quadratic_cohen_bound (q : ℕ) (hq : q ≠ 0) (n : ℤ) :
    ‖cohenCorrelation q n‖ ≤
      16 * ((|ArithmeticFunction.moebius (q / 2 ^ q.factorization 2)| : ℤ) : ℝ) *
      ∏ p ∈ q.primeFactors, ((p : ℝ) + 1) := by
  classical
  let d := q / 2 ^ q.factorization 2
  let s := q.primeFactors.filter (fun p => 2 < p)
  have hμ : ‖((|ArithmeticFunction.moebius d| : ℤ) : ℂ)‖ =
      ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) := by
    rw [Complex.norm_intCast, abs_of_nonneg (Int.cast_nonneg (abs_nonneg _))]
  have hμ0 : 0 ≤ ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) :=
    Int.cast_nonneg (abs_nonneg _)
  have hnorms : (∏ p ∈ s, ‖oddCohenFactor p n‖) ≤ ∏ p ∈ s, ((p : ℝ) + 1) := by
    apply Finset.prod_le_prod₀
    · exact fun p _ => norm_nonneg _
    · exact fun p _ => norm_oddCohenFactor_le p n
  have hsub : (∏ p ∈ s, ((p : ℝ) + 1)) ≤ ∏ p ∈ q.primeFactors, ((p : ℝ) + 1) := by
    apply prod_le_prod_of_subset_of_one_le₀ (filter_subset _ _)
    · exact fun p _ => by positivity
    · exact fun p _ _ => le_add_of_nonneg_left (Nat.cast_nonneg p)
  rw [quadratic_cohen_identity q hq, norm_mul, norm_mul, norm_prod, hμ]
  calc
    _ ≤ ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) * 16 *
        ∏ p ∈ s, ((p : ℝ) + 1) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (norm_twoAdicCohenFactor_le _ n) hμ0
      · exact hnorms
      · exact prod_nonneg (fun p _ => norm_nonneg _)
      · positivity
    _ ≤ 16 * ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) *
        ∏ p ∈ q.primeFactors, ((p : ℝ) + 1) := by
      rw [mul_comm _ (16 : ℝ)]
      exact mul_le_mul_of_nonneg_left hsub (by positivity)

end PrimeSquares
