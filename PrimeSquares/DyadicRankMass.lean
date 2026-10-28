import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Dyadic rank intervals and the coefficient mass estimate

Ranks start at zero. Block j consists of ranks 2^j-1 through 2^(j+1)-2.
The mass bound is proved for a nonnegative decreasing sequence extended by
zero beyond a finite cutoff. A later module constructs this sequence and
the actual blocks for each finite complex input.
-/

open Finset

namespace PrimeSquares

def dyadicRankStart (j : ℕ) : ℕ := 2^j - 1

def dyadicRankInterval (j : ℕ) : Finset ℕ := Ico (dyadicRankStart j) (dyadicRankStart (j+1))

theorem dyadicRankStart_zero : dyadicRankStart 0 = 0 := by norm_num [dyadicRankStart]

theorem dyadicRankStart_succ (j : ℕ) : dyadicRankStart (j+1) = dyadicRankStart j + 2^j := by
  unfold dyadicRankStart
  rw [pow_succ]
  have h : 1 ≤ (2 : ℕ)^j := one_le_pow₀ (by decide)
  omega

theorem dyadicRankStart_mono : Monotone dyadicRankStart := by
  intro i j hij
  exact Nat.sub_le_sub_right (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hij) 1

theorem dyadicRankInterval_card (j : ℕ) : (dyadicRankInterval j).card = 2^j := by
  simp only [dyadicRankInterval, Nat.card_Ico, dyadicRankStart_succ, Nat.add_sub_cancel_left]

theorem dyadicRankInterval_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (dyadicRankInterval i) (dyadicRankInterval j) := by
  apply disjoint_left.mpr
  intro n hi hj
  have hi' := mem_Ico.mp hi
  have hj' := mem_Ico.mp hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h := dyadicRankStart_mono (show i+1 ≤ j by omega)
    omega
  · have h := dyadicRankStart_mono (show j+1 ≤ i by omega)
    omega

theorem dyadicRankInterval_cover (n : ℕ) : n ∈ dyadicRankInterval (Nat.log2 (n+1)) := by
  have hlo := Nat.log2_self_le (by omega : n+1 ≠ 0)
  have hhi := Nat.lt_log2_self (n := n+1)
  have hpow : 1 ≤ (2 : ℕ)^(Nat.log2 (n+1)) := one_le_pow₀ (by decide)
  have hpow' : 1 ≤ (2 : ℕ)^(Nat.log2 (n+1)+1) := one_le_pow₀ (by decide)
  simp only [dyadicRankInterval, mem_Ico, dyadicRankStart]
  omega

theorem dyadicRankInterval_index_le {n L : ℕ} (hn : n < L) : Nat.log2 (n+1) ≤ L :=
  (Nat.log2_le_self (n+1)).trans (by omega)

theorem dyadic_rank_next_mass {m : ℕ → ℝ} {p : ℝ}
    (hm : ∀ n, 0 ≤ m n) (hmono : Antitone m) (hp : 0 < p) (j : ℕ) :
    (2 : ℝ)^(j+1) * (m (dyadicRankStart (j+1)))^p ≤
      2 * ∑ n ∈ dyadicRankInterval j, (m n)^p := by
  have hpoint (n : ℕ) (hn : n ∈ dyadicRankInterval j) :
      (m (dyadicRankStart (j+1)))^p ≤ (m n)^p := by
    have hle : n ≤ dyadicRankStart (j+1) := (mem_Ico.mp hn).2.le
    exact Real.rpow_le_rpow (hm _) (hmono hle) hp.le
  have hmass : (2 : ℝ)^j * (m (dyadicRankStart (j+1)))^p ≤
      ∑ n ∈ dyadicRankInterval j, (m n)^p := by
    calc
      _ = ∑ _ ∈ dyadicRankInterval j, (m (dyadicRankStart (j+1)))^p := by
        simp only [sum_const, nsmul_eq_mul, dyadicRankInterval_card, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ _ := sum_le_sum hpoint
  rw [pow_succ]
  nlinarith

theorem dyadic_rank_mass_prefix {m : ℕ → ℝ} {p : ℝ}
    (hm : ∀ n, 0 ≤ m n) (hmono : Antitone m) (hp : 0 < p) (K : ℕ) :
    (∑ j ∈ range (K+1), (2 : ℝ)^j * (m (dyadicRankStart j))^p) ≤
      (m 0)^p + 2 * ∑ n ∈ range (dyadicRankStart K), (m n)^p := by
  induction K with
  | zero => simp [dyadicRankStart]
  | succ K ih =>
    rw [show K.succ+1 = (K+1)+1 by omega, sum_range_succ]
    have hnext := dyadic_rank_next_mass hm hmono hp K
    have hsplit := sum_range_add_sum_Ico (fun n => (m n)^p)
      (dyadicRankStart_mono (show K ≤ K+1 by omega))
    change (∑ n ∈ range (dyadicRankStart K), (m n)^p) +
      (∑ n ∈ dyadicRankInterval K, (m n)^p) = _ at hsplit
    change _ ≤ (m 0)^p + 2 * ∑ n ∈ range (dyadicRankStart (K+1)), (m n)^p
    linarith

theorem finite_prefix_mass_le {m : ℕ → ℝ} {p : ℝ}
    (hm : ∀ n, 0 ≤ m n) (hp : 0 < p) (L : ℕ) (htail : ∀ n, L ≤ n → m n = 0) (R : ℕ) :
    (∑ n ∈ range R, (m n)^p) ≤ ∑ n ∈ range L, (m n)^p := by
  by_cases hRL : R ≤ L
  · exact sum_le_sum_of_subset_of_nonneg (range_mono hRL)
      (fun n _ _ => Real.rpow_nonneg (hm n) _)
  · have hLR : L ≤ R := le_of_lt (lt_of_not_ge hRL)
    rw [← sum_range_add_sum_Ico (fun n => (m n)^p) hLR]
    have hz : (∑ n ∈ Ico L R, (m n)^p) = 0 := by
      apply sum_eq_zero
      intro n hn
      rw [htail n (mem_Ico.mp hn).1, Real.zero_rpow hp.ne']
    rw [hz, add_zero]

theorem dyadic_rank_coefficient_power {m : ℕ → ℝ} {p : ℝ}
    (hm : ∀ n, 0 ≤ m n) (hp : 0 < p) (j : ℕ) :
    (((2 : ℝ)^j)^(1/p) * m (dyadicRankStart j))^p =
      (2 : ℝ)^j * (m (dyadicRankStart j))^p := by
  rw [Real.mul_rpow (by positivity) (hm _), one_div,
    Real.rpow_inv_rpow (by positivity : (0 : ℝ) ≤ 2^j) hp.ne']

/-- The factor three is uniform in the cutoff, number of blocks and input. -/
theorem dyadic_rank_coefficient_mass {m : ℕ → ℝ} {p : ℝ}
    (hm : ∀ n, 0 ≤ m n) (hmono : Antitone m) (hp : 0 < p)
    (L : ℕ) (htail : ∀ n, L ≤ n → m n = 0) (K : ℕ) :
    (∑ j ∈ range (K+1), (((2 : ℝ)^j)^(1/p) * m (dyadicRankStart j))^p) ≤
      3 * ∑ n ∈ range L, (m n)^p := by
  simp_rw [dyadic_rank_coefficient_power hm hp]
  have hprefix := dyadic_rank_mass_prefix hm hmono hp K
  have hfirst := finite_prefix_mass_le hm hp L htail 1
  simp only [sum_range_one] at hfirst
  have hrest := finite_prefix_mass_le hm hp L htail (dyadicRankStart K)
  linarith

end PrimeSquares
