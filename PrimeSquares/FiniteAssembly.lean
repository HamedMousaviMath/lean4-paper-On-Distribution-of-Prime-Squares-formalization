import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!+# Finite exceptional-set assembly

The finite inequalities at the end of Section 9 of the attached paper.
These results do not assert the circle-method or sieve estimates.
All main terms, counting functions and errors are explicit hypotheses.
-/

namespace PrimeSquares

open Finset

variable {α : Type*}

noncomputable def badSet (s : Finset α) (e₁ e₂ : α → ℝ) (t : ℝ) : Finset α :=
  s.filter (fun n => t < |e₁ n| + |e₂ n|)

theorem abs_sum_sq_le (a b : ℝ) :
    (|a| + |b|) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := sq_nonneg (|a| - |b|)
  nlinarith [sq_abs a, sq_abs b]

theorem badSet_energy_bound (s : Finset α) (e₁ e₂ : α → ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    ((badSet s e₁ e₂ t).card : ℝ) * t ^ 2 ≤
      2 * ∑ n ∈ s, ((e₁ n) ^ 2 + (e₂ n) ^ 2) := by
  classical
  have hpoint (n : α) (hn : n ∈ badSet s e₁ e₂ t) :
      t ^ 2 ≤ 2 * ((e₁ n) ^ 2 + (e₂ n) ^ 2) := by
    have hlarge : t < |e₁ n| + |e₂ n| := (mem_filter.mp hn).2
    have hsq : t ^ 2 ≤ (|e₁ n| + |e₂ n|) ^ 2 := by
      nlinarith [abs_nonneg (e₁ n), abs_nonneg (e₂ n)]
    exact hsq.trans (abs_sum_sq_le (e₁ n) (e₂ n))
  calc
    ((badSet s e₁ e₂ t).card : ℝ) * t ^ 2 =
        ∑ n ∈ badSet s e₁ e₂ t, t ^ 2 := by simp
    _ ≤ ∑ n ∈ badSet s e₁ e₂ t, 2 * ((e₁ n) ^ 2 + (e₂ n) ^ 2) :=
      sum_le_sum hpoint
    _ = 2 * ∑ n ∈ badSet s e₁ e₂ t, ((e₁ n) ^ 2 + (e₂ n) ^ 2) := by
      rw [mul_sum]
    _ ≤ 2 * ∑ n ∈ s, ((e₁ n) ^ 2 + (e₂ n) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum_of_subset_of_nonneg
      · exact filter_subset _ _
      · intro n _ _
        exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem badSet_card_bound (s : Finset α) (e₁ e₂ : α → ℝ)
    (t B₁ B₂ : ℝ) (ht : 0 < t)
    (h₁ : ∑ n ∈ s, (e₁ n) ^ 2 ≤ B₁)
    (h₂ : ∑ n ∈ s, (e₂ n) ^ 2 ≤ B₂) :
    ((badSet s e₁ e₂ t).card : ℝ) ≤ 2 * (B₁ + B₂) / t ^ 2 := by
  have henergy := badSet_energy_bound s e₁ e₂ t (le_of_lt ht)
  rw [sum_add_distrib] at henergy
  apply (le_div_iff₀ (sq_pos_of_pos ht)).2
  nlinarith

theorem count_lower_bound (R M e₁ e₂ u t : ℝ)
    (hmain : 4 * t ≤ M)
    (hcount : M + e₁ - e₂ - u ≤ R)
    (herr : |e₁| + |e₂| ≤ t) (hu : u ≤ t) :
    2 * t ≤ R := by
  have h₁ := neg_abs_le e₁
  have h₂ := le_abs_self e₂
  linarith

/-- Finite, quantitative version of the last exceptional-set argument in Section 9.
The lower bound for the representation count and the two mean-square estimates
are hypotheses, not hidden axioms or proved analytic inputs. -/
theorem zero_count_card_bound
    (s : Finset α) (R : α → ℕ) (M e₁ e₂ u : α → ℝ)
    (t B₁ B₂ : ℝ) (ht : 0 < t)
    (hmain : ∀ n ∈ s, 4 * t ≤ M n)
    (hcount : ∀ n ∈ s, M n + e₁ n - e₂ n - u n ≤ (R n : ℝ))
    (hu : ∀ n ∈ s, u n ≤ t)
    (h₁ : ∑ n ∈ s, (e₁ n) ^ 2 ≤ B₁)
    (h₂ : ∑ n ∈ s, (e₂ n) ^ 2 ≤ B₂) :
    ((s.filter (fun n => R n = 0)).card : ℝ) ≤ 2 * (B₁ + B₂) / t ^ 2 := by
  classical
  have hsub : s.filter (fun n => R n = 0) ⊆ badSet s e₁ e₂ t := by
    intro n hn
    rcases mem_filter.mp hn with ⟨hns, hnzero⟩
    apply mem_filter.mpr
    refine ⟨hns, ?_⟩
    by_contra hlarge
    have herr : |e₁ n| + |e₂ n| ≤ t := le_of_not_gt hlarge
    have hpos := count_lower_bound (R n : ℝ) (M n) (e₁ n) (e₂ n) (u n) t
      (hmain n hns) (hcount n hns) herr (hu n hns)
    rw [hnzero] at hpos
    simp only [Nat.cast_zero] at hpos
    linarith
  have hcard : ((s.filter (fun n => R n = 0)).card : ℝ) ≤
      ((badSet s e₁ e₂ t).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  exact hcard.trans (badSet_card_bound s e₁ e₂ t B₁ B₂ ht h₁ h₂)

end PrimeSquares
