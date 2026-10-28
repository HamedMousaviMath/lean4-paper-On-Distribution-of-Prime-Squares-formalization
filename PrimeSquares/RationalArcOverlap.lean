import PrimeSquares.SourceArcCutoff
import Mathlib.Tactic.IntervalCases

/-!
# Finite overlap count, including the two smallest denominator scales
-/

open Finset

namespace PrimeSquares

theorem rational_small_denominator_list {r : ℚ} (hr : r ∈ Set.Ico (0 : ℚ) 1)
    (hd : r.den < 4) : r ∈ ({0, 1/2, 1/3, 2/3} : Finset ℚ) := by
  have hn0 : (0 : ℤ) ≤ r.num := Rat.num_nonneg.mpr hr.1
  have hdp : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hnq : (r.num : ℚ) < r.den := (div_lt_one hdp).mp (by
    rw [r.num_div_den]
    exact hr.2)
  have hni : r.num < (r.den : ℤ) := by exact_mod_cast hnq
  have hnU : r.num ≤ 2 := by omega
  have hcases : r.den = 1 ∨ r.den = 2 ∨ r.den = 3 := by have := r.den_pos; omega
  rcases hcases with h | h | h
  all_goals
    rw [← r.num_div_den, h]
    interval_cases r.num <;> norm_num [h] at *

noncomputable def activeRationalCenters (Γ : Finset ℚ) (ξ : ℝ) : Finset ℚ := by
  classical
  exact Γ.filter (fun r => sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ)) ≠ 0)

theorem activeRationalCenters_large_card (Γ : Finset ℚ) (ξ : ℝ) {M : ℕ}
    (hM : ∀ r ∈ Γ, r.den ≤ M) :
    ((activeRationalCenters Γ ξ).filter (fun r => 2 ≤ Nat.log2 r.den)).card ≤ Nat.log2 M + 1 := by
  classical
  apply le_trans (card_le_card_of_injOn
    (t := range (Nat.log2 M + 1)) (fun r : ℚ => Nat.log2 r.den) ?_ ?_) (card_range _).le
  · intro r hr
    obtain ⟨har, hlog⟩ := mem_filter.mp hr
    obtain ⟨hrΓ, _⟩ := mem_filter.mp har
    have hden := hM r hrΓ
    have hMp : M ≠ 0 := by have := r.den_pos; omega
    have hl : Nat.log2 r.den ≤ Nat.log2 M :=
      (Nat.le_log2 hMp).mpr ((Nat.log2_self_le r.den_pos.ne').trans hden)
    exact mem_range.mpr (by change Nat.log2 r.den < Nat.log2 M + 1; omega)
  · intro r hr t ht heq
    change Nat.log2 r.den = Nat.log2 t.den at heq
    obtain ⟨har, hlog⟩ := mem_filter.mp hr
    obtain ⟨hat, _⟩ := mem_filter.mp ht
    obtain ⟨_, hξr⟩ := mem_filter.mp har
    obtain ⟨_, hξt⟩ := mem_filter.mp hat
    have hrd : (r.den : ℝ) ≤ (2 : ℝ)^(Nat.log2 r.den+1) := by
      exact_mod_cast (Nat.lt_log2_self (n := r.den)).le
    have htd : (t.den : ℝ) ≤ (2 : ℝ)^(Nat.log2 r.den+1) := by
      rw [heq]
      exact_mod_cast (Nat.lt_log2_self (n := t.den)).le
    rw [← heq] at hξt
    exact sourceArcCutoffScale_unique hlog hrd htd hξr hξt

theorem activeRationalCenters_small_card (Γ : Finset ℚ) (ξ : ℝ)
    (hΓ : ∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1) :
    ((activeRationalCenters Γ ξ).filter (fun r => ¬ 2 ≤ Nat.log2 r.den)).card ≤ 4 := by
  classical
  have hsub : (activeRationalCenters Γ ξ).filter (fun r => ¬ 2 ≤ Nat.log2 r.den) ⊆
      ({0,1/2,1/3,2/3} : Finset ℚ) := by
    intro r hr
    obtain ⟨har, hlog⟩ := mem_filter.mp hr
    obtain ⟨hrΓ, _⟩ := mem_filter.mp har
    have hd : r.den < 4 := by
      by_contra h
      have hp : (2 : ℕ)^2 ≤ r.den := by omega
      exact hlog ((Nat.le_log2 r.den_pos.ne').mpr hp)
    exact rational_small_denominator_list (hΓ r hrΓ) hd
  have hc := card_le_card hsub
  norm_num at hc ⊢
  exact hc

theorem activeRationalCenters_card (Γ : Finset ℚ) (ξ : ℝ) {M : ℕ}
    (hΓ : ∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1) (hM : ∀ r ∈ Γ, r.den ≤ M) :
    (activeRationalCenters Γ ξ).card ≤ Nat.log2 M + 5 := by
  classical
  have hlarge := activeRationalCenters_large_card Γ ξ hM
  have hsmall := activeRationalCenters_small_card Γ ξ hΓ
  have he := card_filter_add_card_filter_not (s := activeRationalCenters Γ ξ)
    (fun r => 2 ≤ Nat.log2 r.den)
  omega

theorem log2_floor_le_real_log {R : ℝ} (hR : 1 ≤ R) :
    (Nat.log2 ⌊R⌋₊ : ℝ) ≤ Real.log R / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hz : ⌊R⌋₊ = 0
  · simp only [hz, Nat.log2_zero, Nat.cast_zero]
    exact div_nonneg (Real.log_nonneg hR) hlog2.le
  · have hp : (2 : ℝ)^(Nat.log2 ⌊R⌋₊) ≤ R := by
      have hn := Nat.log2_self_le hz
      have hh : (2 : ℝ)^(Nat.log2 ⌊R⌋₊) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast hn
      exact hh.trans (Nat.floor_le (by linarith : 0 ≤ R))
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ)^(Nat.log2 ⌊R⌋₊)) hp
    rw [Real.log_pow] at hl
    exact (le_div_iff₀ hlog2).mpr hl

theorem activeRationalCenters_real_card (Γ : Finset ℚ) (ξ : ℝ) {R : ℝ}
    (hR : 1 ≤ R) (hΓ : ∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1)
    (hden : ∀ r ∈ Γ, (r.den : ℝ) ≤ R) :
    ((activeRationalCenters Γ ξ).card : ℝ) ≤ 5 + Real.log R / Real.log 2 := by
  have hM : ∀ r ∈ Γ, r.den ≤ ⌊R⌋₊ := by
    intro r hr
    exact Nat.le_floor (hden r hr)
  have hc := activeRationalCenters_card Γ ξ hΓ hM
  have hcr : ((activeRationalCenters Γ ξ).card : ℝ) ≤ (Nat.log2 ⌊R⌋₊ : ℝ)+5 := by
    exact_mod_cast hc
  have hl := log2_floor_le_real_log hR
  linarith

end PrimeSquares
