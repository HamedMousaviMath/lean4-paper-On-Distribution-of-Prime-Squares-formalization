import PrimeSquares.AnnularBlockLogarithmicBudget
import Mathlib.Data.Nat.Factorial.Basic

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def rationalFrequencyLoss (P : ℕ) (Γ : Finset ℚ) : ℝ :=
  1 + Real.log (1 + Real.log (P : ℝ)) + Real.log ((Γ.card : ℝ) + 1)

theorem rationalFrequencyLoss_nonneg {P : ℕ} (hP : 0 < P) (Γ : Finset ℚ) :
    0 ≤ rationalFrequencyLoss P Γ := by
  have hp : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hl := Real.log_nonneg hp
  have hll := Real.log_nonneg (show 1 ≤ 1 + Real.log (P : ℝ) by linarith)
  have hc := Real.log_nonneg (show 1 ≤ (Γ.card : ℝ) + 1 by have h := Nat.cast_nonneg (α := ℝ) Γ.card; linarith)
  unfold rationalFrequencyLoss
  linarith

theorem rationalFrequencyLoss_subset {P : ℕ} {Δ Γ : Finset ℚ} (h : Δ ⊆ Γ) :
    rationalFrequencyLoss P Δ ≤ rationalFrequencyLoss P Γ := by
  unfold rationalFrequencyLoss
  apply add_le_add le_rfl
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.add_le_add_right (card_le_card h) 1

theorem rationalBand_common_period (s : ℕ) (Γ : Finset ℚ)
    (hd : ∀ r ∈ Γ, (r.den : ℝ) ≤ (2 : ℝ)^(s+1)) :
    0 < ((2 : ℕ)^(s+1)).factorial ∧
      ∀ r ∈ Γ, r.den ∣ ((2 : ℕ)^(s+1)).factorial := by
  refine ⟨Nat.factorial_pos _, ?_⟩
  intro r hr
  exact Nat.dvd_factorial r.den_pos (by exact_mod_cast hd r hr)

theorem rationalBand_log_card (s : ℕ) (Γ : Finset ℚ)
    (hc : ∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ, (r.den : ℝ) ≤ (2 : ℝ)^(s+1)) :
    Real.log ((Γ.card : ℝ) + 1) ≤ 6*((s : ℝ)+1) := by
  have h := circleFrequencyLogFactor_denominator_budget Γ s hc hd
  have hl := Real.log_nonneg (show 1 ≤ (Γ.card : ℝ)+1 by have h := Nat.cast_nonneg (α := ℝ) Γ.card; linarith)
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  unfold circleFrequencyLogFactor at h
  nlinarith

theorem rationalBand_log_period (s : ℕ) :
    Real.log (1 + Real.log (((2 : ℕ)^(s+1)).factorial : ℝ)) ≤ 4*((s : ℝ)+1) := by
  let D : ℕ := (2 : ℕ)^(s+1)
  have hD : 0 < D := by dsimp [D]; positivity
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hp : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hL : Real.log (D.factorial : ℝ) ≤ (D : ℝ)*Real.log (D : ℝ) := by
    have hh := Real.log_le_log hp (show (D.factorial : ℝ) ≤ (D : ℝ)^D by exact_mod_cast Nat.factorial_le_pow D)
    simpa only [Real.log_pow] using hh
  have hld : Real.log (D : ℝ) ≤ D :=
    (Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ)<D)).trans (by linarith)
  have hP : 0 ≤ Real.log (D.factorial : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.factorial_pos D)
  have hlower : 0 < 1+Real.log (D.factorial : ℝ) := by linarith
  have hsq : 1+Real.log (D.factorial : ℝ) ≤ (2*(D : ℝ))^2 := by
    have hh := mul_le_mul_of_nonneg_left hld (show 0 ≤ (D : ℝ) by positivity)
    nlinarith
  have hdlog : Real.log (D : ℝ) = ((s : ℝ)+1)*Real.log 2 := by
    dsimp [D]
    rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_add,Nat.cast_one]
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    linarith
  calc
    _ ≤ Real.log ((2*(D : ℝ))^2) := Real.log_le_log hlower hsq
    _ = 2*(Real.log 2+((s : ℝ)+1)*Real.log 2) := by
      rw [Real.log_pow,Real.log_mul (by norm_num : (2 : ℝ)≠0) (by linarith : (D : ℝ)≠0),hdlog]
      norm_num
    _ ≤ _ := by
      have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      have hh := mul_le_mul_of_nonneg_left htwo (show 0 ≤ (s : ℝ)+1 by positivity)
      nlinarith

theorem rationalBand_loss_linear (s : ℕ) (Γ : Finset ℚ)
    (hc : ∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ, (r.den : ℝ) ≤ (2 : ℝ)^(s+1)) :
    rationalFrequencyLoss ((2 : ℕ)^(s+1)).factorial Γ ≤ 11*((s : ℝ)+1) := by
  have hp := rationalBand_log_period s
  have hn := rationalBand_log_card s Γ hc hd
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  unfold rationalFrequencyLoss
  linarith

end PrimeSquares
