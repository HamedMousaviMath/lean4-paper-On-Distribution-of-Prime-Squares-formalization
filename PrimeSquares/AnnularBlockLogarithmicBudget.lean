import PrimeSquares.WeightedAnnularAllStartingScales
import PrimeSquares.CanonicalRationalCenters

open Finset
namespace PrimeSquares

theorem circleFrequencyLogFactor_mono {Δ Γ : Finset ℚ} (h : Δ ⊆ Γ) :
    circleFrequencyLogFactor Δ ≤ circleFrequencyLogFactor Γ := by
  have hl : Real.log ((Δ.card : ℝ)+1) ≤ Real.log ((Γ.card : ℝ)+1) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (card_le_card h) 1)
  have hn : 0 ≤ Real.log ((Δ.card : ℝ)+1) := Real.log_nonneg (by have h := Nat.cast_nonneg (α := ℝ) Δ.card;linarith)
  exact pow_le_pow_left₀ (by linarith) (by linarith) 2

theorem circleFrequencyLogFactor_denominator_budget (Γ : Finset ℚ) (s : ℕ)
    (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1)) :
    circleFrequencyLogFactor Γ ≤ 36*((s : ℝ)+1)^2 := by
  have hsub : Γ ⊆ canonicalRationalCenters ((2 : ℕ)^(s+1)) := by
    intro r hr
    apply (mem_canonicalRationalCenters _ r).mpr
    exact ⟨hc r hr,by exact_mod_cast hd r hr⟩
  have hcard := (card_le_card hsub).trans (canonicalRationalCenters_card _)
  have hp : (1 : ℕ) ≤ (2 : ℕ)^(s+1) := Nat.one_le_pow _ _ (by norm_num)
  have he : 8*((2 : ℕ)^(s+1))^2=(2 : ℕ)^(2*s+5) := by
    rw [show (8 : ℕ)=2^3 by norm_num,←pow_mul,←pow_add]
    congr 1;omega
  have hn : Γ.card+1 ≤ (2 : ℕ)^(2*s+5) := by
    rw [←he]
    nlinarith
  have hl : Real.log ((Γ.card : ℝ)+1) ≤ ((2*(s : ℝ)+5)*Real.log 2) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ)<(Γ.card : ℝ)+1)
      (by exact_mod_cast hn : (Γ.card : ℝ)+1 ≤ (2 : ℝ)^(2*s+5))
    simpa only [Real.log_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using h
  have h2 : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    linarith
  have hlu : Real.log ((Γ.card : ℝ)+1) ≤ 5*((s : ℝ)+1) := by
    have h := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2*(s : ℝ)+5)
    nlinarith
  have hln : 0 ≤ Real.log ((Γ.card : ℝ)+1) := Real.log_nonneg (by have h := Nat.cast_nonneg (α := ℝ) Γ.card;linarith)
  unfold circleFrequencyLogFactor
  nlinarith [show (0 : ℝ) ≤ (s : ℝ) by positivity]

noncomputable def annularTruncationConstant (C : ℝ) : ℝ :=
  3*(8+18*C+annularProjectionErrorL2Constant)

theorem annularTruncationConstant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ annularTruncationConstant C := by
  unfold annularTruncationConstant
  have hE := annularProjectionErrorL2Constant_pos
  positivity

theorem annular_allStarting_budget (Γ : Finset ℚ) (s : ℕ)
    (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) :
    ((s : ℝ)+3)*(A*((3/2 : ℝ)*(2*(s : ℝ)+3)+(1/2)*C*circleFrequencyLogFactor Γ+
      annularProjectionErrorL2Constant)) ≤ annularTruncationConstant C*A*((s : ℝ)+1)^3 := by
  have hE := annularProjectionErrorL2Constant_pos
  have hlog := circleFrequencyLogFactor_denominator_budget Γ s hc hd
  have hs : (0 : ℝ) ≤ s := by positivity
  have hs1 : (1 : ℝ) ≤ ((s : ℝ)+1)^2 := by nlinarith
  have hlin : (3/2 : ℝ)*(2*(s : ℝ)+3) ≤ 8*((s : ℝ)+1)^2 := by nlinarith
  have herr : annularProjectionErrorL2Constant ≤
      annularProjectionErrorL2Constant*((s : ℝ)+1)^2 :=
    le_mul_of_one_le_right (by positivity) hs1
  have hcLog := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ (1/2)*C)
  have hb : (3/2 : ℝ)*(2*(s : ℝ)+3)+(1/2)*C*circleFrequencyLogFactor Γ+
      annularProjectionErrorL2Constant ≤ (8+18*C+annularProjectionErrorL2Constant)*((s : ℝ)+1)^2 := by
    nlinarith only [hlin,herr,hcLog]
  have hb0 : 0 ≤ 8+18*C+annularProjectionErrorL2Constant := by positivity
  calc
    _ ≤ ((s : ℝ)+3)*(A*((8+18*C+annularProjectionErrorL2Constant)*((s : ℝ)+1)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hA) (by positivity)
    _ ≤ (3*((s : ℝ)+1))*(A*((8+18*C+annularProjectionErrorL2Constant)*((s : ℝ)+1)^2)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by unfold annularTruncationConstant;ring

end PrimeSquares
