import PrimeSquares.NormalizedStoppingPairing
import PrimeSquares.DyadicHighFactorComparison
import PrimeSquares.SelectedPrimeErrorMaximum
import PrimeSquares.FiniteAnnularMaximum

/-!
# Uniform large-stopping-scale pairing for the actual common operator family

All constants are chosen before the interval, sets, varying scale, Q and
starting threshold. The low, high and error terms use the same selected
Page data and exact decomposition from Proposition 4.19.
-/

open Finset
open scoped lp
namespace PrimeSquares

theorem annularDyadicValue_l2 (j : ℕ) (F : Finset ℤ) (x : ℤ) :
    annularDyadicValue j F x =
      annularWeightedSquareAverage (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
        ((2 : ℕ)^j*2) ArithmeticFunction.vonMangoldt (finiteIndicatorLp F 2) x := by
  simpa only [annularDyadicValue, finiteConvolution_indicator, finiteInputLp_one] using
    annularWeightedSquareAverage_finiteInput (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
      ((2 : ℕ)^j*2) ArithmeticFunction.vonMangoldt F (fun _ => 1) x

theorem annularDyadicValue_selected_decomposition {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (j : ℕ) (Q : ℝ) (F : Finset ℤ) (x : ℤ) :
    annularDyadicValue j F x =
      selectedPrimeLow D ((2 : ℕ)^j*2)
        (by have := dyadic_annular_scale_lower (M := 2) (by norm_num) j; omega) Q (finiteIndicatorLp F 1) x +
      selectedPrimeHigh D ((2 : ℕ)^j*2)
        (by have := dyadic_annular_scale_lower (M := 2) (by norm_num) j; omega) Q (finiteIndicatorLp F 2) x +
      selectedPrimeError D ((2 : ℕ)^j*2)
        (by have := dyadic_annular_scale_lower (M := 2) (by norm_num) j; omega) Q (finiteIndicatorLp F 2) x := by
  have h := selectedPrime_decomposition_l1 D ((2 : ℕ)^j*2)
    (by have := dyadic_annular_scale_lower (M := 2) (by norm_num) j; omega) Q (finiteIndicatorLp F 1) x
  rw [lpInclusion_finiteIndicator] at h
  exact (annularDyadicValue_l2 j F x).trans h

theorem primeLargeStopping_pairing {c δ c₁ : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (H419 : Proposition419Bounds D δ) (hδ : 0 < δ) (hc₁ : 2 < c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : SparseIntegerInterval) (F G H : Finset ℤ) (τ : ℤ → ℕ)
      (k : ℕ) (N₀ : ℝ), G ⊆ H → 2 ≤ (2 : ℝ)^k → 2 ≤ N₀ →
      Real.log ((2 : ℝ)^k) ≤ δ*Real.sqrt (Real.log N₀) →
      (∀ x ∈ G, N₀ ≤ (((2 : ℕ)^(τ x)*2 : ℕ) : ℝ)) →
      (∀ x ∈ G, sourceLocalMass ((2 : ℕ)^(τ x)*2) (finiteIndicatorLp F 1) x ≤
        320*((F.card : ℝ)/I.length)) →
      ‖∑ x ∈ G, annularDyadicValue (τ x) F x‖/(5*(I.length : ℝ)) ≤
        C*localPrimeScalar c₁ (finiteSetDensity (5*(I.length : ℝ)) F H) ((2 : ℝ)^k) := by
  obtain ⟨KH, hKH, _, hHigh⟩ := H419.high (c₁-2) (by linarith)
  obtain ⟨KR, hKR, hReg⟩ := regularizedHighFactor_dyadic c₁
  obtain ⟨KE, hKE, hError⟩ := selectedPrimeError_countable_maximum D H419
  let CL := 25600*lowSpatialConstant
  have hCL : 0 ≤ CL := mul_nonneg (by norm_num) lowSpatialConstant_nonneg
  let C := 1+CL+KH*KR+KE
  have hC : 0 < C := by dsimp [C]; positivity
  have hCLc : CL ≤ C := by dsimp [C]; nlinarith [mul_pos hKH hKR]
  have hKHc : KH*KR ≤ C := by dsimp [C]; linarith
  have hKEc : KE ≤ C := by dsimp [C]; nlinarith [mul_pos hKH hKR]
  refine ⟨C, hC, ?_⟩
  intro I F G H τ k N₀ hGH hQ hN₀ hcut hτ hadm
  let Q := (2 : ℝ)^k
  let L := 5*(I.length : ℝ)
  have hI : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hL : 0 < L := by dsimp [L]; positivity
  have hQ0 : 0 < Q := by dsimp [Q]; positivity
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by dsimp [Q]; linarith)
  have hlog2 : Real.log (2*Q) ≤ 2*Real.log Q := by
    rw [Real.log_mul (by norm_num) hQ0.ne']
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hQ
    linarith
  have hvalid : ∀ x ∈ G, Real.log Q ≤ δ*Real.sqrt
      (Real.log (((2 : ℕ)^(τ x)*2 : ℕ) : ℝ)) := by
    intro x hx
    exact hcut.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (Real.log_le_log (by linarith) (hτ x hx))) hδ.le)
  obtain ⟨Hi, _, _, hHi, hHinorm, _⟩ := hHigh Q N₀ hQ hN₀ hcut (finiteIndicatorLp F 2)
  obtain ⟨Er, hEr, _, hErnorm⟩ := hError Q hQ (finiteIndicatorLp F 2)
  let lo := fun x => selectedPrimeLow D ((2 : ℕ)^(τ x)*2)
    (by have := dyadic_annular_scale_lower (M := 2) (by norm_num) (τ x); omega) Q (finiteIndicatorLp F 1) x
  let hi := fun x => selectedPrimeHigh D ((2 : ℕ)^(τ x)*2)
    (by have := dyadic_annular_scale_lower (M := 2) (by norm_num) (τ x); omega) Q (finiteIndicatorLp F 2) x
  let er := fun x => selectedPrimeError D ((2 : ℕ)^(τ x)*2)
    (by have := dyadic_annular_scale_lower (M := 2) (by norm_num) (τ x); omega) Q (finiteIndicatorLp F 2) x
  have hlo : ∀ x ∈ G, ‖lo x‖ ≤ C/L*Q*Real.log Q*(F.card : ℝ) := by
    intro x hx
    have hN := dyadic_annular_scale_lower (M := 2) (by norm_num) (τ x)
    have hl := H419.low_local _ hN Q hQ (hvalid x hx) (by omega) (finiteIndicatorLp F 1) x
    have hLC := lowSpatialConstant_nonneg
    calc
      _ ≤ (8*lowSpatialConstant*Q*Real.log (2*Q))*(320*((F.card : ℝ)/I.length)) :=
        hl.trans (mul_le_mul_of_nonneg_left (hadm x hx) (by
          have hh := Real.log_nonneg (show (1 : ℝ) ≤ 2*Q by linarith)
          positivity))
      _ ≤ (8*lowSpatialConstant*Q*(2*Real.log Q))*(320*((F.card : ℝ)/I.length)) := by gcongr
      _ = CL/L*Q*Real.log Q*(F.card : ℝ) := by dsimp [CL, L]; field_simp; ring
      _ ≤ _ := by gcongr
  have hhi : ∀ x ∈ G, ‖hi x‖ ≤ Hi x := by
    intro x hx
    have h := hHi (τ x) x
    rw [selectedPrimeHighTail_of_le D N₀ Q (τ x) (hτ x hx)] at h
    exact h
  have her : ∀ x ∈ G, ‖er x‖ ≤ Er x := by
    intro x hx
    have h := hEr (τ x) x
    rw [selectedPrimeValidError_of_valid D (τ x) (hvalid x hx)] at h
    exact h
  have hHn : ‖Hi‖ ≤ C*Q^(-(1/2 : ℝ))*orliczHighFactor c₁ (1/2) Q*Real.sqrt (F.card : ℝ) := by
    rw [finiteIndicatorLp_two_norm, show (2 : ℝ)+(c₁-2)=c₁ by ring] at hHinorm
    calc
      _ ≤ (KH*Q^(-(1/2 : ℝ))*Real.exp (c₁*regularizedHighExponentWeight Q))*Real.sqrt (F.card : ℝ) := hHinorm
      _ ≤ (KH*Q^(-(1/2 : ℝ))*(KR*orliczHighFactor c₁ (1/2) Q))*Real.sqrt (F.card : ℝ) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hReg k) (by positivity))
          (Real.sqrt_nonneg _)
      _ = (KH*KR)*Q^(-(1/2 : ℝ))*orliczHighFactor c₁ (1/2) Q*Real.sqrt (F.card : ℝ) := by ring
      _ ≤ _ := by
        have hp := (Real.exp_pos (c₁*(Real.log Q)^(1/2 : ℝ)/Real.log (Real.log Q))).le
        gcongr
  have hEn : ‖Er‖ ≤ C*Q^(-(1/2 : ℝ))*Real.sqrt (F.card : ℝ) := by
    rw [finiteIndicatorLp_two_norm] at hErnorm
    exact hErnorm.trans (by gcongr)
  exact normalizedStoppingPairing F G H hGH _ lo hi er Hi Er hL hC.le hQ
    (fun x _ => annularDyadicValue_selected_decomposition D (τ x) Q F x) hlo hhi her hHn hEn

end PrimeSquares
