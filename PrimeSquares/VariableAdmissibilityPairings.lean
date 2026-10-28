import PrimeSquares.OrdinarySquareStoppingEndpoint
import PrimeSquares.PrimeLargeStoppingPairing

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

theorem ordinaryStopping_pairing_scalar_with_constant {CS B₀ : ℝ} (hCS : 1 ≤ CS) (hB₀ : 1 ≤ B₀)
    (HS : OrdinarySquareStoppingInput CS) (I : SparseIntegerInterval)
    (F G H : Finset ℤ) (τ : ℤ → ℕ)
    (hF : F ⊆ I.five.points) (hG : G ⊆ I.points) (hGH : G ⊆ H)
    (hscale : ∀ x ∈ G, ((2 : ℕ)^(τ x)*2)^2 ≤ I.length)
    (hadm : ∀ x ∈ G, sourceLocalMass ((2 : ℕ)^(τ x)*2) (finiteIndicatorLp F 1) x ≤
      B₀*((F.card : ℝ)/I.length)) (k : ℕ) (hk : 2 ≤ (2 : ℝ)^k) :
    ‖∑ x ∈ G, ordinaryDyadicValue (τ x) F x‖ / (5*(I.length : ℝ)) ≤
      ((5*B₀)*CS) * (finiteSetDensity (5*(I.length : ℝ)) F H * ((2 : ℝ)^k) *
        (Real.log ((2 : ℝ)^k))^(2 : ℝ) +
        (finiteSetDensity (5*(I.length : ℝ)) F H)^(1/2 : ℝ) *
          ((2 : ℝ)^k)^(-(1/2 : ℝ)) * Real.log ((2 : ℝ)^k)) := by
  obtain ⟨lo, hi, heq, hlo, hhi⟩ := HS I F G τ B₀ hB₀ hF hG hscale hadm k hk
  have hCS0 : 0 < CS := by linarith
  have hB0 : 0 < B₀ := by linarith
  let C := (5*B₀)*CS
  let L := 5*(I.length : ℝ)
  let Q := (2 : ℝ)^k
  have hI : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hL : 0 < L := by dsimp [L]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by dsimp [Q]; linarith)
  have hCC : CS ≤ C := by
    dsimp [C]
    have hh := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ)≤5*B₀) hCS0.le
    simpa only [one_mul] using hh
  let B := C/L*Q*(Real.log Q)^(2 : ℝ)*(F.card : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlo' : ∀ x ∈ G, ‖lo x‖ ≤ B := by
    intro x hx
    have he : CS*B₀*((F.card : ℝ)/I.length)*Q*(Real.log Q)^(2 : ℝ) = B := by
      dsimp [B, C, L]
      field_simp
    exact (hlo x hx).trans_eq he
  have hhi' : ‖hi‖ ≤ C*Q^(-(1/2 : ℝ))*Real.log Q*Real.sqrt (F.card : ℝ) :=
    hhi.trans (by gcongr)
  have hcG : (G.card : ℝ) ≤ H.card := by exact_mod_cast card_le_card hGH
  have hraw := finite_highLow_pairing_bound G _ lo hi B heq hlo'
  have hbig : ‖∑ x ∈ G, ordinaryDyadicValue (τ x) F x‖ ≤
      (H.card : ℝ)*B + (C*Q^(-(1/2 : ℝ))*Real.log Q*Real.sqrt (F.card : ℝ))*
        Real.sqrt (H.card : ℝ) := by
    exact hraw.trans (add_le_add (mul_le_mul_of_nonneg_right hcG hB)
      (mul_le_mul hhi' (Real.sqrt_le_sqrt hcG) (Real.sqrt_nonneg _)
        (by positivity)))
  have he := normalized_pairing_terms L (F.card : ℝ) (H.card : ℝ)
    (Q*(Real.log Q)^(2 : ℝ)) (Q^(-(1/2 : ℝ))*Real.log Q) C hL
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ ((H.card : ℝ)*B + (C*Q^(-(1/2 : ℝ))*Real.log Q*Real.sqrt (F.card : ℝ))*
        Real.sqrt (H.card : ℝ))/L := div_le_div_of_nonneg_right hbig hL.le
    _ = _ := by
      dsimp only [B, finiteSetDensity]
      convert he using 1 <;> ring

theorem ordinaryStopping_endpoint_with_constant {CS B₀ : ℝ} (hCS : 1 ≤ CS) (hB₀ : 1 ≤ B₀)
    (HS : OrdinarySquareStoppingInput CS) :
    ∃ K : ℝ, 0 < K ∧ ∀ (I : SparseIntegerInterval) (F G H : Finset ℤ) (τ : ℤ → ℕ),
      F ⊆ I.five.points → H ⊆ I.five.points → G ⊆ I.points → G ⊆ H →
      F.Nonempty → H.Nonempty →
      (∀ x ∈ G, ((2 : ℕ)^(τ x)*2)^2 ≤ I.length) →
      (∀ x ∈ G, sourceLocalMass ((2 : ℕ)^(τ x)*2) (finiteIndicatorLp F 1) x ≤
        B₀*((F.card : ℝ)/I.length)) →
      ‖∑ x ∈ G, ordinaryDyadicValue (τ x) F x‖/(5*(I.length : ℝ)) ≤
        K*(finiteSetDensity (5*(I.length : ℝ)) F H)^(2/3 : ℝ)*
          (paperLog (finiteSetDensity (5*(I.length : ℝ)) F H))^(4/3 : ℝ) := by
  have hCS0 : 0 < CS := by linarith
  have hB0 : 0 < B₀ := by linarith
  let K := ((5*B₀)*CS)*highLowOptimizationConstant 1 (1/2) 2 1
  have hC : 0 < (5*B₀)*CS := by positivity
  have hK : 0 < K := mul_pos hC (highLowOptimizationConstant_pos (by norm_num) (by norm_num) _ _)
  refine ⟨K, hK, ?_⟩
  intro I F G H τ hF hH hG hGH hFn hHn hscale hadm
  let L := 5*(I.length : ℝ)
  have hI : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hL : 0 < L := by dsimp [L]; positivity
  have hFc : (F.card : ℝ) ≤ L := by
    have hh := card_le_card hF
    rw [integerInterval_card_points] at hh
    change _ ≤ 5*I.length at hh
    dsimp [L]
    exact_mod_cast hh
  have hHc : (H.card : ℝ) ≤ L := by
    have hh := card_le_card hH
    rw [integerInterval_card_points] at hh
    change _ ≤ 5*I.length at hh
    dsimp [L]
    exact_mod_cast hh
  have hF0 : (0 : ℝ) < F.card := by exact_mod_cast card_pos.mpr hFn
  have hH0 : (0 : ℝ) < H.card := by exact_mod_cast card_pos.mpr hHn
  have hd : 0 < finiteSetDensity L F H := div_pos (mul_pos hF0 hH0) (sq_pos_of_pos hL)
  have hd1 : finiteSetDensity L F H ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hL)).mpr
    simpa only [pow_two] using mul_le_mul hFc hHc (Nat.cast_nonneg _) hL.le
  have hb := unrestricted_highLow_scalar (s := 1) (r := 1/2) (γ := 2) (β := 1)
    (δ := finiteSetDensity L F H) (C := (5*B₀)*CS) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hd hd1 hC.le (fun k hk => by
      simpa only [Real.rpow_one] using ordinaryStopping_pairing_scalar_with_constant hCS hB₀ HS I F G H τ
        hF hG hGH hscale hadm k hk)
  norm_num only [highLowEndpoint, highLowDensityExponent, highLowLogExponent,
    show (1 : ℝ)-1/(2*(1+1/2))=2/3 by norm_num,
    show (2 : ℝ)+1*(1-2)/(1+1/2)=4/3 by norm_num] at hb
  simpa only [K, mul_assoc] using hb


theorem primeLargeStopping_pairing_with_constant {c δ c₁ B₀ : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (H419 : Proposition419Bounds D δ) (hδ : 0 < δ) (hc₁ : 2 < c₁) (hB₀ : 1 ≤ B₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : SparseIntegerInterval) (F G H : Finset ℤ) (τ : ℤ → ℕ)
      (k : ℕ) (N₀ : ℝ), G ⊆ H → 2 ≤ (2 : ℝ)^k → 2 ≤ N₀ →
      Real.log ((2 : ℝ)^k) ≤ δ*Real.sqrt (Real.log N₀) →
      (∀ x ∈ G, N₀ ≤ (((2 : ℕ)^(τ x)*2 : ℕ) : ℝ)) →
      (∀ x ∈ G, sourceLocalMass ((2 : ℕ)^(τ x)*2) (finiteIndicatorLp F 1) x ≤
        B₀*((F.card : ℝ)/I.length)) →
      ‖∑ x ∈ G, annularDyadicValue (τ x) F x‖/(5*(I.length : ℝ)) ≤
        C*localPrimeScalar c₁ (finiteSetDensity (5*(I.length : ℝ)) F H) ((2 : ℝ)^k) := by
  obtain ⟨KH, hKH, _, hHigh⟩ := H419.high (c₁-2) (by linarith)
  obtain ⟨KR, hKR, hReg⟩ := regularizedHighFactor_dyadic c₁
  obtain ⟨KE, hKE, hError⟩ := selectedPrimeError_countable_maximum D H419
  have hB0 : 0 < B₀ := by linarith
  let CL := 80*B₀*lowSpatialConstant
  have hCL : 0 ≤ CL := mul_nonneg (by positivity) lowSpatialConstant_nonneg
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
      _ ≤ (8*lowSpatialConstant*Q*Real.log (2*Q))*(B₀*((F.card : ℝ)/I.length)) :=
        hl.trans (mul_le_mul_of_nonneg_left (hadm x hx) (by
          have hh := Real.log_nonneg (show (1 : ℝ) ≤ 2*Q by linarith)
          positivity))
      _ ≤ (8*lowSpatialConstant*Q*(2*Real.log Q))*(B₀*((F.card : ℝ)/I.length)) := by gcongr
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
