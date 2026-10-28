import PrimeSquares.IndependentStoppingInputs
import PrimeSquares.UnrestrictedHighLowBalance

/-!
# Deduce the ordinary-square local endpoint from its independent low/high input

The actual test set G may be smaller than a reference test set H. The
density on the right uses H, so later restriction to the small prime
stopping scales does not require an unstated monotonicity of a log bump.
-/

open Finset
open scoped lp
namespace PrimeSquares

theorem ordinaryStopping_pairing_scalar {CS : ℝ} (hCS : 1 ≤ CS)
    (HS : OrdinarySquareStoppingInput CS) (I : SparseIntegerInterval)
    (F G H : Finset ℤ) (τ : ℤ → ℕ)
    (hF : F ⊆ I.five.points) (hG : G ⊆ I.points) (hGH : G ⊆ H)
    (hscale : ∀ x ∈ G, ((2 : ℕ)^(τ x)*2)^2 ≤ I.length)
    (hadm : ∀ x ∈ G, sourceLocalMass ((2 : ℕ)^(τ x)*2) (finiteIndicatorLp F 1) x ≤
      320*((F.card : ℝ)/I.length)) (k : ℕ) (hk : 2 ≤ (2 : ℝ)^k) :
    ‖∑ x ∈ G, ordinaryDyadicValue (τ x) F x‖ / (5*(I.length : ℝ)) ≤
      (1600*CS) * (finiteSetDensity (5*(I.length : ℝ)) F H * ((2 : ℝ)^k) *
        (Real.log ((2 : ℝ)^k))^(2 : ℝ) +
        (finiteSetDensity (5*(I.length : ℝ)) F H)^(1/2 : ℝ) *
          ((2 : ℝ)^k)^(-(1/2 : ℝ)) * Real.log ((2 : ℝ)^k)) := by
  obtain ⟨lo, hi, heq, hlo, hhi⟩ := HS I F G τ 320 (by norm_num) hF hG hscale hadm k hk
  let C := 1600*CS
  let L := 5*(I.length : ℝ)
  let Q := (2 : ℝ)^k
  have hI : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hL : 0 < L := by dsimp [L]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by dsimp [Q]; linarith)
  have hCC : CS ≤ C := by dsimp [C]; linarith
  let B := C/L*Q*(Real.log Q)^(2 : ℝ)*(F.card : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlo' : ∀ x ∈ G, ‖lo x‖ ≤ B := by
    intro x hx
    have he : CS*320*((F.card : ℝ)/I.length)*Q*(Real.log Q)^(2 : ℝ) = B := by
      dsimp [B, C, L]
      field_simp
      ring
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

theorem ordinaryStopping_endpoint {CS : ℝ} (hCS : 1 ≤ CS)
    (HS : OrdinarySquareStoppingInput CS) :
    ∃ K : ℝ, 0 < K ∧ ∀ (I : SparseIntegerInterval) (F G H : Finset ℤ) (τ : ℤ → ℕ),
      F ⊆ I.five.points → H ⊆ I.five.points → G ⊆ I.points → G ⊆ H →
      F.Nonempty → H.Nonempty →
      (∀ x ∈ G, ((2 : ℕ)^(τ x)*2)^2 ≤ I.length) →
      (∀ x ∈ G, sourceLocalMass ((2 : ℕ)^(τ x)*2) (finiteIndicatorLp F 1) x ≤
        320*((F.card : ℝ)/I.length)) →
      ‖∑ x ∈ G, ordinaryDyadicValue (τ x) F x‖/(5*(I.length : ℝ)) ≤
        K*(finiteSetDensity (5*(I.length : ℝ)) F H)^(2/3 : ℝ)*
          (paperLog (finiteSetDensity (5*(I.length : ℝ)) F H))^(4/3 : ℝ) := by
  let K := (1600*CS)*highLowOptimizationConstant 1 (1/2) 2 1
  have hC : 0 < 1600*CS := by linarith
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
    (δ := finiteSetDensity L F H) (C := 1600*CS) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hd hd1 hC.le (fun k hk => by
      simpa only [Real.rpow_one] using ordinaryStopping_pairing_scalar hCS HS I F G H τ
        hF hG hGH hscale hadm k hk)
  norm_num only [highLowEndpoint, highLowDensityExponent, highLowLogExponent,
    show (1 : ℝ)-1/(2*(1+1/2))=2/3 by norm_num,
    show (2 : ℝ)+1*(1-2)/(1+1/2)=4/3 by norm_num] at hb
  simpa only [K, mul_assoc] using hb

end PrimeSquares
