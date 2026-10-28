import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual finite-set pairings and the l² bridge

The high part is an element of Mathlib's genuine `lp` space at exponent two.
The Cauchy--Schwarz bound is derived from its norm, including empty test sets.
The convolution with an indicator is the explicit finite kernel sum.
-/

open Finset
open scoped lp

namespace PrimeSquares

variable {α : Type*}

theorem norm_finite_sum_le_card_mul (G : Finset α) (f : α → ℂ) (B : ℝ)
    (hf : ∀ x ∈ G, ‖f x‖ ≤ B) : ‖∑ x ∈ G, f x‖ ≤ (G.card : ℝ) * B := by
  calc
    _ ≤ ∑ x ∈ G, ‖f x‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ G, B := sum_le_sum hf
    _ = _ := by simp

theorem norm_finite_sum_le_energy (G : Finset α) (f : α → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∑ x ∈ G, ‖f x‖ ^ 2 ≤ E ^ 2) :
    ‖∑ x ∈ G, f x‖ ≤ E * Real.sqrt (G.card : ℝ) := by
  have hcs : (∑ x ∈ G, ‖f x‖) ^ 2 ≤ (∑ x ∈ G, ‖f x‖ ^ 2) * (G.card : ℝ) := by
    simpa only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one] using
      sum_mul_sq_le_sq_mul_sq G (fun x => ‖f x‖) (fun _ => (1 : ℝ))
  have hs : (∑ x ∈ G, ‖f x‖) ^ 2 ≤ E ^ 2 * (G.card : ℝ) :=
    hcs.trans (mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg _))
  have hnorm := norm_sum_le G f
  have hsum : 0 ≤ ∑ x ∈ G, ‖f x‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg G.card)
  have hpos : 0 ≤ E * Real.sqrt (G.card : ℝ) := mul_nonneg hE (Real.sqrt_nonneg _)
  have he : (E * Real.sqrt (G.card : ℝ)) ^ 2 = E ^ 2 * (G.card : ℝ) := by
    rw [mul_pow, hsqrt]
  have hle : ∑ x ∈ G, ‖f x‖ ≤ E * Real.sqrt (G.card : ℝ) := by nlinarith
  exact hnorm.trans hle

theorem norm_finite_sum_le_lp_two (G : Finset α) (f : ℓ²(α, ℂ)) :
    ‖∑ x ∈ G, f x‖ ≤ ‖f‖ * Real.sqrt (G.card : ℝ) := by
  apply norm_finite_sum_le_energy G f ‖f‖ (norm_nonneg _)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.sum_rpow_le_norm_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) f G

/-- Triangle inequality and Cauchy--Schwarz, proved for the genuine high output. -/
theorem finite_highLow_pairing_bound (G : Finset α) (f lo : α → ℂ) (hi : ℓ²(α, ℂ))
    (B : ℝ) (heq : ∀ x ∈ G, f x = lo x + hi x) (hlo : ∀ x ∈ G, ‖lo x‖ ≤ B) :
    ‖∑ x ∈ G, f x‖ ≤ (G.card : ℝ) * B + ‖hi‖ * Real.sqrt (G.card : ℝ) := by
  have he : (∑ x ∈ G, f x) = (∑ x ∈ G, lo x) + ∑ x ∈ G, hi x := by
    rw [← sum_add_distrib]
    exact sum_congr rfl heq
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (norm_finite_sum_le_card_mul G lo B hlo)
    (norm_finite_sum_le_lp_two G hi))

noncomputable def indicatorConvolution (K : ℤ → ℂ) (F : Finset ℤ) (x : ℤ) : ℂ :=
  ∑ y ∈ F, K (x - y)

noncomputable def restrictedKernelPairing (K : ℤ → ℂ) (F G : Finset ℤ) : ℂ :=
  ∑ x ∈ G, indicatorConvolution K F x

theorem indicatorConvolution_empty (K : ℤ → ℂ) (x : ℤ) :
    indicatorConvolution K ∅ x = 0 := by simp [indicatorConvolution]

theorem restrictedKernelPairing_empty_left (K : ℤ → ℂ) (G : Finset ℤ) :
    restrictedKernelPairing K ∅ G = 0 := by
  simp [restrictedKernelPairing, indicatorConvolution_empty]

theorem restrictedKernelPairing_empty_right (K : ℤ → ℂ) (F : Finset ℤ) :
    restrictedKernelPairing K F ∅ = 0 := by simp [restrictedKernelPairing]

theorem indicatorConvolution_add (K L : ℤ → ℂ) (F : Finset ℤ) (x : ℤ) :
    indicatorConvolution (K + L) F x = indicatorConvolution K F x + indicatorConvolution L F x := by
  simp only [indicatorConvolution, Pi.add_apply, sum_add_distrib]

theorem indicatorConvolution_norm_le (K : ℤ → ℂ) (F : Finset ℤ) (M : ℝ)
    (hK : ∀ z, ‖K z‖ ≤ M) (x : ℤ) :
    ‖indicatorConvolution K F x‖ ≤ (F.card : ℝ) * M :=
  norm_finite_sum_le_card_mul F (fun y => K (x - y)) M (fun _ _ => hK _)

theorem restrictedKernelPairing_norm_le (K : ℤ → ℂ) (F G : Finset ℤ) (M : ℝ)
    (hK : ∀ z, ‖K z‖ ≤ M) :
    ‖restrictedKernelPairing K F G‖ ≤ (F.card : ℝ) * (G.card : ℝ) * M := by
  calc
    _ ≤ (G.card : ℝ) * ((F.card : ℝ) * M) :=
      norm_finite_sum_le_card_mul G (indicatorConvolution K F) _
        (fun x _ => indicatorConvolution_norm_le K F M hK x)
    _ = _ := by ring

end PrimeSquares
