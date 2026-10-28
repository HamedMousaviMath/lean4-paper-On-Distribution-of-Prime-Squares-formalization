import PrimeSquares.FourierGaussCompatibility
import PrimeSquares.MangoldtNonunits

/-!
# Exact residue grouping of the square Fourier sums

The full finite symbol at a/q + theta is grouped over all residue classes,
then over the actual unit group with the non-unit remainder retained.
This is the finite identity in the proof of Lemma 6.5, for arbitrary real
weights. No progression asymptotic or model approximation is assumed.
-/

open Finset
open scoped Classical

namespace PrimeSquares

theorem negativeFourierCharacter_add_argument (n : ℤ) (α β : PrimeCircle) :
    negativeFourierCharacter n (α+β) =
      negativeFourierCharacter n α * negativeFourierCharacter n β := by
  simp only [negativeFourierCharacter, fourier_apply, zsmul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

theorem negativeSquareCharacter_rational_shift (q : ℕ) [NeZero q] (a : ℤ)
    (n : ℕ) (θ : PrimeCircle) :
    negativeFourierCharacter ((n : ℤ)^2) ((((a : ℝ) / q : ℝ) : PrimeCircle)+θ) =
      ZMod.stdAddChar (-((a : ZMod q) * (n : ZMod q)^2)) *
        negativeFourierCharacter ((n : ℤ)^2) θ := by
  rw [negativeFourierCharacter_add_argument, negativeSquareCharacter_rational]

noncomputable def squareResidueSum (S : Finset ℕ) (q : ℕ) (r : ZMod q)
    (w : ℕ → ℝ) (θ : PrimeCircle) : ℂ :=
  ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = r),
    (w n : ℂ) * negativeFourierCharacter ((n : ℤ)^2) θ

theorem finite_sum_residue_fibers (S : Finset ℕ) (q : ℕ) [NeZero q]
    (F : ZMod q → ℕ → ℂ) :
    (∑ r : ZMod q, ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod q) = r), F r n) =
      ∑ n ∈ S, F (n : ZMod q) n := by
  classical
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  simp

theorem finiteSquareSymbol_residues (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ)
    (q : ℕ) [NeZero q] (a : ℤ) (θ : PrimeCircle) :
    finiteSquareSymbol S c w ((((a : ℝ) / q : ℝ) : PrimeCircle)+θ) =
      (c : ℂ) * ∑ r : ZMod q, ZMod.stdAddChar (-((a : ZMod q)*r^2)) *
        squareResidueSum S q r w θ := by
  rw [finiteSquareSymbol_apply]
  congr 1
  simp only [squareResidueSum, mul_sum]
  rw [finite_sum_residue_fibers]
  apply sum_congr rfl
  intro n _
  rw [negativeSquareCharacter_rational_shift]
  ring

theorem squareResidueSum_coprime_filter (S : Finset ℕ) (q : ℕ)
    (r : ZMod q) (w : ℕ → ℝ) (θ : PrimeCircle) :
    squareResidueSum (S.filter (fun n => n.Coprime q)) q r w θ =
      if IsUnit r then squareResidueSum S q r w θ else 0 := by
  classical
  simp only [squareResidueSum, filter_filter, sum_filter]
  by_cases hr : IsUnit r
  · rw [ite_eq_left hr]
    apply sum_congr rfl
    intro n _
    by_cases hn : (n : ZMod q) = r
    · have hc : n.Coprime q := by rw [← ZMod.isUnit_iff_coprime, hn]; exact hr
      rw [ite_eq_left ⟨hc, hn⟩, ite_eq_left hn]
    · simp only [hn, and_false, ite_false]
  · rw [ite_eq_right hr]
    apply sum_eq_zero
    intro n _
    by_cases hn : (n : ZMod q) = r
    · have hc : ¬n.Coprime q := by rw [← ZMod.isUnit_iff_coprime, hn]; exact hr
      simp only [hc, false_and, ite_false]
    · simp only [hn, and_false, ite_false]

theorem finiteSquareSymbol_coprime_residues (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ)
    (q : ℕ) [NeZero q] (a : ℤ) (θ : PrimeCircle) :
    finiteSquareSymbol (S.filter (fun n => n.Coprime q)) c w
        ((((a : ℝ) / q : ℝ) : PrimeCircle)+θ) =
      (c : ℂ) * ∑ u : (ZMod q)ˣ,
        ZMod.stdAddChar (-((a : ZMod q)*(u : ZMod q)^2)) *
          squareResidueSum S q (u : ZMod q) w θ := by
  rw [finiteSquareSymbol_residues]
  simp only [squareResidueSum_coprime_filter, mul_ite, mul_zero]
  rw [sum_unit_filter_eq_sum_units]

theorem finiteSquareSymbol_coprime_split (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ)
    (q : ℕ) (ξ : PrimeCircle) :
    finiteSquareSymbol S c w ξ =
      finiteSquareSymbol (S.filter (fun n => n.Coprime q)) c w ξ +
      finiteSquareSymbol (S.filter (fun n => ¬n.Coprime q)) c w ξ := by
  simp only [finiteSquareSymbol_apply, ← mul_add]
  congr 1
  exact (sum_filter_add_sum_filter_not S (fun n => n.Coprime q) _).symm

theorem finiteSquareSymbol_reduced_residues (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ)
    (q : ℕ) [NeZero q] (a : ℤ) (θ : PrimeCircle) :
    finiteSquareSymbol S c w ((((a : ℝ) / q : ℝ) : PrimeCircle)+θ) =
      (c : ℂ) * ∑ u : (ZMod q)ˣ,
        ZMod.stdAddChar (-((a : ZMod q)*(u : ZMod q)^2)) *
          squareResidueSum S q (u : ZMod q) w θ +
      finiteSquareSymbol (S.filter (fun n => ¬n.Coprime q)) c w
        ((((a : ℝ) / q : ℝ) : PrimeCircle)+θ) := by
  rw [finiteSquareSymbol_coprime_split S c w q, finiteSquareSymbol_coprime_residues]

end PrimeSquares
