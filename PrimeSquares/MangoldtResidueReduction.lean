import PrimeSquares.SquareResidueGrouping

/-!
# Quantified reduced-residue error for the actual annular symbol

The discarded non-unit terms have uniform Fourier norm at most
(log q + 2 sqrt(N) log N)/N. This is an unconditional finite-cutoff bound
and is stronger than the loose error used at this step in the source.
-/

open Finset

namespace PrimeSquares

theorem finiteSquareSymbol_norm_le_mass (S : Finset ℕ) {c : ℝ} (hc : 0 ≤ c)
    (w : ℕ → ℝ) (hw : ∀ n ∈ S, 0 ≤ w n) (ξ : PrimeCircle) :
    ‖finiteSquareSymbol S c w ξ‖ ≤ c * ∑ n ∈ S, w n := by
  rw [finiteSquareSymbol_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  calc
    _ ≤ ∑ n ∈ S, ‖(w n : ℂ) * negativeFourierCharacter ((n : ℤ)^2) ξ‖ := norm_sum_le _ _
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      rw [norm_mul, negativeFourierCharacter_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw n hn)]

theorem mangoldt_nonunit_symbol_norm_le {N q : ℕ} (hN : 1 ≤ N) (hq : 0 < q)
    (S : Finset ℕ) (hS : S ⊆ Ioc 0 N) {c : ℝ} (hc : 0 ≤ c) (ξ : PrimeCircle) :
    ‖finiteSquareSymbol (S.filter (fun n => ¬n.Coprime q)) c
        ArithmeticFunction.vonMangoldt ξ‖ ≤
      c * (Real.log q + 2 * Real.sqrt N * Real.log N) := by
  exact (finiteSquareSymbol_norm_le_mass _ hc _
    (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg) ξ).trans
      (mul_le_mul_of_nonneg_left (mangoldtNonunitMass_le hN hq S hS) hc)

theorem annularMangoldt_reduced_residues_bound {N q : ℕ} (hN : 1 ≤ N) [NeZero q]
    (a : ℤ) (θ : PrimeCircle) :
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt
        ((((a : ℝ) / q : ℝ) : PrimeCircle)+θ) -
      Complex.ofReal ((N : ℝ)⁻¹) * ∑ u : (ZMod q)ˣ,
        ZMod.stdAddChar (-((a : ZMod q)*(u : ZMod q)^2)) *
          squareResidueSum (Ioc (N/2) N) q (u : ZMod q)
            ArithmeticFunction.vonMangoldt θ‖ ≤
      (Real.log q + 2 * Real.sqrt N * Real.log N) / N := by
  change ‖finiteSquareSymbol (Ioc (N/2) N) (N : ℝ)⁻¹ ArithmeticFunction.vonMangoldt _ - _‖ ≤ _
  rw [finiteSquareSymbol_reduced_residues, add_sub_cancel_left]
  have h := mangoldt_nonunit_symbol_norm_le hN (NeZero.pos q) (Ioc (N/2) N)
    (annularIndices_subset N) (inv_nonneg.mpr (Nat.cast_nonneg N))
    ((((a : ℝ) / q : ℝ) : PrimeCircle)+θ)
  simpa only [div_eq_inv_mul] using h

theorem annularMangoldt_nonunit_symbol_one (N : ℕ) (ξ : PrimeCircle) :
    finiteSquareSymbol ((Ioc (N/2) N).filter (fun n => ¬n.Coprime 1)) (N : ℝ)⁻¹
      ArithmeticFunction.vonMangoldt ξ = 0 := by
  simp [finiteSquareSymbol]

end PrimeSquares
