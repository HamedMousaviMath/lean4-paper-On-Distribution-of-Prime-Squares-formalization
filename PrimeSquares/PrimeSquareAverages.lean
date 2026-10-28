import PrimeSquares.WeightedSquareAverages
import Mathlib.NumberTheory.Chebyshev

/-!
# Elementary inputs for the actual von Mangoldt and square averages

Lambda is Mathlib's actual von Mangoldt function, including prime powers.
Chebyshev's proved elementary bound supplies a uniform norm without PNT.
The source positivity, domination and local spatial bound are deductions,
not hypotheses. The Fourier high-low decompositions remain separate work.
-/

open Finset
open scoped lp

namespace PrimeSquares

noncomputable def primeSquareChebyshevConstant : ℝ := Real.log 4 + 4

theorem primeSquareChebyshevConstant_pos : 0 < primeSquareChebyshevConstant := by
  have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  unfold primeSquareChebyshevConstant
  linarith

theorem mangoldt_square_mass_bound (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt n ≤ primeSquareChebyshevConstant * N := by
  simpa [Chebyshev.psi, primeSquareChebyshevConstant] using
    Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N : (0 : ℝ) ≤ N)

theorem mangoldt_weight_le_log {N n : ℕ} (hn : n ∈ Ioc 0 N) :
    ArithmeticFunction.vonMangoldt n ≤ Real.log N := by
  obtain ⟨hn0, hnN⟩ := mem_Ioc.mp hn
  exact ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnN))

theorem mangoldtSquareAverage_norm_le {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    {N : ℕ} (hN : 0 < N) :
    ‖weightedSquareAverage hp N ArithmeticFunction.vonMangoldt‖ ≤ primeSquareChebyshevConstant ∧
    ‖annularWeightedSquareAverage hp N ArithmeticFunction.vonMangoldt‖ ≤ primeSquareChebyshevConstant :=
  ⟨normalizedSquareOperator_norm_le hp hN _ (Subset.rfl) _
      (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (mangoldt_square_mass_bound N),
    normalizedSquareOperator_norm_le hp hN _ (annularIndices_subset N) _
      (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (mangoldt_square_mass_bound N)⟩

theorem ordinarySquareAverage_norm_le {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    {N : ℕ} (hN : 0 < N) :
    ‖weightedSquareAverage hp N (fun _ => 1)‖ ≤ 1 ∧
    ‖annularWeightedSquareAverage hp N (fun _ => 1)‖ ≤ 1 := by
  have hm : (∑ _ ∈ Ioc 0 N, (1 : ℝ)) ≤ 1 * N := by simp
  exact ⟨normalizedSquareOperator_norm_le hp hN _ (Subset.rfl) _ (fun _ => by norm_num) hm,
    normalizedSquareOperator_norm_le hp hN _ (annularIndices_subset N) _ (fun _ => by norm_num) hm⟩

theorem mangoldtSquareKernel_l2_bound {N : ℕ} (hN : 0 < N) :
    KernelL2Bound (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt)
      primeSquareChebyshevConstant ∧
    KernelL2Bound (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt)
      primeSquareChebyshevConstant :=
  ⟨normalizedSquareKernel_l2_bound hN _ (Subset.rfl) _
      (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (mangoldt_square_mass_bound N),
    normalizedSquareKernel_l2_bound hN _ (annularIndices_subset N) _
      (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (mangoldt_square_mass_bound N)⟩

theorem ordinarySquareKernel_l2_bound {N : ℕ} (hN : 0 < N) :
    KernelL2Bound (weightedSquareAverageKernel N (fun _ => 1)) 1 ∧
    KernelL2Bound (annularWeightedSquareAverageKernel N (fun _ => 1)) 1 := by
  have hm : (∑ _ ∈ Ioc 0 N, (1 : ℝ)) ≤ 1 * N := by simp
  exact ⟨normalizedSquareKernel_l2_bound hN _ (Subset.rfl) _ (fun _ => by norm_num) hm,
    normalizedSquareKernel_l2_bound hN _ (annularIndices_subset N) _ (fun _ => by norm_num) hm⟩

theorem annularMangoldt_indicator_domination (N : ℕ) (F : Finset ℤ) (x : ℤ) :
    ‖indicatorConvolution (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F x‖ ≤
      Real.log N * (indicatorConvolution (annularWeightedSquareAverageKernel N (fun _ => 1)) F x).re := by
  apply finiteSquareKernel_indicator_domination _ (by positivity) _ _
    (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  intro n hn
  simpa only [mul_one] using mangoldt_weight_le_log (annularIndices_subset N hn)

theorem annularMangoldt_spatial_domination {N : ℕ} (hN : 0 < N) (F : Finset ℤ) (x : ℤ) :
    ‖indicatorConvolution (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F x‖ ≤
      Real.log ((N : ℝ)^2) *
        (indicatorConvolution (annularWeightedSquareAverageKernel N (fun _ => 1)) F x).re := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt hN)
  have hK : NonnegativeKernel (annularWeightedSquareAverageKernel N (fun _ => 1)) :=
    finiteSquareKernel_nonnegative _ (by positivity) _ (fun _ _ => by norm_num)
  have hcompare : Real.log N ≤ Real.log ((N : ℝ)^2) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  exact (annularMangoldt_indicator_domination N F x).trans
    (mul_le_mul_of_nonneg_right hcompare (indicatorConvolution_re_nonneg hK F x))

/-- The actual source elementary hypotheses at spatial scale N^2.
Only the two high-low decomposition fields of the abstract theorem
remain to be established for these kernels. -/
structure AnnularSquareElementaryInputs (N : ℕ) : Prop where
  prime_nonnegative : NonnegativeKernel
    (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt)
  square_nonnegative : NonnegativeKernel (annularWeightedSquareAverageKernel N (fun _ => 1))
  domination : ∀ F : Finset ℤ, ∀ x,
    ‖indicatorConvolution (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F x‖ ≤
      Real.log ((N : ℝ)^2) *
        (indicatorConvolution (annularWeightedSquareAverageKernel N (fun _ => 1)) F x).re
  local_bound : ∀ F : Finset ℤ, ∀ x,
    ‖indicatorConvolution (annularWeightedSquareAverageKernel N (fun _ => 1)) F x‖ ≤
      ((N : ℝ)^2)^(-(1/2 : ℝ)) * ‖finiteIndicatorLp (F ∩ squareAverageWindow N x) 1‖
  prime_l2 : KernelL2Bound (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt)
    primeSquareChebyshevConstant
  square_l2 : KernelL2Bound (annularWeightedSquareAverageKernel N (fun _ => 1)) 1

theorem annular_square_elementary_inputs {N : ℕ} (hN : 0 < N) : AnnularSquareElementaryInputs N where
  prime_nonnegative := finiteSquareKernel_nonnegative _ (by positivity) _
    (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  square_nonnegative := finiteSquareKernel_nonnegative _ (by positivity) _ (fun _ _ => by norm_num)
  domination := annularMangoldt_spatial_domination hN
  local_bound := squareKernel_local_bound N _ (annularIndices_subset N)
  prime_l2 := (mangoldtSquareKernel_l2_bound hN).2
  square_l2 := (ordinarySquareKernel_l2_bound hN).2

end PrimeSquares
