import PrimeSquares.PrimeSparseRoot
import PrimeSquares.IndependentSquareDecomposition
import PrimeSquares.TheoremOneOne

/-!
# The literal full prime-square maximum is controlled by the finite root

Every integer cutoff N>=2 is compared with a dyadic full cutoff, then the
full-to-annular identity gives the factor four. The supremum is genuine:
its range is proved bounded and it dominates every original cutoff.
-/

open Finset
open scoped NNReal
namespace PrimeSquares

theorem fullPrimeKernel_cutoff_bound {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (hMN : M ≤ 2*N) (z : ℤ) :
    (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt z).re ≤
      2*(weightedSquareAverageKernel M ArithmeticFunction.vonMangoldt z).re := by
  have hM : 0 < M := hN.trans_le hNM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hKM := finiteSquareKernel_nonnegative (Ioc 0 M) (by positivity : 0 ≤ (M : ℝ)⁻¹)
    ArithmeticFunction.vonMangoldt (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  by_cases hz : z ∈ (Ioc 0 N).image (fun n : ℕ => (n : ℤ)^2)
  · obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
    have hnM : n ∈ Ioc 0 M := mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2.trans hNM⟩
    have hi : (N : ℝ)⁻¹ ≤ 2*(M : ℝ)⁻¹ := by
      have h : (1 : ℝ)/(N : ℝ) ≤ 2/(M : ℝ) :=
        (div_le_div_iff₀ hNr hMr).mpr (by
          simpa only [one_mul] using (show (M : ℝ) ≤ 2*(N : ℝ) by exact_mod_cast hMN))
      simpa only [one_div, div_eq_mul_inv, one_mul] using h
    simp only [weightedSquareAverageKernel, finiteSquareKernel_at_square,
      ite_eq_left hn, ite_eq_left hnM, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hi
      (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  · rw [weightedSquareAverageKernel, finiteSquareKernel_eq_zero _ _ _ hz, Complex.zero_re]
    exact mul_nonneg (by norm_num) (hKM z).2

theorem fullPrimeIndicator_cutoff_bound {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (hMN : M ≤ 2*N) (F : Finset ℤ) (x : ℤ) :
    ‖indicatorConvolution (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F x‖ ≤
      2*‖indicatorConvolution (weightedSquareAverageKernel M ArithmeticFunction.vonMangoldt) F x‖ := by
  have hKN := finiteSquareKernel_nonnegative (Ioc 0 N) (by positivity : 0 ≤ (N : ℝ)⁻¹)
    ArithmeticFunction.vonMangoldt (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hKM := finiteSquareKernel_nonnegative (Ioc 0 M) (by positivity : 0 ≤ (M : ℝ)⁻¹)
    ArithmeticFunction.vonMangoldt (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  change NonnegativeKernel (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) at hKN
  change NonnegativeKernel (weightedSquareAverageKernel M ArithmeticFunction.vonMangoldt) at hKM
  rw [complex_norm_eq_re (indicatorConvolution_im_zero hKN F x) (indicatorConvolution_re_nonneg hKN F x),
    complex_norm_eq_re (indicatorConvolution_im_zero hKM F x) (indicatorConvolution_re_nonneg hKM F x)]
  simp only [indicatorConvolution, Complex.re_sum, mul_sum]
  exact sum_le_sum (fun y _ => fullPrimeKernel_cutoff_bound hN hNM hMN (x-y))

theorem primeSparseRoot_full_dyadic (F G : Finset ℤ) {x : ℤ} (hx : x ∈ G) (k : ℕ) :
    ‖indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^k)
      ArithmeticFunction.vonMangoldt) F x‖ ≤
      2*(truncatedAnnularMaximum (primeSparseRoot F G).length F x : ℝ) := by
  let B : ℝ := truncatedAnnularMaximum (primeSparseRoot F G).length F x
  have hB : 0 ≤ B := NNReal.coe_nonneg _
  induction k with
  | zero =>
    have he : indicatorConvolution (weightedSquareAverageKernel 1 ArithmeticFunction.vonMangoldt) F x = 0 := by
      simp [indicatorConvolution, weightedSquareAverageKernel, finiteSquareKernel,
        show (Ioc 0 1 : Finset ℕ) = {1} by decide]
    simp only [pow_zero, he, norm_zero]
    positivity
  | succ k ih =>
    have hd := annular_indicator_two_mul ((2 : ℕ)^k) ArithmeticFunction.vonMangoldt F x
    rw [Nat.mul_comm 2 ((2 : ℕ)^k)] at hd
    have he : indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^k*2)
        ArithmeticFunction.vonMangoldt) F x = annularDyadicValue k F x + (1/2 : ℂ)*
          indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^k) ArithmeticFunction.vonMangoldt) F x := by
      change _ = indicatorConvolution (annularWeightedSquareAverageKernel ((2 : ℕ)^k*2)
        ArithmeticFunction.vonMangoldt) F x + _
      rw [hd]
      ring
    rw [pow_succ, he]
    calc
      _ ≤ ‖annularDyadicValue k F x‖ + (1/2 : ℝ)*
          ‖indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^k) ArithmeticFunction.vonMangoldt) F x‖ := by
        simpa only [norm_mul, show ‖(1/2 : ℂ)‖=(1/2 : ℝ) by norm_num] using norm_add_le
          (annularDyadicValue k F x) ((1/2 : ℂ)*indicatorConvolution
            (weightedSquareAverageKernel ((2 : ℕ)^k) ArithmeticFunction.vonMangoldt) F x)
      _ ≤ B+(1/2 : ℝ)*(2*B) := add_le_add (primeSparseRoot_dominates F G hx k)
        (mul_le_mul_of_nonneg_left ih (by norm_num))
      _ = _ := by ring

theorem primeSparseRoot_full_cutoff (F G : Finset ℤ) {x : ℤ} (hx : x ∈ G)
    {N : ℕ} (hN : 2 ≤ N) :
    ‖indicatorConvolution (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F x‖ ≤
      4*(truncatedAnnularMaximum (primeSparseRoot F G).length F x : ℝ) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨k, _, hkN, hNk⟩ := exists_dyadic_below (show (2 : ℝ) ≤ 2*(N : ℝ) by linarith)
  have hNM : N ≤ (2 : ℕ)^k := by exact_mod_cast (show (N : ℝ) ≤ (2 : ℝ)^k by linarith)
  have hMN : (2 : ℕ)^k ≤ 2*N := by exact_mod_cast hkN
  exact (fullPrimeIndicator_cutoff_bound (by omega : 0 < N) hNM hMN F x).trans
    (by nlinarith [primeSparseRoot_full_dyadic F G hx k])

theorem primeSquareAverageValue_indicator_kernel (N : ℕ) (F : Finset ℤ) (x : ℤ) :
    primeSquareAverageValue N (finiteIndicator F) x =
      indicatorConvolution (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F x := by
  have h := weightedSquareAverage_finiteInput (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    N ArithmeticFunction.vonMangoldt F (fun _ => 1) x
  rw [finiteConvolution_indicator, finiteInputLp_one, weightedSquareAverage_apply] at h
  exact h.symm

noncomputable def primeSquareMaximalIndicator (F : Finset ℤ) (x : ℤ) : ℝ :=
  ⨆ n : ℕ, ‖primeSquareAverageValue (n+2) (finiteIndicator F) x‖

noncomputable def primeSquareMaximalPairing (F G : Finset ℤ) : ℝ :=
  ∑ x ∈ G, primeSquareMaximalIndicator F x

theorem primeSquareMaximalIndicator_bdd (F : Finset ℤ) (x : ℤ) :
    BddAbove (Set.range (fun n : ℕ => ‖primeSquareAverageValue (n+2) (finiteIndicator F) x‖)) := by
  refine ⟨4*(truncatedAnnularMaximum (primeSparseRoot F {x}).length F x : ℝ), ?_⟩
  rintro _ ⟨n, rfl⟩
  change ‖primeSquareAverageValue (n+2) (finiteIndicator F) x‖ ≤ _
  rw [primeSquareAverageValue_indicator_kernel]
  exact primeSparseRoot_full_cutoff F {x} (mem_singleton_self _) (by omega)

theorem primeSquareMaximalIndicator_dominates (F : Finset ℤ) (x : ℤ) {N : ℕ} (hN : 2 ≤ N) :
    ‖primeSquareAverageValue N (finiteIndicator F) x‖ ≤ primeSquareMaximalIndicator F x := by
  change _ ≤ ⨆ n : ℕ, ‖primeSquareAverageValue (n+2) (finiteIndicator F) x‖
  have h : ‖primeSquareAverageValue (N-2+2) (finiteIndicator F) x‖ ≤
      ⨆ n : ℕ, ‖primeSquareAverageValue (n+2) (finiteIndicator F) x‖ :=
    le_ciSup (primeSquareMaximalIndicator_bdd F x) (N-2)
  simpa only [Nat.sub_add_cancel hN] using h

theorem primeSquareMaximalIndicator_nonneg (F : Finset ℤ) (x : ℤ) :
    0 ≤ primeSquareMaximalIndicator F x :=
  (norm_nonneg _).trans (primeSquareMaximalIndicator_dominates F x (by norm_num : 2 ≤ (2 : ℕ)))

theorem primeSquareMaximalPairing_nonneg (F G : Finset ℤ) : 0 ≤ primeSquareMaximalPairing F G :=
  sum_nonneg (fun x _ => primeSquareMaximalIndicator_nonneg F x)

theorem primeSquareMaximalPairing_le_root (F G : Finset ℤ) :
    primeSquareMaximalPairing F G ≤ 4*annularLocalMaxPairing (primeSparseRoot F G) F G := by
  rw [primeSparseRoot_pairing, mul_sum]
  apply sum_le_sum
  intro x hx
  apply ciSup_le
  intro n
  rw [primeSquareAverageValue_indicator_kernel]
  exact primeSparseRoot_full_cutoff F G hx (by omega)

end PrimeSquares
