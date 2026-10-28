import PrimeSquares.OrdinaryAnnularPositiveFamily
import PrimeSquares.PrimeFullMaximalComparison
import PrimeSquares.RestrictedToModular
import PrimeSquares.NearOneGaugeComparison

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem fullOrdinaryKernel_cutoff_bound {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (hMN : M ≤ 2*N) (z : ℤ) :
    (weightedSquareAverageKernel N (fun _ => 1) z).re ≤
      2*(weightedSquareAverageKernel M (fun _ => 1) z).re := by
  have hM : 0 < M := hN.trans_le hNM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hKM := finiteSquareKernel_nonnegative (Ioc 0 M) (by positivity : 0 ≤ (M : ℝ)⁻¹)
    (fun _ => 1) (fun _ _ => by norm_num)
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
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ))
  · rw [weightedSquareAverageKernel, finiteSquareKernel_eq_zero _ _ _ hz, Complex.zero_re]
    exact mul_nonneg (by norm_num) (hKM z).2

theorem fullOrdinaryIndicator_cutoff_bound {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (hMN : M ≤ 2*N) (F : Finset ℤ) (x : ℤ) :
    ‖indicatorConvolution (weightedSquareAverageKernel N (fun _ => 1)) F x‖ ≤
      2*‖indicatorConvolution (weightedSquareAverageKernel M (fun _ => 1)) F x‖ := by
  have hKN := finiteSquareKernel_nonnegative (Ioc 0 N) (by positivity : 0 ≤ (N : ℝ)⁻¹)
    (fun _ => 1) (fun _ _ => by norm_num)
  have hKM := finiteSquareKernel_nonnegative (Ioc 0 M) (by positivity : 0 ≤ (M : ℝ)⁻¹)
    (fun _ => 1) (fun _ _ => by norm_num)
  change NonnegativeKernel (weightedSquareAverageKernel N (fun _ => 1)) at hKN
  change NonnegativeKernel (weightedSquareAverageKernel M (fun _ => 1)) at hKM
  rw [complex_norm_eq_re (indicatorConvolution_im_zero hKN F x) (indicatorConvolution_re_nonneg hKN F x),
    complex_norm_eq_re (indicatorConvolution_im_zero hKM F x) (indicatorConvolution_re_nonneg hKM F x)]
  simp only [indicatorConvolution, Complex.re_sum, mul_sum]
  exact sum_le_sum (fun y _ => fullOrdinaryKernel_cutoff_bound hN hNM hMN (x-y))

theorem ordinarySquareFullValue_indicator_kernel (N : ℕ) (F : Finset ℤ) (x : ℤ) :
    ordinarySquareFullValue N (finiteIndicator F) x =
      indicatorConvolution (weightedSquareAverageKernel N (fun _ => 1)) F x := by
  have h := weightedSquareAverage_finiteInput (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    N (fun _ => 1) F (fun _ => 1) x
  rw [finiteConvolution_indicator, finiteInputLp_one, weightedSquareAverage_apply] at h
  simpa only [ordinarySquareFullValue, finiteIndicatorLp, Complex.ofReal_one, Complex.ofReal_inv, one_mul] using h.symm

theorem ordinary_annular_indicator_kernel (j : ℕ) (F : Finset ℤ) (x : ℤ) :
    positiveAverage ordinaryAnnularDyadicFamily j (finiteIndicator F) x =
      indicatorConvolution (annularWeightedSquareAverageKernel ((2 : ℕ)^j)
        (fun _ => 1)) F x := by
  have h := annularWeightedSquareAverage_finiteInput (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    ((2 : ℕ)^j) (fun _ => 1) F (fun _ => 1) x
  rw [finiteConvolution_indicator, finiteInputLp_one] at h
  rw [h]
  exact ordinaryAnnularDyadicFamily_apply j (finiteIndicatorLp F 2) x

theorem ordinary_full_dyadic_annular_bound (F : Finset ℤ) (x : ℤ) (k : ℕ) :
    ‖indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^k)
      (fun _ => 1)) F x‖ ≤
      2*positiveMaximal ordinaryAnnularDyadicFamily (finiteIndicator F) x := by
  let B := positiveMaximal ordinaryAnnularDyadicFamily (finiteIndicator F) x
  have hB : 0 ≤ B := (positiveMaximal_indicator_bound ordinaryAnnularDyadicFamily F x).1
  induction k with
  | zero =>
    have hann := positiveMaximal_dominates ordinaryAnnularDyadicFamily (by norm_num : (0 : ℝ) ≤ 1)
      (finiteIndicator_norm_le_one F) 0 x
    rw [ordinary_annular_indicator_kernel] at hann
    have he : annularWeightedSquareAverageKernel ((2 : ℕ)^0) (fun _ => 1) =
        weightedSquareAverageKernel 1 (fun _ => 1) := rfl
    rw [he] at hann
    simp only [pow_zero]
    exact hann.trans (by linarith)

  | succ k ih =>
    have hd := annular_indicator_two_mul ((2 : ℕ)^k) (fun _ => 1) F x
    rw [Nat.mul_comm 2 ((2 : ℕ)^k)] at hd
    have he : indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^k*2)
        (fun _ => 1)) F x =
      indicatorConvolution (annularWeightedSquareAverageKernel ((2 : ℕ)^k*2)
        (fun _ => 1)) F x+(1/2 : ℂ)*
          indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^k) (fun _ => 1)) F x := by
      rw [hd]; ring
    have hann := positiveMaximal_dominates ordinaryAnnularDyadicFamily (by norm_num : (0 : ℝ) ≤ 1)
      (finiteIndicator_norm_le_one F) (k+1) x
    rw [ordinary_annular_indicator_kernel, pow_succ] at hann
    rw [pow_succ, he]
    calc
      _ ≤ ‖indicatorConvolution (annularWeightedSquareAverageKernel ((2 : ℕ)^k*2)
          (fun _ => 1)) F x‖+(1/2 : ℝ)*
          ‖indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^k) (fun _ => 1)) F x‖ := by
        simpa only [norm_mul, show ‖(1/2 : ℂ)‖ = (1/2 : ℝ) by norm_num] using norm_add_le
          (indicatorConvolution (annularWeightedSquareAverageKernel ((2 : ℕ)^k*2) (fun _ => 1)) F x)
          ((1/2 : ℂ)*indicatorConvolution (weightedSquareAverageKernel ((2 : ℕ)^k) (fun _ => 1)) F x)
      _ ≤ B+(1/2 : ℝ)*(2*B) := add_le_add hann (mul_le_mul_of_nonneg_left ih (by norm_num))
      _ = _ := by ring

theorem ordinary_full_annular_maximal_bound (F : Finset ℤ) (x : ℤ) :
    positiveMaximal ordinaryPositiveFamily (finiteIndicator F) x ≤
      4*positiveMaximal ordinaryAnnularDyadicFamily (finiteIndicator F) x := by
  apply ciSup_le
  intro n
  rw [ordinaryPositiveFamily_apply, ordinarySquareFullValue_indicator_kernel]
  let N := n+2
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by dsimp [N]; omega)
  obtain ⟨k, _hk, hkN, hNk⟩ := exists_dyadic_below (show (2 : ℝ) ≤ 2*(N : ℝ) by linarith)
  have hNM : N ≤ (2 : ℕ)^k := by exact_mod_cast (show (N : ℝ) ≤ (2 : ℝ)^k by linarith)
  have hMN : (2 : ℕ)^k ≤ 2*N := by exact_mod_cast hkN
  exact (fullOrdinaryIndicator_cutoff_bound (by dsimp [N]; omega) hNM hMN F x).trans
    (by nlinarith [ordinary_full_dyadic_annular_bound F x k])

theorem positiveRestrictedGauge_ordinary_full {Cg Rg : ℝ} (hC : 0 ≤ Cg) (hR : 0 ≤ Rg)
    (H : PositiveRestrictedGauge ordinaryAnnularDyadicFamily Cg Rg) :
    PositiveRestrictedGauge ordinaryPositiveFamily Cg
      (Rg*(4*Real.exp (4*Cg*Real.log 2))^2) := by
  intro F t ht D
  have ht0 : 0 < t := by linarith
  have hdist := H F (4*t) (by linarith) D
  have hpsi2 := nearOnePsi_doubling hC (show 0 ≤ t by linarith)
  have hpsi4 := nearOnePsi_doubling hC (show 0 ≤ 2*t by linarith)
  rw [show 2*(2*t) = 4*t by ring] at hpsi4
  have hpsi : nearOnePsi Cg (4*t) ≤ (4*Real.exp (4*Cg*Real.log 2))^2*nearOnePsi Cg t := by
    have h := mul_le_mul_of_nonneg_left hpsi2 (show 0 ≤ 4*Real.exp (4*Cg*Real.log 2) by positivity)
    nlinarith
  have hsub : finiteDistribution D (positiveMaximal ordinaryPositiveFamily (finiteIndicator F)) (1/t) ≤
      finiteDistribution D (positiveMaximal ordinaryAnnularDyadicFamily (finiteIndicator F)) (1/(4*t)) := by
    classical
    apply Nat.cast_le.mpr
    apply card_le_card
    intro x hx
    obtain ⟨hx, hval⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨hx, ?_⟩
    have hbound := ordinary_full_annular_maximal_bound F x
    have he : 4*(1/(4*t)) = 1/t := by ring
    nlinarith
  calc
    _ ≤ Rg*(F.card : ℝ)*nearOnePsi Cg (4*t) := hsub.trans hdist
    _ ≤ Rg*(F.card : ℝ)*((4*Real.exp (4*Cg*Real.log 2))^2*nearOnePsi Cg t) :=
      mul_le_mul_of_nonneg_left hpsi (mul_nonneg hR (Nat.cast_nonneg F.card))
    _ = _ := by ring

end PrimeSquares
