import PrimeSquares.HighLowOperators

/-!
# Positivity and domination of actual convolution pairings

For a nonnegative convolution kernel, summing its indicator outputs cannot
cancel. This connects the source's pointwise A_N domination to the B_N
pairing bound. The A_N kernel itself need not be nonnegative for this step.
-/

open Finset

namespace PrimeSquares

def NonnegativeKernel (K : ℤ → ℂ) : Prop :=
  ∀ z, (K z).im = 0 ∧ 0 ≤ (K z).re

theorem complex_norm_eq_re {z : ℂ} (him : z.im = 0) (hre : 0 ≤ z.re) : ‖z‖ = z.re := by
  have he : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simpa only [Complex.ofReal_im] using him
  rw [he, Complex.norm_of_nonneg hre]
  simp only [Complex.ofReal_re]

theorem indicatorConvolution_im_zero {K : ℤ → ℂ} (hK : NonnegativeKernel K)
    (F : Finset ℤ) (x : ℤ) : (indicatorConvolution K F x).im = 0 := by
  simp only [indicatorConvolution, Complex.im_sum]
  exact sum_eq_zero fun y _ => (hK (x - y)).1

theorem indicatorConvolution_re_nonneg {K : ℤ → ℂ} (hK : NonnegativeKernel K)
    (F : Finset ℤ) (x : ℤ) : 0 ≤ (indicatorConvolution K F x).re := by
  simp only [indicatorConvolution, Complex.re_sum]
  exact sum_nonneg fun y _ => (hK (x - y)).2

theorem restrictedKernelPairing_norm_positive {K : ℤ → ℂ} (hK : NonnegativeKernel K)
    (F G : Finset ℤ) :
    ‖restrictedKernelPairing K F G‖ = ∑ x ∈ G, (indicatorConvolution K F x).re := by
  have him : (restrictedKernelPairing K F G).im = 0 := by
    simp only [restrictedKernelPairing, Complex.im_sum]
    exact sum_eq_zero fun x _ => indicatorConvolution_im_zero hK F x
  have hre : 0 ≤ (restrictedKernelPairing K F G).re := by
    simp only [restrictedKernelPairing, Complex.re_sum]
    exact sum_nonneg fun x _ => indicatorConvolution_re_nonneg hK F x
  rw [complex_norm_eq_re him hre]
  simp only [restrictedKernelPairing, Complex.re_sum]

theorem restrictedKernelPairing_domination {KA KB : ℤ → ℂ} (hKB : NonnegativeKernel KB)
    (H : ℝ) (hdom : ∀ F : Finset ℤ, ∀ x,
      ‖indicatorConvolution KA F x‖ ≤ H * (indicatorConvolution KB F x).re)
    (F G : Finset ℤ) :
    ‖restrictedKernelPairing KA F G‖ ≤ H * ‖restrictedKernelPairing KB F G‖ := by
  calc
    _ ≤ ∑ x ∈ G, ‖indicatorConvolution KA F x‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ G, H * (indicatorConvolution KB F x).re := sum_le_sum fun x _ => hdom F x
    _ = _ := by rw [restrictedKernelPairing_norm_positive hKB]; exact (mul_sum G _ _).symm

theorem restrictedKernelPairing_domination_normalized {KA KB : ℤ → ℂ}
    (hKB : NonnegativeKernel KB) (H N : ℝ) (hN : 0 < N)
    (hdom : ∀ F : Finset ℤ, ∀ x,
      ‖indicatorConvolution KA F x‖ ≤ H * (indicatorConvolution KB F x).re)
    (F G : Finset ℤ) :
    ‖restrictedKernelPairing KA F G‖ / N ≤ H * (‖restrictedKernelPairing KB F G‖ / N) := by
  calc
    _ ≤ (H * ‖restrictedKernelPairing KB F G‖) / N :=
      div_le_div_of_nonneg_right (restrictedKernelPairing_domination hKB H hdom F G) hN.le
    _ = _ := by ring

end PrimeSquares
