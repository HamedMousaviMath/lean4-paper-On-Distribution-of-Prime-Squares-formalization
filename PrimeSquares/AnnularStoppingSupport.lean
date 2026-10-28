import PrimeSquares.IntegerIntervalGeometry
import PrimeSquares.PrimeSquareAverages

/-! # Exact support localization used in the stopping recursion -/

open Finset
namespace PrimeSquares

theorem annularSquare_indicator_localize (I : SparseIntegerInterval) {N : ℕ}
    (hN : N^2 ≤ I.length) (w : ℕ → ℝ) (F : Finset ℤ) {x : ℤ} (hx : x ∈ I.points) :
    indicatorConvolution (annularWeightedSquareAverageKernel N w) F x =
      indicatorConvolution (annularWeightedSquareAverageKernel N w) (F ∩ I.five.points) x := by
  unfold indicatorConvolution
  symm
  apply sum_subset inter_subset_left
  intro y hyF hy
  apply finiteSquareKernel_support_interval _ N (annularIndices_subset N)
  intro hz
  have hh := mem_Icc.mp hz
  have hs : (N : ℤ)^2 ≤ I.length := by exact_mod_cast hN
  have hd : |x-y| ≤ (I.length : ℤ) := by rw [abs_le]; constructor <;> omega
  exact hy (mem_inter.mpr ⟨hyF, integerInterval_local_ball_subset_five I hx hd⟩)

theorem annularSquare_indicator_restrict_twice {I R : SparseIntegerInterval}
    (hIR : I.points ⊆ R.points) {N : ℕ} (hN : N^2 ≤ I.length)
    (w : ℕ → ℝ) (F : Finset ℤ) {x : ℤ} (hx : x ∈ I.points) :
    indicatorConvolution (annularWeightedSquareAverageKernel N w) (F ∩ R.five.points) x =
      indicatorConvolution (annularWeightedSquareAverageKernel N w) (F ∩ I.five.points) x := by
  rw [annularSquare_indicator_localize I hN w (F ∩ R.five.points) hx]
  congr 1
  have h5 := integerInterval_five_subset hIR
  ext y
  simp only [mem_inter]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h5 h.2⟩, h.2⟩⟩

theorem nonnegativeKernel_indicator_norm_mono {K : ℤ → ℂ} (hK : NonnegativeKernel K)
    {F H : Finset ℤ} (hFH : F ⊆ H) (x : ℤ) :
    ‖indicatorConvolution K F x‖ ≤ ‖indicatorConvolution K H x‖ := by
  rw [complex_norm_eq_re (indicatorConvolution_im_zero hK F x)
      (indicatorConvolution_re_nonneg hK F x),
    complex_norm_eq_re (indicatorConvolution_im_zero hK H x)
      (indicatorConvolution_re_nonneg hK H x)]
  simp only [indicatorConvolution, Complex.re_sum]
  exact sum_le_sum_of_subset_of_nonneg hFH (fun y _ _ => (hK (x-y)).2)

theorem annularMangoldt_indicator_norm_mono (N : ℕ) {F H : Finset ℤ} (hFH : F ⊆ H) (x : ℤ) :
    ‖indicatorConvolution (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F x‖ ≤
      ‖indicatorConvolution (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) H x‖ := by
  exact nonnegativeKernel_indicator_norm_mono
    (finiteSquareKernel_nonnegative _ (by positivity) _
      (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)) hFH x

end PrimeSquares
