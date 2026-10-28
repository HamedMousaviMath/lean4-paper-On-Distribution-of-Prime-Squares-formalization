import PrimeSquares.AnnularCutoffInverseKernel
import PrimeSquares.CompactCircleInverseKernel

namespace PrimeSquares

noncomputable def circleAnnularCutoff (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (a : ℝ) (ha : 2 ≤ a) : C(PrimeCircle, ℂ) :=
  compactCircleLift (annularCutoffSymbol N hN β a) (annularCutoffSymbol_support N hN β ha)

theorem circleAnnularCutoff_kernel {N : ℕ} (hN : 1 ≤ N) (β : ℝ) {a : ℝ} (ha : 2 ≤ a) (x : ℤ) :
    fourierKernel (circleAnnularCutoff N hN β a ha) x=smoothedAnnularKernel N β a x := by
  rw [circleAnnularCutoff,compactCircleLift_inverse_kernel _ _
    (fun ξ hξ => annularCutoffSymbol_narrow N hN β ha hξ),annular_cutoff_inverse_transform hN β ha]

end PrimeSquares
