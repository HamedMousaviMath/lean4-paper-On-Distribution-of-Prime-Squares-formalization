import PrimeSquares.RealOrdinaryTermKernel

open Finset
namespace PrimeSquares

noncomputable def realOrdinaryLowModel (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) (hQ : 0 < Q)
    (hb : 2*Q ≤ (N : ℝ)^2) : C(PrimeCircle, ℂ) :=
  ∑ q ∈ Icc 1 ⌊Q⌋₊,realOrdinaryCircleTerm N hN Q hQ hb q

noncomputable def realOrdinaryPhysicalKernel (N : ℕ) (Q : ℝ) (x : ℤ) : ℂ :=
  ∑ q ∈ Icc 1 ⌊Q⌋₊,normalizedCohenCorrelation q x*smoothedAnnularKernel N 1 (ordinaryLowWidth N Q q) x

theorem realOrdinaryLowModel_kernel (N : ℕ) (hN : 1 ≤ N) {Q : ℝ} (hQ : 0 < Q)
    (hb : 2*Q ≤ (N : ℝ)^2) (x : ℤ) :
    fourierKernel (realOrdinaryLowModel N hN Q hQ hb) x=realOrdinaryPhysicalKernel N Q x := by
  rw [realOrdinaryLowModel,fourierKernel_sum,realOrdinaryPhysicalKernel]
  apply sum_congr rfl
  intro q hq
  have : NeZero q := ⟨by have h := (mem_Icc.mp hq).1;omega⟩
  exact realOrdinaryCircleTerm_kernel N hN hQ hb q x

end PrimeSquares
