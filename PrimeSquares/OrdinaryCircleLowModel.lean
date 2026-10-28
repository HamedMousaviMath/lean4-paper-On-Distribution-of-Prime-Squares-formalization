import PrimeSquares.OrdinaryCircleLowTerm
import PrimeSquares.OrdinaryPhysicalLow

open Finset
namespace PrimeSquares

noncomputable def ordinaryCircleLowModel (N Q : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) : C(PrimeCircle, ℂ) :=
  ∑ q ∈ Icc 1 Q,ordinaryCircleLowTerm N Q hN hQ hb q

theorem ordinaryCircleLowModel_kernel (N Q : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (x : ℤ) :
    fourierKernel (ordinaryCircleLowModel N Q hN hQ hb) x=ordinaryPhysicalLowKernel N Q x := by
  rw [ordinaryCircleLowModel,fourierKernel_sum,ordinaryPhysicalLowKernel]
  apply sum_congr rfl
  intro q hq
  have : NeZero q := ⟨by have h := (mem_Icc.mp hq).1;omega⟩
  exact ordinaryCircleLowTerm_kernel N Q hN hQ hb q x

end PrimeSquares
