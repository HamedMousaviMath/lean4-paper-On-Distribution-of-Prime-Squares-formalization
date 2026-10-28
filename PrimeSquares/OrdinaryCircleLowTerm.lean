import PrimeSquares.CircleFrequencyShiftKernel
import PrimeSquares.CorrelationPhaseSums
import PrimeSquares.LowWidthLowerBounds
import PrimeSquares.FourierKernelSums

namespace PrimeSquares

noncomputable def ordinaryCircleLowTerm (N Q : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q : ℕ) : C(PrimeCircle, ℂ) :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    let ha : 2 ≤ ordinaryLowWidth N Q q := ordinaryLowWidth_two_le
      (by exact_mod_cast (show 0 < Q by omega))
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hq)) hb
    ∑ u : (ZMod q)ˣ,principalSquareSum q u •
      circleFrequencyShift (circleAnnularCutoff N hN 1 (ordinaryLowWidth N Q q) ha)
        (((((u : ZMod q).val : ℝ)/q) : ℝ) : PrimeCircle)

theorem ordinaryCircleLowTerm_kernel (N Q : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q : ℕ) [NeZero q] (x : ℤ) :
    fourierKernel (ordinaryCircleLowTerm N Q hN hQ hb q) x=
      normalizedCohenCorrelation q x*smoothedAnnularKernel N 1 (ordinaryLowWidth N Q q) x := by
  simp only [ordinaryCircleLowTerm,dite_eq_right (NeZero.ne q)]
  rw [fourierKernel_sum]
  simp_rw [fourierKernel_smul,circleFrequencyShift_real_kernel,circleAnnularCutoff_kernel,←mul_assoc]
  rw [←Finset.sum_mul,normalizedCohenCorrelation_phase_sum]

theorem ordinaryCircleLowTerm_zero (N Q : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) : ordinaryCircleLowTerm N Q hN hQ hb 0=0 := by
  simp [ordinaryCircleLowTerm]

end PrimeSquares
