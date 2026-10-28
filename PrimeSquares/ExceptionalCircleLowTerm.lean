import PrimeSquares.OrdinaryCircleLowTerm
import PrimeSquares.InducedIntegerCorrelation

namespace PrimeSquares

noncomputable def exceptionalCircleLowTerm (N Q : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (β : ℝ) (d : ℕ) : C(PrimeCircle, ℂ) :=
  if hd : d=0 then 0 else
    letI : NeZero d := ⟨hd⟩
    let ha : 2 ≤ exceptionalLowWidth N Q (conductorMajorant q₀) d := exceptionalLowWidth_two_le
      (by exact_mod_cast (show 0 < Q by omega)) (conductorMajorant_one_le q₀ (NeZero.pos q₀))
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd)) hb
    ∑ u : (ZMod (q₀*d))ˣ,
      twistedSquareSum (q₀*d) (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ d) χ₀) u •
        circleFrequencyShift (circleAnnularCutoff N hN β (exceptionalLowWidth N Q (conductorMajorant q₀) d) ha)
          (((((u : ZMod (q₀*d)).val : ℝ)/((q₀*d : ℕ) : ℝ)) : ℝ) : PrimeCircle)

theorem exceptionalCircleLowTerm_kernel (N Q : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q₀ d : ℕ) [NeZero q₀] [NeZero d]
    (χ₀ : DirichletCharacter ℂ q₀) (β : ℝ) (x : ℤ) :
    fourierKernel (exceptionalCircleLowTerm N Q hN hQ hb q₀ χ₀ β d) x=
      inducedIntegerCorrelation q₀ χ₀ d x*smoothedAnnularKernel N β (exceptionalLowWidth N Q (conductorMajorant q₀) d) x := by
  simp only [exceptionalCircleLowTerm,dite_eq_right (NeZero.ne d)]
  rw [fourierKernel_sum]
  simp_rw [fourierKernel_smul,circleFrequencyShift_real_kernel,circleAnnularCutoff_kernel,←mul_assoc]
  rw [←Finset.sum_mul,twistedCorrelation_phase_sum,inducedIntegerCorrelation_eq]

theorem exceptionalCircleLowTerm_zero (N Q : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hb : 2*(Q : ℝ) ≤ (N : ℝ)^2) (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀) (β : ℝ) :
    exceptionalCircleLowTerm N Q hN hQ hb q₀ χ₀ β 0=0 := by simp [exceptionalCircleLowTerm]

end PrimeSquares
