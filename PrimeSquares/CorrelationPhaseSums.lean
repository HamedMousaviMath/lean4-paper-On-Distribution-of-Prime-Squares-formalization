import PrimeSquares.IntegerRationalPhase
import PrimeSquares.NormalizedCohenCorrelation

namespace PrimeSquares

theorem normalizedCohenCorrelation_phase_sum (q : ℕ) [NeZero q] (x : ℤ) :
    (∑ u : (ZMod q)ˣ,principalSquareSum q u*
      realFourierPhase ((((u : ZMod q).val : ℝ)/q)*(x : ℝ)))=normalizedCohenCorrelation q x := by
  simp_rw [realFourierPhase_unit_rational]
  rw [normalizedCohenCorrelation_principal,twistedSquareCorrelation]
  simp only [twistedSquareSum_principal]

theorem twistedCorrelation_phase_sum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℤ) :
    (∑ u : (ZMod q)ˣ,twistedSquareSum q χ u*
      realFourierPhase ((((u : ZMod q).val : ℝ)/q)*(x : ℝ)))=twistedSquareCorrelation q χ (x : ZMod q) := by
  simp_rw [realFourierPhase_unit_rational]
  rfl

end PrimeSquares
