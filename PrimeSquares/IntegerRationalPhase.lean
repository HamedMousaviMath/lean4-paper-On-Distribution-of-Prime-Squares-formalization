import PrimeSquares.RealInverseFourierIntegral
import PrimeSquares.FourierGaussCompatibility

namespace PrimeSquares

theorem realFourierPhase_rational (q : ℕ) [NeZero q] (a x : ℤ) :
    realFourierPhase (((a : ℝ)/q)*(x : ℝ))=ZMod.stdAddChar ((a*x : ℤ) : ZMod q) := by
  calc
    _ = (fourier x ((((a : ℝ)/q : ℝ)) : PrimeCircle) : ℂ) :=
      (realFourierPhase_integer_character x _).symm
    _ = negativeFourierCharacter (-x) ((((a : ℝ)/q : ℝ)) : PrimeCircle) := by
      simp only [negativeFourierCharacter,neg_neg]
    _ = ZMod.stdAddChar ((-(a*(-x)) : ℤ) : ZMod q) := negativeFourierCharacter_rational q a (-x)
    _ = _ := by congr 1;push_cast;ring

theorem realFourierPhase_unit_rational (q : ℕ) [NeZero q] (u : (ZMod q)ˣ) (x : ℤ) :
    realFourierPhase ((((u : ZMod q).val : ℝ)/q)*(x : ℝ))=
      ZMod.stdAddChar ((u : ZMod q)*(x : ZMod q)) := by
  simpa only [Int.cast_natCast,Int.cast_mul,ZMod.natCast_zmod_val] using
    realFourierPhase_rational q ((u : ZMod q).val : ℤ) x

end PrimeSquares
