import PrimeSquares.SquareFourier
import PrimeSquares.TwistedQuadratic

/-!
# Compatibility with the arithmetic Gauss-sum convention

At rational circle frequencies the negative Fourier character is exactly
the standard ZMod additive character with a minus sign. The principal and
twisted Gauss sums already proved in Section 3 therefore have the same phase
and totient normalization as the analytic Fourier symbols.
-/

open Finset

namespace PrimeSquares

theorem negativeFourierCharacter_rational (q : ℕ) [NeZero q] (a n : ℤ) :
    negativeFourierCharacter n (((a : ℝ) / q : ℝ) : PrimeCircle) =
      ZMod.stdAddChar ((-(a*n) : ℤ) : ZMod q) := by
  rw [negativeFourierCharacter_real, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

theorem negativeSquareCharacter_rational (q : ℕ) [NeZero q] (a : ℤ) (n : ℕ) :
    negativeFourierCharacter ((n : ℤ)^2) (((a : ℝ) / q : ℝ) : PrimeCircle) =
      ZMod.stdAddChar (-((a : ZMod q) * (n : ZMod q)^2)) := by
  rw [negativeFourierCharacter_rational]
  congr 1
  push_cast
  rfl

theorem principalSquareSum_negativeFourier (q : ℕ) [NeZero q] (a : ℤ) :
    principalSquareSum q (a : ZMod q) = (q.totient : ℂ)⁻¹ *
      ∑ u : (ZMod q)ˣ, negativeFourierCharacter (((u : ZMod q).val : ℤ)^2)
        (((a : ℝ) / q : ℝ) : PrimeCircle) := by
  simp only [principalSquareSum, negativeSquareCharacter_rational, ZMod.natCast_zmod_val]

theorem twistedSquareSum_negativeFourier (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ℤ) :
    twistedSquareSum q χ (a : ZMod q) = (q.totient : ℂ)⁻¹ *
      ∑ u : (ZMod q)ˣ, χ u * negativeFourierCharacter (((u : ZMod q).val : ℤ)^2)
        (((a : ℝ) / q : ℝ) : PrimeCircle) := by
  simp only [twistedSquareSum, twistedUnitQuadraticGaussSum,
    negativeSquareCharacter_rational, ZMod.natCast_zmod_val, neg_mul]

end PrimeSquares
