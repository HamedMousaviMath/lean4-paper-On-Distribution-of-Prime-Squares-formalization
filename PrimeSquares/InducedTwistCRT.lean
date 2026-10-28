import PrimeSquares.TwistedQuadratic

/-!
# CRT for an induced twist and a coprime principal factor

The character is Mathlib's actual `DirichletCharacter.changeLevel`. The
inverse-modulus coefficients in the additive character are retained.
-/

open Finset

namespace PrimeSquares

theorem induced_character_crt_value (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (χ : DirichletCharacter ℂ m) (ab : (ZMod m)ˣ × (ZMod n)ˣ) :
    DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ
      ((crtUnitsEquiv h).symm ab : (ZMod (m * n))ˣ) = χ ab.1 := by
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
  have ht := (crtUnitsEquiv_cast h ((crtUnitsEquiv h).symm ab)).1
  simp only [MulEquiv.apply_symm_apply] at ht
  exact congrArg χ ht.symm

theorem induced_twistedGauss_coprime_mul (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (χ : DirichletCharacter ℂ m) (a : ZMod (m * n)) :
    twistedUnitQuadraticGaussSum (m * n)
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ) a =
      twistedUnitQuadraticGaussSum m χ
        (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) a *
          (((ZMod.unitOfCoprime n h.symm)⁻¹ : (ZMod m)ˣ) : ZMod m)) *
      unitQuadraticGaussSum n
        (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) a *
          (((ZMod.unitOfCoprime m h)⁻¹ : (ZMod n)ˣ) : ZMod n)) := by
  classical
  calc
    _ = ∑ ab : (ZMod m)ˣ × (ZMod n)ˣ,
        DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ
          ((crtUnitsEquiv h).symm ab : (ZMod (m * n))ˣ) *
        ZMod.stdAddChar
          (a * (((crtUnitsEquiv h).symm ab : (ZMod (m * n))ˣ) : ZMod (m * n)) ^ 2) :=
      (Equiv.sum_comp (crtUnitsEquiv h).symm.toEquiv _).symm
    _ = ∑ ab : (ZMod m)ˣ × (ZMod n)ˣ,
        (χ ab.1 * ZMod.stdAddChar
          ((ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) a *
            (((ZMod.unitOfCoprime n h.symm)⁻¹ : (ZMod m)ˣ) : ZMod m)) * (ab.1 : ZMod m) ^ 2)) *
        ZMod.stdAddChar ((ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) a *
            (((ZMod.unitOfCoprime m h)⁻¹ : (ZMod n)ˣ) : ZMod n)) * (ab.2 : ZMod n) ^ 2) := by
      apply sum_congr rfl
      intro ab _
      rw [induced_character_crt_value m n h, stdAddChar_crt m n h]
      have ht := crtUnitsEquiv_cast h ((crtUnitsEquiv h).symm ab)
      simp only [MulEquiv.apply_symm_apply] at ht
      have hm : ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m)
          (a * (((crtUnitsEquiv h).symm ab : (ZMod (m * n))ˣ) : ZMod (m * n)) ^ 2) *
          (((ZMod.unitOfCoprime n h.symm)⁻¹ : (ZMod m)ˣ) : ZMod m) =
          (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) a *
            (((ZMod.unitOfCoprime n h.symm)⁻¹ : (ZMod m)ˣ) : ZMod m)) * (ab.1 : ZMod m) ^ 2 := by
        simp only [map_mul, map_pow, ← ht.1]
        ring
      have hn : ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n)
          (a * (((crtUnitsEquiv h).symm ab : (ZMod (m * n))ˣ) : ZMod (m * n)) ^ 2) *
          (((ZMod.unitOfCoprime m h)⁻¹ : (ZMod n)ˣ) : ZMod n) =
          (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) a *
            (((ZMod.unitOfCoprime m h)⁻¹ : (ZMod n)ˣ) : ZMod n)) * (ab.2 : ZMod n) ^ 2 := by
        simp only [map_mul, map_pow, ← ht.2]
        ring
      rw [hm, hn]
      ring
    _ = _ := by
      simp only [twistedUnitQuadraticGaussSum, unitQuadraticGaussSum]
      rw [Fintype.sum_prod_type, sum_mul_sum]

theorem induced_twistedSquareSum_coprime_mul (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (χ : DirichletCharacter ℂ m) (a : ZMod (m * n)) :
    twistedSquareSum (m * n)
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ) a =
      twistedSquareSum m χ
        (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) a *
          (((ZMod.unitOfCoprime n h.symm)⁻¹ : (ZMod m)ˣ) : ZMod m)) *
      principalSquareSum n
        (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) a *
          (((ZMod.unitOfCoprime m h)⁻¹ : (ZMod n)ˣ) : ZMod n)) := by
  rw [twistedSquareSum, induced_twistedGauss_coprime_mul m n h,
    twistedSquareSum, principalSquareSum_as_unitGauss]
  simp only [map_neg, neg_mul, Nat.totient_mul h, Nat.cast_mul, mul_inv_rev]
  ring

end PrimeSquares
