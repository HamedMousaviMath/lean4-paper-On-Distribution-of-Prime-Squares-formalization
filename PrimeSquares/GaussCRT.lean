import PrimeSquares.PrincipalGauss
import PrimeSquares.RamanujanCRT

/-!
# CRT for the actual principal quadratic Gauss sum

The standard character introduces inverse-modulus coefficients. These are
retained explicitly rather than assuming unscaled multiplicativity at fixed a.
-/

open Finset

namespace PrimeSquares

theorem stdAddChar_crt (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (x : ZMod (m * n)) :
    ZMod.stdAddChar x =
      ZMod.stdAddChar (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) x *
        (((ZMod.unitOfCoprime n h.symm)⁻¹ : (ZMod m)ˣ) : ZMod m)) *
      ZMod.stdAddChar (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) x *
        (((ZMod.unitOfCoprime m h)⁻¹ : (ZMod n)ˣ) : ZMod n)) := by
  have he := crtUnitsEquiv_scaled_phase h (ZMod.unitOfCoprime n h.symm)⁻¹
    (ZMod.unitOfCoprime m h)⁻¹ x
  dsimp only at he
  have hone : (crtUnitsEquiv h).symm ((1 : (ZMod m)ˣ), (1 : (ZMod n)ˣ)) = 1 :=
    (crtUnitsEquiv h).symm.map_one
  simpa only [mul_inv_cancel, hone, Units.val_one, mul_one] using he

theorem unitQuadraticGaussSum_coprime_mul (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (a : ZMod (m * n)) :
    unitQuadraticGaussSum (m * n) a =
      unitQuadraticGaussSum m
        (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) a *
          (((ZMod.unitOfCoprime n h.symm)⁻¹ : (ZMod m)ˣ) : ZMod m)) *
      unitQuadraticGaussSum n
        (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) a *
          (((ZMod.unitOfCoprime m h)⁻¹ : (ZMod n)ˣ) : ZMod n)) := by
  classical
  calc
    _ = ∑ ab : (ZMod m)ˣ × (ZMod n)ˣ, ZMod.stdAddChar
        (a * (((crtUnitsEquiv h).symm ab : (ZMod (m * n))ˣ) : ZMod (m * n)) ^ 2) := by
      exact (Equiv.sum_comp (crtUnitsEquiv h).symm.toEquiv _).symm
    _ = ∑ ab : (ZMod m)ˣ × (ZMod n)ˣ,
        ZMod.stdAddChar ((ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) a *
            (((ZMod.unitOfCoprime n h.symm)⁻¹ : (ZMod m)ˣ) : ZMod m)) * (ab.1 : ZMod m) ^ 2) *
        ZMod.stdAddChar ((ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) a *
            (((ZMod.unitOfCoprime m h)⁻¹ : (ZMod n)ˣ) : ZMod n)) * (ab.2 : ZMod n) ^ 2) := by
      apply sum_congr rfl
      intro ab _
      rw [stdAddChar_crt m n h]
      have ht := crtUnitsEquiv_cast h ((crtUnitsEquiv h).symm ab)
      simp only [MulEquiv.apply_symm_apply] at ht
      simp only [map_mul, map_pow, ← ht.1, ← ht.2]
      congr 1 <;> congr 1 <;> ring
    _ = _ := by
      simp only [unitQuadraticGaussSum]
      rw [Fintype.sum_prod_type, sum_mul_sum]

theorem principalSquareSum_coprime_mul (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (a : ZMod (m * n)) :
    principalSquareSum (m * n) a =
      principalSquareSum m
        (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) a *
          (((ZMod.unitOfCoprime n h.symm)⁻¹ : (ZMod m)ˣ) : ZMod m)) *
      principalSquareSum n
        (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) a *
          (((ZMod.unitOfCoprime m h)⁻¹ : (ZMod n)ˣ) : ZMod n)) := by
  rw [principalSquareSum_as_unitGauss, unitQuadraticGaussSum_coprime_mul m n h,
    principalSquareSum_as_unitGauss, principalSquareSum_as_unitGauss]
  simp only [map_neg, neg_mul, Nat.totient_mul h, Nat.cast_mul, mul_inv_rev]
  ring

theorem scaled_norm_principalSquareSum_coprime_mul (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (a : ZMod (m * n)) :
    Real.sqrt (m * n : ℕ) * ‖principalSquareSum (m * n) a‖ =
      (Real.sqrt m * ‖principalSquareSum m
        (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) a *
          (((ZMod.unitOfCoprime n h.symm)⁻¹ : (ZMod m)ˣ) : ZMod m))‖) *
      (Real.sqrt n * ‖principalSquareSum n
        (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) a *
          (((ZMod.unitOfCoprime m h)⁻¹ : (ZMod n)ˣ) : ZMod n))‖) := by
  rw [principalSquareSum_coprime_mul m n h, norm_mul, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg m)]
  ring

end PrimeSquares
