import PrimeSquares.TwistedQuadratic

/-!
# Exact cancellation for real character twists

Source: Lemma 3.27, `l:exceptionalarithmetic`.

The square-zero permutation from `UnitSquareShift` preserves a quadratic
character if its displacement is twice another square-zero element. This
proves vanishing directly at any modulus divisible by an odd prime square
or by 64, without assuming a classification of primitive real characters.
-/

open Finset

namespace PrimeSquares

theorem dirichletCharacter_quadratic_iff_real (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) : χ.IsQuadratic ↔ ∀ a, star (χ a) = χ a := by
  constructor
  · intro hχ a
    rcases hχ a with h | h | h <;> simp [h]
  · intro hχ
    have hi : χ⁻¹ = χ := by
      rw [← MulChar.star_eq_inv]
      ext a
      exact hχ a
    apply MulChar.isQuadratic_iff_sq_eq_one.mpr
    calc
      χ ^ 2 = χ⁻¹ * χ := by rw [hi, pow_two]
      _ = 1 := inv_mul_cancel χ

theorem quadratic_character_changeLevel {m n : ℕ} (h : m ∣ n)
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) :
    (DirichletCharacter.changeLevel h χ).IsQuadratic := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  rw [← map_pow, hχ.sq_eq_one, map_one]

theorem quadratic_character_unit_square {R : Type*} [CommRing R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) (v : Rˣ) : χ ((v : R) ^ 2) = 1 := by
  rw [map_pow, ← MulChar.pow_apply_coe, hχ.sq_eq_one, MulChar.one_apply_coe]

/-- The shift is multiplication by a unit square when t=2s and s²=0. -/
theorem squareShiftEquiv_eq_mul_square {R : Type*} [CommRing R]
    (t s : R) (ht : t ^ 2 = 0) (hs : s ^ 2 = 0) (hst : 2 * s = t) (u : Rˣ) :
    ∃ v : Rˣ, squareShiftEquiv t ht u = u * v ^ 2 := by
  let z : R := s * (↑u⁻¹ : R) ^ 2
  have hz : z ^ 2 = 0 := by simp only [z, mul_pow, hs, zero_mul]
  let v : Rˣ := squareShiftUnit z hz 1
  refine ⟨v, Units.ext ?_⟩
  change (u : R) + t * (↑u⁻¹ : R) = (u : R) * (1 + z * 1) ^ 2
  dsimp only [z]
  calc
    _ = (u : R) + 2 * s * (↑u⁻¹ : R) := by rw [hst]
    _ = (u : R) * (1 + (s * (↑u⁻¹ : R) ^ 2) * 1) ^ 2 := by
      calc
        _ = (u : R) + 2 * s * (↑u⁻¹ : R) * ((u : R) * (↑u⁻¹ : R)) +
            s ^ 2 * (u : R) * (↑u⁻¹ : R) ^ 4 := by rw [u.mul_inv, hs]; ring
        _ = _ := by ring

theorem quadratic_character_squareShift {R : Type*} [CommRing R]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic)
    (t s : R) (ht : t ^ 2 = 0) (hs : s ^ 2 = 0) (hst : 2 * s = t) (u : Rˣ) :
    χ ((squareShiftEquiv t ht u : Rˣ) : R) = χ u := by
  obtain ⟨v, hv⟩ := squareShiftEquiv_eq_mul_square t s ht hs hst u
  rw [hv, Units.val_mul, Units.val_pow_eq_pow_val, map_mul,
    quadratic_character_unit_square χ hχ, mul_one]

theorem twistedGauss_eq_zero_of_quadratic_shift (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic)
    (t s : ZMod q) (ht : t ^ 2 = 0) (hs : s ^ 2 = 0) (hst : 2 * s = t)
    (h2t : 2 * t ≠ 0) (a : ZMod q) (ha : IsUnit a) :
    twistedUnitQuadraticGaussSum q χ a = 0 := by
  classical
  have hphase : ZMod.stdAddChar (a * (2 * t)) ≠ (1 : ℂ) := by
    intro h
    have hzero : a * (2 * t) = 0 := ZMod.injective_stdAddChar
      (h.trans (AddChar.map_zero_eq_one _).symm)
    exact h2t ((ha.mul_right_eq_zero).mp hzero)
  have hshift : twistedUnitQuadraticGaussSum q χ a =
      ZMod.stdAddChar (a * (2 * t)) * twistedUnitQuadraticGaussSum q χ a := by
    unfold twistedUnitQuadraticGaussSum
    calc
      _ = ∑ u : (ZMod q)ˣ,
          χ ((squareShiftEquiv t ht u : (ZMod q)ˣ) : ZMod q) *
          ZMod.stdAddChar (a * ((squareShiftEquiv t ht u : (ZMod q)ˣ) : ZMod q) ^ 2) :=
        (Equiv.sum_comp (squareShiftEquiv t ht) _).symm
      _ = ∑ u : (ZMod q)ˣ, ZMod.stdAddChar (a * (2 * t)) *
          (χ u * ZMod.stdAddChar (a * (u : ZMod q) ^ 2)) := by
        apply sum_congr rfl
        intro u _
        rw [quadratic_character_squareShift χ hχ t s ht hs hst,
          squareShiftEquiv_sq, mul_add, AddChar.map_add_eq_mul]
        ring
      _ = _ := (mul_sum ..).symm
  exact eq_zero_of_mul_eq_self_left hphase hshift.symm

/-- An odd character cancels against r -> -r, at every coefficient. -/
theorem twistedGauss_eq_zero_of_odd (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ (-1) ≠ 1) (a : ZMod q) :
    twistedUnitQuadraticGaussSum q χ a = 0 := by
  have he := twistedUnitQuadraticGaussSum_mul_unit_sq q χ a (-1)
  simp only [Units.val_neg, Units.val_one, neg_one_sq, mul_one] at he
  exact eq_zero_of_mul_eq_self_left hχ he

/-- The odd-prime-square obstruction holds at the full modulus, without CRT. -/
theorem twistedGauss_odd_prime_square (q p : ℕ) [NeZero q]
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ^ 2 ∣ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic)
    (a : ZMod q) (ha : IsUnit a) : twistedUnitQuadraticGaussSum q χ a = 0 := by
  obtain ⟨m, hm⟩ := hd
  have hmpos : 0 < m := by
    have := NeZero.pos q
    rw [hm] at this
    exact Nat.pos_of_mul_pos_left this
  obtain ⟨c, hc⟩ := hp.odd_of_ne_two hp2
  have h2c : 2 * (c + 1) = p + 1 := by omega
  have hqzero : (p : ZMod q) ^ 2 * (m : ZMod q) = 0 := by
    have hz : ((p ^ 2 * m : ℕ) : ZMod q) = 0 := by rw [← hm, ZMod.natCast_self]
    simpa only [Nat.cast_mul, Nat.cast_pow] using hz
  let t : ZMod q := (p : ZMod q) * (m : ZMod q)
  let s : ZMod q := ((c + 1 : ℕ) : ZMod q) * t
  have ht : t ^ 2 = 0 := by
    calc
      _ = ((p : ZMod q) ^ 2 * (m : ZMod q)) * (m : ZMod q) := by dsimp [t]; ring
      _ = 0 := by rw [hqzero, zero_mul]
  have hs : s ^ 2 = 0 := by simp only [s, mul_pow, ht, mul_zero]
  have hst : 2 * s = t := by
    have he : (2 : ZMod q) * ((c + 1 : ℕ) : ZMod q) = (p : ZMod q) + 1 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using
        congrArg (fun n : ℕ => (n : ZMod q)) h2c
    calc
      _ = ((p : ZMod q) + 1) * t := by dsimp only [s]; rw [← mul_assoc, he]
      _ = (p : ZMod q) ^ 2 * (m : ZMod q) + t := by dsimp only [t]; ring
      _ = t := by rw [hqzero, zero_add]
  have h2t : 2 * t ≠ 0 := by
    intro he
    have hz : ((2 * p * m : ℕ) : ZMod q) = 0 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc, t] using he
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    have hlt : 2 * p * m < q := by
      rw [hm]
      exact Nat.mul_lt_mul_of_pos_right (by nlinarith) hmpos
    exact Nat.not_dvd_of_pos_of_lt (by positivity) hlt hd
  exact twistedGauss_eq_zero_of_quadratic_shift q χ hχ t s ht hs hst h2t a ha

/-- A factor 64 forces cancellation for every quadratic character. -/
theorem twistedGauss_sixtyfour_dvd (q : ℕ) [NeZero q] (hd : 64 ∣ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic)
    (a : ZMod q) (ha : IsUnit a) : twistedUnitQuadraticGaussSum q χ a = 0 := by
  obtain ⟨m, hm⟩ := hd
  have hmpos : 0 < m := by
    have := NeZero.pos q
    rw [hm] at this
    exact Nat.pos_of_mul_pos_left this
  have hqzero : (64 : ZMod q) * (m : ZMod q) = 0 := by
    have hz : ((64 * m : ℕ) : ZMod q) = 0 := by rw [← hm, ZMod.natCast_self]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hz
  let t : ZMod q := 16 * (m : ZMod q)
  let s : ZMod q := 8 * (m : ZMod q)
  have ht : t ^ 2 = 0 := by
    calc
      _ = (64 * (m : ZMod q)) * (4 * (m : ZMod q)) := by dsimp only [t]; ring
      _ = 0 := by rw [hqzero, zero_mul]
  have hs : s ^ 2 = 0 := by
    calc
      _ = (64 * (m : ZMod q)) * (m : ZMod q) := by dsimp only [s]; ring
      _ = 0 := by rw [hqzero, zero_mul]
  have hst : 2 * s = t := by dsimp only [s, t]; ring
  have h2t : 2 * t ≠ 0 := by
    intro he
    have hz : ((32 * m : ℕ) : ZMod q) = 0 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, t, show (32 : ZMod q) = 2 * 16 by ring,
        mul_assoc] using he
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
    exact Nat.not_dvd_of_pos_of_lt (by positivity) (by omega : 32 * m < q) hd
  exact twistedGauss_eq_zero_of_quadratic_shift q χ hχ t s ht hs hst h2t a ha

theorem twistedSquareSum_odd_prime_square (q p : ℕ) [NeZero q]
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ^ 2 ∣ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic)
    (a : ZMod q) (ha : IsUnit a) : twistedSquareSum q χ a = 0 := by
  rw [twistedSquareSum, twistedGauss_odd_prime_square q p hp hp2 hd χ hχ (-a) ha.neg,
    mul_zero]

theorem twistedSquareSum_sixtyfour_dvd (q : ℕ) [NeZero q] (hd : 64 ∣ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic)
    (a : ZMod q) (ha : IsUnit a) : twistedSquareSum q χ a = 0 := by
  rw [twistedSquareSum, twistedGauss_sixtyfour_dvd q hd χ hχ (-a) ha.neg, mul_zero]

theorem twistedSquareSum_eq_zero_of_odd (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ (-1) ≠ 1) (a : ZMod q) :
    twistedSquareSum q χ a = 0 := by
  rw [twistedSquareSum, twistedGauss_eq_zero_of_odd q χ hχ, mul_zero]

end PrimeSquares
