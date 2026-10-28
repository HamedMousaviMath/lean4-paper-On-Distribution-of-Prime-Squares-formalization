import PrimeSquares.QuadraticCohen

/-!
# Vanishing local factors in the quadratic Cohen identity

Source: `sources/current/Draft5.tex`, proof of `l:cohenquadratic`.

For a square-zero element t of a commutative ring, r -> r + t/r is a
permutation of the units, with inverse r -> r - t/r. It changes r² by 2t.
If 2t is nonzero in ZMod q, reindexing a primitive unit-coefficient quadratic
Gauss sum therefore multiplies it by a phase different from 1, forcing it to
vanish. Fourier expansion transfers the vanishing to C_q(n).

Take t=p^(k-1) for odd p and k>=2, or t=2^(a-2) for a>=4. This proves both
vanishing claims in the paper by one argument, without invoking root lifting.
The final statements use exponents j+2 and j+4 to avoid truncated subtraction.
-/

open Finset

namespace PrimeSquares

/-- The unit r+t/r, with its inverse exhibited explicitly. -/
def squareShiftUnit {R : Type*} [CommRing R] (t : R) (ht : t ^ 2 = 0) (u : Rˣ) : Rˣ where
  val := (u : R) + t * (↑u⁻¹ : R)
  inv := (↑u⁻¹ : R) - t * (↑u⁻¹ : R) ^ 3
  val_inv := by
    calc
      ((u : R) + t * (↑u⁻¹ : R)) * ((↑u⁻¹ : R) - t * (↑u⁻¹ : R) ^ 3) =
          (u : R) * (↑u⁻¹ : R) + t * (↑u⁻¹ : R) ^ 2 *
            (1 - (u : R) * (↑u⁻¹ : R)) - t ^ 2 * (↑u⁻¹ : R) ^ 4 := by ring
      _ = 1 := by rw [u.mul_inv, ht]; ring
  inv_val := by
    calc
      ((↑u⁻¹ : R) - t * (↑u⁻¹ : R) ^ 3) * ((u : R) + t * (↑u⁻¹ : R)) =
          (u : R) * (↑u⁻¹ : R) + t * (↑u⁻¹ : R) ^ 2 *
            (1 - (u : R) * (↑u⁻¹ : R)) - t ^ 2 * (↑u⁻¹ : R) ^ 4 := by ring
      _ = 1 := by rw [u.mul_inv, ht]; ring

/-- The permutation of the units given by the square-zero shift. -/
def squareShiftEquiv {R : Type*} [CommRing R] (t : R) (ht : t ^ 2 = 0) : Equiv.Perm Rˣ where
  toFun := squareShiftUnit t ht
  invFun := squareShiftUnit (-t) (by simpa only [neg_sq] using ht)
  left_inv u := by
    apply Units.ext
    change (u : R) + t * (↑u⁻¹ : R) + (-t) *
      ((↑u⁻¹ : R) - t * (↑u⁻¹ : R) ^ 3) = (u : R)
    calc
      _ = (u : R) + t ^ 2 * (↑u⁻¹ : R) ^ 3 := by ring
      _ = (u : R) := by rw [ht]; ring
  right_inv u := by
    apply Units.ext
    change (u : R) + (-t) * (↑u⁻¹ : R) + t *
      ((↑u⁻¹ : R) - (-t) * (↑u⁻¹ : R) ^ 3) = (u : R)
    calc
      _ = (u : R) + t ^ 2 * (↑u⁻¹ : R) ^ 3 := by ring
      _ = (u : R) := by rw [ht]; ring

/-- This permutation changes every unit square by the same amount, 2t. -/
theorem squareShiftEquiv_sq {R : Type*} [CommRing R] (t : R) (ht : t ^ 2 = 0) (u : Rˣ) :
    ((squareShiftEquiv t ht u : Rˣ) : R) ^ 2 = (u : R) ^ 2 + 2 * t := by
  change ((u : R) + t * (↑u⁻¹ : R)) ^ 2 = _
  calc
    _ = (u : R) ^ 2 + 2 * t * ((u : R) * (↑u⁻¹ : R)) +
        t ^ 2 * (↑u⁻¹ : R) ^ 2 := by ring
    _ = _ := by rw [u.mul_inv, ht]; ring

/-- The unnormalized quadratic exponential sum over units. -/
noncomputable def unitQuadraticGaussSum (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  ∑ u : (ZMod q)ˣ, ZMod.stdAddChar (a * (u : ZMod q) ^ 2)

/-- Reindexing by the shift forces a unit-coefficient Gauss sum to vanish. -/
theorem unitQuadraticGaussSum_eq_zero_of_square_zero (q : ℕ) [NeZero q]
    (t : ZMod q) (ht : t ^ 2 = 0) (h2t : 2 * t ≠ 0)
    (a : ZMod q) (ha : IsUnit a) : unitQuadraticGaussSum q a = 0 := by
  classical
  have hphase : ZMod.stdAddChar (a * (2 * t)) ≠ (1 : ℂ) := by
    intro h
    have hzero : a * (2 * t) = 0 := ZMod.injective_stdAddChar
      (h.trans (AddChar.map_zero_eq_one _).symm)
    exact h2t ((ha.mul_right_eq_zero).mp hzero)
  have hshift : unitQuadraticGaussSum q a =
      ZMod.stdAddChar (a * (2 * t)) * unitQuadraticGaussSum q a := by
    unfold unitQuadraticGaussSum
    calc
      _ = ∑ u : (ZMod q)ˣ,
          ZMod.stdAddChar (a * ((squareShiftEquiv t ht u : (ZMod q)ˣ) : ZMod q) ^ 2) :=
        (Equiv.sum_comp (squareShiftEquiv t ht) _).symm
      _ = ∑ u : (ZMod q)ˣ, ZMod.stdAddChar (a * (2 * t)) *
          ZMod.stdAddChar (a * (u : ZMod q) ^ 2) := by
        apply sum_congr rfl
        intro u _
        rw [squareShiftEquiv_sq, mul_add, AddChar.map_add_eq_mul]
        exact mul_comm _ _
      _ = _ := (mul_sum ..).symm
  have hprod : (ZMod.stdAddChar (a * (2 * t)) - 1) * unitQuadraticGaussSum q a = 0 := by
    rw [sub_mul, one_mul, ← hshift, sub_self]
  rcases mul_eq_zero.mp hprod with h | h
  · exact False.elim (hphase (sub_eq_zero.mp h))
  · exact h

/-- Equivalence of the complete-residue filter and unit-group conventions. -/
theorem sum_unit_filter_eq_sum_units (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    (∑ r : ZMod q, if IsUnit r then f r else 0) = ∑ u : (ZMod q)ˣ, f u := by
  classical
  rw [← sum_filter]
  rw [sum_subtype _ (by simp : ∀ r : ZMod q, r ∈ univ.filter IsUnit ↔ IsUnit r) f]
  exact (Fintype.sum_equiv
    (Submonoid.unitsTypeEquivIsUnitSubmonoid (M := ZMod q)).toEquiv
    (fun u : (ZMod q)ˣ => f u) (fun r => f r) (fun _ => rfl)).symm

/-- Expansion into Gauss sums transfers the vanishing to the Cohen correlation. -/
theorem quadraticRamanujanSum_eq_zero_of_square_zero (q : ℕ) [NeZero q]
    (t : ZMod q) (ht : t ^ 2 = 0) (h2t : 2 * t ≠ 0) (n : ZMod q) :
    quadraticRamanujanSum q n = 0 := by
  classical
  have hGauss (a : (ZMod q)ˣ) :
      (∑ r : (ZMod q)ˣ, ZMod.stdAddChar ((n - (r : ZMod q) ^ 2) * (a : ZMod q))) = 0 := by
    calc
      _ = ZMod.stdAddChar (n * (a : ZMod q)) * unitQuadraticGaussSum q (-(a : ZMod q)) := by
        unfold unitQuadraticGaussSum
        rw [mul_sum]
        apply sum_congr rfl
        intro r _
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      _ = 0 := by
        rw [unitQuadraticGaussSum_eq_zero_of_square_zero q t ht h2t _ a.isUnit.neg,
          mul_zero]
  unfold quadraticRamanujanSum
  rw [sum_unit_filter_eq_sum_units]
  simp_rw [ramanujanSum, sum_unit_filter_eq_sum_units]
  rw [sum_comm]
  exact sum_eq_zero fun a _ => hGauss a

/-- C_(p^k)(n)=0 for all odd primes p, all k>=2, and all residues n. -/
theorem quadraticRamanujanSum_odd_prime_pow (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (k : ℕ) (n : ZMod (p ^ (k + 2))) : quadraticRamanujanSum (p ^ (k + 2)) n = 0 := by
  have hp : p.Prime := Fact.out
  let t : ZMod (p ^ (k + 2)) := (p ^ (k + 1) : ℕ)
  have ht : t ^ 2 = 0 := by
    dsimp [t]
    rw [← Nat.cast_pow, ← pow_mul, ZMod.natCast_eq_zero_iff]
    exact Nat.pow_dvd_pow p (by omega)
  have h2t : 2 * t ≠ 0 := by
    intro h
    have hcast : ((2 * p ^ (k + 1) : ℕ) : ZMod (p ^ (k + 2))) = 0 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    have hq : p ^ (k + 2) = p ^ (k + 1) * p := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    rw [hq, mul_comm 2 (p ^ (k + 1))] at hd
    have hd2 : p ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos hp.pos) hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h2
    · exact hp.ne_one h1
    · exact hp2 h2
  exact quadraticRamanujanSum_eq_zero_of_square_zero _ t ht h2t n

/-- C_(2^a)(n)=0 for every a>=4 and every residue n. -/
theorem quadraticRamanujanSum_two_pow_ge_four (k : ℕ) (n : ZMod (2 ^ (k + 4))) :
    quadraticRamanujanSum (2 ^ (k + 4)) n = 0 := by
  let t : ZMod (2 ^ (k + 4)) := (2 ^ (k + 2) : ℕ)
  have ht : t ^ 2 = 0 := by
    dsimp [t]
    rw [← Nat.cast_pow, ← pow_mul, ZMod.natCast_eq_zero_iff]
    exact Nat.pow_dvd_pow 2 (by omega)
  have h2t : 2 * t ≠ 0 := by
    intro h
    have hp : 2 ^ (k + 3) = 2 * 2 ^ (k + 2) := by
      rw [show k + 3 = (k + 2) + 1 by omega, pow_succ, mul_comm]
    have hcast : ((2 ^ (k + 3) : ℕ) : ZMod (2 ^ (k + 4))) = 0 := by
      rw [hp, Nat.cast_mul, Nat.cast_ofNat]
      exact h
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    exact (Nat.not_dvd_of_pos_of_lt (by positivity)
      (Nat.pow_lt_pow_right (by decide) (by omega : k + 3 < k + 4))) hd
  exact quadraticRamanujanSum_eq_zero_of_square_zero _ t ht h2t n

end PrimeSquares
