import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.Ring

/-!
# The finite sums in the quadratic Cohen identity

Source: `sources/current/Draft5.tex`, `l:cohenquadratic`, Section 3.
The definitions use the actual standard complex additive character, rather than
an unevaluated hypothesis or a replacement integer model of a Ramanujan sum.
This module starts with the odd-prime factor. The full composite-modulus formula
and its uniform bound are assembled in `PrimeSquares.CohenProduct`.
-/

open Finset

namespace PrimeSquares

/-- The Ramanujan sum, with a complete residue system filtered by units. -/
noncomputable def ramanujanSum (q : ℕ) [NeZero q] (m : ZMod q) : ℂ :=
  ∑ a : ZMod q, if IsUnit a then ZMod.stdAddChar (m * a) else 0

/-- `C_q(n)`, the Ramanujan correlation over square shifts by units. -/
noncomputable def quadraticRamanujanSum (q : ℕ) [NeZero q] (n : ZMod q) : ℂ :=
  ∑ r : ZMod q, if IsUnit r then ramanujanSum q (n - r ^ 2) else 0

/-- Orthogonality of the standard additive character on a cyclic group. -/
theorem sum_stdAddChar_mul (q : ℕ) [NeZero q] (m : ZMod q) :
    (∑ a : ZMod q, ZMod.stdAddChar (m * a)) = if m = 0 then (q : ℂ) else 0 := by
  split_ifs with h
  · simp [h, AddChar.map_zero_eq_one, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q h)

/-- The prime-modulus Ramanujan sum, proved from the exponential definition. -/
theorem ramanujanSum_prime (p : ℕ) [Fact p.Prime] (m : ZMod p) :
    ramanujanSum p m = if m = 0 then (p : ℂ) - 1 else -1 := by
  classical
  have term (a : ZMod p) :
      (if IsUnit a then ZMod.stdAddChar (m * a) else 0) =
        ZMod.stdAddChar (m * a) - if a = 0 then 1 else 0 := by
    by_cases ha : a = 0
    · simp [ha, AddChar.map_zero_eq_one]
    · simp [isUnit_iff_ne_zero, ha]
  simp_rw [ramanujanSum, term]
  rw [sum_sub_distrib, sum_stdAddChar_mul]
  simp only [sum_ite_eq', mem_univ, ite_true]
  split_ifs <;> ring

/-- An intermediate identity in terms of the number of all square roots. -/
theorem quadraticRamanujanSum_prime_root_count (p : ℕ) [Fact p.Prime] (n : ZMod p) :
    quadraticRamanujanSum p n =
      (p : ℂ) * ((univ.filter fun r : ZMod p => r ^ 2 = n).card : ℂ) -
        (p : ℂ) - ramanujanSum p n := by
  classical
  have term (r : ZMod p) :
      (if IsUnit r then ramanujanSum p (n - r ^ 2) else 0) =
        ((p : ℂ) * (if r ^ 2 = n then 1 else 0) - 1) -
          if r = 0 then ramanujanSum p n else 0 := by
    by_cases hr : r = 0
    · subst r
      simp only [not_isUnit_zero, ↓reduceIte, zero_pow (by decide : 2 ≠ 0)]
      rw [ramanujanSum_prime]
      by_cases hn : n = 0 <;> simp [hn, eq_comm]
    · rw [ite_eq_left (isUnit_iff_ne_zero.mpr hr), ite_eq_right hr, sub_zero,
        ramanujanSum_prime]
      by_cases h : r ^ 2 = n
      · simp [h]
      · have h' : n - r ^ 2 ≠ 0 := by simpa [sub_eq_zero, eq_comm] using h
        simp [h, h']
  simp_rw [quadraticRamanujanSum, term]
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum]
  simp

/-- The odd-prime factor in Draft5, equation `e:Cp`. -/
theorem quadraticRamanujanSum_odd_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (n : ℤ) :
    quadraticRamanujanSum p (n : ZMod p) =
      if legendreSym p n = 1 then (p : ℂ) + 1 else 1 - (p : ℂ) := by
  classical
  have hroots : ((univ.filter fun r : ZMod p => r ^ 2 = (n : ZMod p)).card : ℂ) =
      (legendreSym p n : ℂ) + 1 := by
    have h : ((univ.filter fun r : ZMod p => r ^ 2 = (n : ZMod p)).card : ℤ) =
        legendreSym p n + 1 := by
      simpa only [Set.toFinset_ofPred] using legendreSym.card_sqrts p hp n
    exact_mod_cast h
  rw [quadraticRamanujanSum_prime_root_count, hroots, ramanujanSum_prime]
  by_cases hn : (n : ZMod p) = 0
  · have hχ : legendreSym p n = 0 := (legendreSym.eq_zero_iff p n).mpr hn
    simp [hn, hχ]
  · rw [ite_eq_right hn]
    rcases legendreSym.eq_one_or_neg_one p hn with hχ | hχ <;> simp [hχ] <;> ring

/-- When every unit square is one, the correlation is a constant sum. -/
theorem quadraticRamanujanSum_of_unit_sq_one (q : ℕ) [NeZero q]
    (h : ∀ r : ZMod q, IsUnit r → r ^ 2 = 1) (n : ZMod q) :
    quadraticRamanujanSum q n =
      ((univ.filter fun r : ZMod q => IsUnit r).card : ℂ) * ramanujanSum q (n - 1) := by
  classical
  unfold quadraticRamanujanSum
  have term (r : ZMod q) :
      (if IsUnit r then ramanujanSum q (n - r ^ 2) else 0) =
        if IsUnit r then ramanujanSum q (n - 1) else 0 := by
    split_ifs with hr
    · rw [h r hr]
    · rfl
  simp_rw [term]
  rw [← sum_filter]
  simp

/-- Modulus one, including its unit and additive-character conventions. -/
theorem quadraticRamanujanSum_one (n : ZMod 1) : quadraticRamanujanSum 1 n = 1 := by
  have hu (r : ZMod 1) : IsUnit r := by
    rw [Subsingleton.elim r 1]
    exact isUnit_one
  have he (r : ZMod 1) : ZMod.stdAddChar r = (1 : ℂ) := by
    rw [Subsingleton.elim r 0, AddChar.map_zero_eq_one]
  have hc (m : ZMod 1) : ramanujanSum 1 m = 1 := by
    unfold ramanujanSum
    rw [Fintype.sum_unique, ite_eq_left (hu _), he]
  unfold quadraticRamanujanSum
  rw [Fintype.sum_unique, ite_eq_left (hu _), hc]

/-- The factor at 2, stated on residues; this is the parity factor in `e:Ta`. -/
theorem quadraticRamanujanSum_two (n : ZMod 2) :
    quadraticRamanujanSum 2 n = if n = 1 then 1 else -1 := by
  classical
  rw [quadraticRamanujanSum_of_unit_sq_one 2 (by decide)]
  have hcard : (univ.filter fun r : ZMod 2 => IsUnit r).card = 1 := by decide
  rw [hcard]
  simp only [Nat.cast_one, one_mul, ramanujanSum_prime]
  norm_num [sub_eq_zero]

/-- The factor at 4 before applying the prime-power Ramanujan evaluation. -/
theorem quadraticRamanujanSum_four (n : ZMod 4) :
    quadraticRamanujanSum 4 n = 2 * ramanujanSum 4 (n - 1) := by
  classical
  rw [quadraticRamanujanSum_of_unit_sq_one 4 (by decide)]
  have hcard : (univ.filter fun r : ZMod 4 => IsUnit r).card = 2 := by decide
  rw [hcard]
  norm_num

/-- The factor at 8 before applying the prime-power Ramanujan evaluation. -/
theorem quadraticRamanujanSum_eight (n : ZMod 8) :
    quadraticRamanujanSum 8 n = 4 * ramanujanSum 8 (n - 1) := by
  classical
  rw [quadraticRamanujanSum_of_unit_sq_one 8 (by decide)]
  have hcard : (univ.filter fun r : ZMod 8 => IsUnit r).card = 4 := by decide
  rw [hcard]
  norm_num

end PrimeSquares
