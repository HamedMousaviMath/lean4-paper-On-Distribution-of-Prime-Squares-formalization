import PrimeSquares.CohenProduct

/-!
# Linear Cohen identity

Elementary input to Draft5, Lemma 3.11 (`l:progressioncohen`). The Ramanujan
sum at a unit equals the Möbius function. Fourier expansion then evaluates
its linear correlation over all units. The square-zero translation below
also supplies the cancellation needed when the progression modulus and its
complement share a prime factor.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace PrimeSquares

/-- Translation by a square-zero element preserves the units. -/
def nilpotentAddUnit {R : Type*} [CommRing R] (t : R) (ht : t ^ 2 = 0) (u : Rˣ) : Rˣ where
  val := (u : R) + t
  inv := (↑u⁻¹ : R) - t * (↑u⁻¹ : R) ^ 2
  val_inv := by
    calc
      _ = (u : R) * (↑u⁻¹ : R) + t * (↑u⁻¹ : R) *
          (1 - (u : R) * (↑u⁻¹ : R)) - t ^ 2 * (↑u⁻¹ : R) ^ 2 := by ring
      _ = 1 := by rw [u.mul_inv, ht]; ring
  inv_val := by
    calc
      _ = (u : R) * (↑u⁻¹ : R) + t * (↑u⁻¹ : R) *
          (1 - (u : R) * (↑u⁻¹ : R)) - t ^ 2 * (↑u⁻¹ : R) ^ 2 := by ring
      _ = 1 := by rw [u.mul_inv, ht]; ring

/-- The inverse translation is translation by -t. -/
def nilpotentAddEquiv {R : Type*} [CommRing R] (t : R) (ht : t ^ 2 = 0) : Equiv.Perm Rˣ where
  toFun := nilpotentAddUnit t ht
  invFun := nilpotentAddUnit (-t) (by simpa only [neg_sq] using ht)
  left_inv u := by apply Units.ext; change (u : R) + t + -t = (u : R); ring
  right_inv u := by apply Units.ext; change (u : R) + -t + t = (u : R); ring

/-- A nontrivial square-zero translation forces the primitive linear sum to vanish. -/
theorem ramanujanSum_one_eq_zero_of_square_zero (q : ℕ) [NeZero q]
    (t : ZMod q) (ht : t ^ 2 = 0) (hnt : t ≠ 0) : ramanujanSum q 1 = 0 := by
  classical
  have hphase : ZMod.stdAddChar t ≠ (1 : ℂ) := by
    intro h
    exact hnt (ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one _).symm))
  have hshift : ramanujanSum q 1 = ZMod.stdAddChar t * ramanujanSum q 1 := by
    simp only [ramanujanSum, sum_unit_filter_eq_sum_units, one_mul]
    calc
      _ = ∑ u : (ZMod q)ˣ,
          ZMod.stdAddChar ((nilpotentAddEquiv t ht u : (ZMod q)ˣ) : ZMod q) :=
        (Equiv.sum_comp (nilpotentAddEquiv t ht) _).symm
      _ = ∑ u : (ZMod q)ˣ, ZMod.stdAddChar t * ZMod.stdAddChar (u : ZMod q) := by
        apply sum_congr rfl
        intro u _
        change ZMod.stdAddChar ((u : ZMod q) + t) = _
        rw [AddChar.map_add_eq_mul, mul_comm]
      _ = _ := (mul_sum ..).symm
  have hprod : (ZMod.stdAddChar t - 1) * ramanujanSum q 1 = 0 := by
    rw [sub_mul, one_mul, ← hshift, sub_self]
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hphase)

/-- Ramanujan sums at one vanish at every prime power of exponent at least two. -/
theorem ramanujanSum_one_prime_pow (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ramanujanSum (p ^ (k + 2)) 1 = 0 := by
  have hp : p.Prime := Fact.out
  let t : ZMod (p ^ (k + 2)) := (p ^ (k + 1) : ℕ)
  have ht : t ^ 2 = 0 := by
    dsimp [t]
    rw [← Nat.cast_pow, ← pow_mul, ZMod.natCast_eq_zero_iff]
    exact Nat.pow_dvd_pow p (by omega)
  have hnt : t ≠ 0 := by
    dsimp [t]
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (Nat.pow_pos hp.pos)
      (Nat.pow_lt_pow_right hp.one_lt (by omega : k + 1 < k + 2))
  exact ramanujanSum_one_eq_zero_of_square_zero _ t ht hnt

/-- The actual unit sum, with a zero extension only for the induction interface. -/
noncomputable def ramanujanAtOne (q : ℕ) : ℂ :=
  if h : q = 0 then 0 else
    letI : NeZero q := ⟨h⟩
    ramanujanSum q 1

theorem ramanujanAtOne_eq (q : ℕ) [NeZero q] :
    ramanujanAtOne q = ramanujanSum q 1 := by
  simp [ramanujanAtOne, NeZero.ne q]

theorem ramanujanAtOne_mul (m n : ℕ) (h : m.Coprime n) :
    ramanujanAtOne (m * n) = ramanujanAtOne m * ramanujanAtOne n := by
  by_cases hm : m = 0
  · simp [hm, ramanujanAtOne]
  by_cases hn : n = 0
  · simp [hn, ramanujanAtOne]
  have : NeZero m := ⟨hm⟩
  have : NeZero n := ⟨hn⟩
  simp only [ramanujanAtOne_eq]
  simpa only [map_one] using ramanujanSum_coprime_mul m n h 1

/-- Evaluation at one, proved from local sums and CRT, not assumed as a formula. -/
theorem ramanujanAtOne_eq_moebius (q : ℕ) : ramanujanAtOne q = (μ q : ℂ) := by
  refine Nat.recOnPosPrimePosCoprime (motive := fun q => ramanujanAtOne q = (μ q : ℂ))
    ?_ ?_ ?_ ?_ q
  · intro p k hp hk
    have : Fact p.Prime := ⟨hp⟩
    rw [ArithmeticFunction.moebius_apply_prime_pow hp hk.ne']
    by_cases hk1 : k = 1
    · subst k
      simp only [pow_one, ramanujanAtOne_eq, ramanujanSum_prime,
        Int.cast_ite, Int.cast_neg, Int.cast_one, Int.cast_zero]
      simp [show (1 : ZMod p) ≠ 0 from one_ne_zero]
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 2 := ⟨k - 2, by omega⟩
      rw [ramanujanAtOne_eq, ramanujanSum_one_prime_pow]
      simp
  · simp [ramanujanAtOne]
  · rw [ramanujanAtOne_eq, ArithmeticFunction.moebius_apply_one, Int.cast_one]
    have hu (r : ZMod 1) : IsUnit r := by
      rw [Subsingleton.elim r 1]
      exact isUnit_one
    have he (r : ZMod 1) : ZMod.stdAddChar r = (1 : ℂ) := by
      rw [Subsingleton.elim r 0, AddChar.map_zero_eq_one]
    unfold ramanujanSum
    rw [Fintype.sum_unique, ite_eq_left (hu _), he]
  · intro a b _ _ h ha hb
    rw [ramanujanAtOne_mul a b h, ha, hb,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, Int.cast_mul]

/-- A Ramanujan sum at any unit coefficient is the Möbius function. -/
theorem ramanujanSum_unit_eq_moebius (q : ℕ) [NeZero q] (u : (ZMod q)ˣ) :
    ramanujanSum q (u : ZMod q) = (μ q : ℂ) := by
  rw [show (u : ZMod q) = 1 * (u : ZMod q) by simp,
    ramanujanSum_mul_unit, ← ramanujanAtOne_eq, ramanujanAtOne_eq_moebius]

/-- The ordinary linear Cohen identity, including q=1. -/
theorem linear_cohen_identity (q : ℕ) [NeZero q] (n : ZMod q) :
    (∑ r : (ZMod q)ˣ, ramanujanSum q (n - (r : ZMod q))) =
      (μ q : ℂ) * ramanujanSum q n := by
  classical
  calc
    _ = ∑ a : (ZMod q)ˣ, ZMod.stdAddChar (n * (a : ZMod q)) *
        ramanujanSum q (-(a : ZMod q)) := by
      simp only [ramanujanSum, sum_unit_filter_eq_sum_units]
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ a : (ZMod q)ˣ, ZMod.stdAddChar (n * (a : ZMod q)) * (μ q : ℂ) := by
      apply sum_congr rfl
      intro a _
      rw [show -(a : ZMod q) = ((-a : (ZMod q)ˣ) : ZMod q) from rfl,
        ramanujanSum_unit_eq_moebius]
    _ = _ := by rw [← sum_mul, ramanujanSum, sum_unit_filter_eq_sum_units, mul_comm]

end PrimeSquares
