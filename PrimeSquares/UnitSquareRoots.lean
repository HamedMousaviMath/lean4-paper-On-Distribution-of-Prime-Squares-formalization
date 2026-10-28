import PrimeSquares.TwistedQuadratic
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-! Bounds for the kernel of squaring on the actual modular unit group. -/

open Finset

namespace PrimeSquares

theorem unitSquareRootCount_one : unitSquareRootCount 1 = 1 := by
  rw [unitSquareRootCount_eq_card]
  decide

theorem unitSquareRootCount_odd_prime_pow (p j : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    unitSquareRootCount (p ^ j) ≤ 2 := by
  have : NeZero (p ^ j) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : IsCyclic (ZMod (p ^ j))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 j
  rw [unitSquareRootCount_eq_card]
  exact IsCyclic.card_pow_eq_one_le (by decide)

theorem unitSquareRootCount_two_pow (j : ℕ) : unitSquareRootCount (2 ^ j) ≤ 4 := by
  by_cases hj : j ≤ 2
  · interval_cases j <;> rw [unitSquareRootCount_eq_card] <;> decide
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
  let v : (ZMod (2 ^ (k + 3)))ˣ :=
    ZMod.unitOfCoprime 5 ((by decide : Nat.Coprime 5 2).pow_right (k + 3))
  let f := (powMonoidHom 2 : (ZMod (2 ^ (k + 3)))ˣ →* (ZMod (2 ^ (k + 3)))ˣ)
  have hv : orderOf v = 2 ^ (k + 1) := by
    rw [← orderOf_units]
    simpa [v, Nat.add_assoc] using ZMod.orderOf_five (k + 1)
  let w : f.range := ⟨v ^ 2, ⟨v, rfl⟩⟩
  have hw : orderOf w = 2 ^ k := by
    rw [← Subgroup.orderOf_coe]
    change orderOf (v ^ 2) = 2 ^ k
    rw [orderOf_pow, hv]
    have hd : 2 ∣ 2 ^ (k + 1) := dvd_pow_self _ (by omega)
    rw [Nat.gcd_eq_right hd, pow_succ, Nat.mul_div_cancel]; norm_num
  have hrange : 2 ^ k ≤ Nat.card f.range := by
    rw [← hw]
    exact orderOf_le_card
  have hcard : Nat.card (ZMod (2 ^ (k + 3)))ˣ = 4 * 2 ^ k := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_two (by omega)]
    norm_num [show k + 3 - 1 = k + 2 by omega, pow_add, mul_comm]
  have hprod : Nat.card f.ker * Nat.card f.range = 4 * 2 ^ k := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hcard]
  change Nat.card f.ker ≤ 4
  have hp : 0 < 2 ^ k := by positivity
  nlinarith [Nat.mul_le_mul_left (Nat.card f.ker) hrange]

theorem unitSquareRootCount_prime_pow (p j : ℕ) (hp : p.Prime) :
    unitSquareRootCount (p ^ j) ≤ 4 := by
  by_cases hp2 : p = 2
  · subst p; exact unitSquareRootCount_two_pow j
  · exact (unitSquareRootCount_odd_prime_pow p j hp hp2).trans (by decide)

theorem unitSquareRootCount_coprime_mul (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) : unitSquareRootCount (m * n) = unitSquareRootCount m * unitSquareRootCount n := by
  let e := crtUnitsEquiv h
  let E : (powMonoidHom 2 : (ZMod (m * n))ˣ →* (ZMod (m * n))ˣ).ker ≃
      ((powMonoidHom 2 : (ZMod m)ˣ →* (ZMod m)ˣ).ker ×
       (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).ker) :=
    { toFun := fun u =>
        (⟨(e u).1, by
          change (e u).1 ^ 2 = 1
          have hu : (e u) ^ 2 = 1 := by
            rw [← map_pow, show (u : (ZMod (m * n))ˣ) ^ 2 = 1 from u.property, map_one]
          exact congrArg Prod.fst hu⟩,
         ⟨(e u).2, by
          change (e u).2 ^ 2 = 1
          have hu : (e u) ^ 2 = 1 := by
            rw [← map_pow, show (u : (ZMod (m * n))ˣ) ^ 2 = 1 from u.property, map_one]
          exact congrArg Prod.snd hu⟩)
      invFun := fun uv => ⟨e.symm (uv.1, uv.2), by
        change (e.symm ((uv.1 : (ZMod m)ˣ), (uv.2 : (ZMod n)ˣ))) ^ 2 = 1
        rw [← map_pow]
        have hu : ((uv.1 : (ZMod m)ˣ), (uv.2 : (ZMod n)ˣ)) ^ 2 = 1 :=
          Prod.ext uv.1.property uv.2.property
        rw [hu, map_one]⟩
      left_inv := by intro u; apply Subtype.ext; exact e.symm_apply_apply u
      right_inv := by
        intro uv
        have he := e.apply_symm_apply ((uv.1 : (ZMod m)ˣ), (uv.2 : (ZMod n)ˣ))
        apply Prod.ext <;> apply Subtype.ext
        · exact congrArg Prod.fst he
        · exact congrArg Prod.snd he }
  exact (Nat.card_congr E).trans (Nat.card_prod _ _)

theorem unitSquareRootCount_le_pow (q : ℕ) (hq : q ≠ 0) :
    unitSquareRootCount q ≤ 4 ^ q.primeFactors.card := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => exact (hq rfl).elim
  | one => simp [unitSquareRootCount_one]
  | prime_pow p j hp hj =>
    rw [Nat.primeFactors_prime_pow hj.ne' hp, card_singleton, pow_one]
    exact unitSquareRootCount_prime_pow p j hp
  | coprime a b ha hb hc ihA ihB =>
    have : NeZero a := ⟨by omega⟩
    have : NeZero b := ⟨by omega⟩
    rw [unitSquareRootCount_coprime_mul a b hc,
      Nat.primeFactors_mul (by omega : a ≠ 0) (by omega : b ≠ 0),
      card_union_of_disjoint hc.disjoint_primeFactors, pow_add]
    exact Nat.mul_le_mul (ihA (by omega)) (ihB (by omega))

end PrimeSquares
