import PrimeSquares.CyclicCharacters

/-!
# CRT multiplicativity of the Ramanujan and quadratic Cohen sums

Source: Draft5, equation e:Cmultiplicative in Lemma l:cohenquadratic.
The unit equivalence is inherited from the ring CRT. The coefficient change
(a,b) -> n*a+m*b lifts the scaled CRT coordinates (n*a,m*b); multiplication
by n modulo m and m modulo n are unit permutations. Character scaling then
separates the phases with their correct normalizations. No factorization of
characters or multiplicativity assertion is left as an assumption.
-/

open Finset

namespace PrimeSquares

def crtUnitsEquiv {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

theorem crtUnitsEquiv_val {m n : ℕ} (h : m.Coprime n) (u : (ZMod (m * n))ˣ) :
    ZMod.chineseRemainder h (u : ZMod (m * n)) =
      (((crtUnitsEquiv h u).1 : ZMod m), ((crtUnitsEquiv h u).2 : ZMod n)) := rfl

theorem crtUnitsEquiv_cast {m n : ℕ} (h : m.Coprime n) (u : (ZMod (m * n))ˣ) :
    ((crtUnitsEquiv h u).1 : ZMod m) =
      ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) u ∧
    ((crtUnitsEquiv h u).2 : ZMod n) =
      ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) u := by
  constructor
  · change (ZMod.cast (u : ZMod (m * n)) : ZMod m × ZMod n).1 = _
    exact Prod.fst_zmod_cast _
  · change (ZMod.cast (u : ZMod (m * n)) : ZMod m × ZMod n).2 = _
    exact Prod.snd_zmod_cast _

theorem crtUnitsEquiv_scaled_val {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) :
    let un : (ZMod m)ˣ := ZMod.unitOfCoprime n h.symm
    let um : (ZMod n)ˣ := ZMod.unitOfCoprime m h
    ((crtUnitsEquiv h).symm (un * a, um * b) : ZMod (m * n)) =
      (n : ZMod (m * n)) * ((a : ZMod m).val : ZMod (m * n)) +
      (m : ZMod (m * n)) * ((b : ZMod n).val : ZMod (m * n)) := by
  dsimp only
  apply (ZMod.chineseRemainder h).injective
  rw [crtUnitsEquiv_val]
  simp only [MulEquiv.apply_symm_apply, Units.val_mul, ZMod.coe_unitOfCoprime,
    map_add, map_mul, map_natCast]
  ext <;> simp

theorem crtUnitsEquiv_scaled_phase {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) (x : ZMod (m * n)) :
    let un : (ZMod m)ˣ := ZMod.unitOfCoprime n h.symm
    let um : (ZMod n)ˣ := ZMod.unitOfCoprime m h
    ZMod.stdAddChar (x * ((crtUnitsEquiv h).symm (un * a, um * b) : ZMod (m * n))) =
      ZMod.stdAddChar (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) x * (a : ZMod m)) *
      ZMod.stdAddChar (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) x * (b : ZMod n)) := by
  dsimp only
  rw [crtUnitsEquiv_scaled_val, mul_add, AddChar.map_add_eq_mul]
  have ha : x * ((n : ZMod (m * n)) * ((a : ZMod m).val : ZMod (m * n))) =
      (n : ZMod (m * n)) * (x * ((a : ZMod m).val : ZMod (m * n))) := by ring
  have hb : x * ((m : ZMod (m * n)) * ((b : ZMod n).val : ZMod (m * n))) =
      (m : ZMod (m * n)) * (x * ((b : ZMod n).val : ZMod (m * n))) := by ring
  rw [ha, hb, stdAddChar_scale m n, stdAddChar_scale_left m n]
  simp only [map_mul, map_natCast, ZMod.natCast_zmod_val]

theorem ramanujanSum_coprime_mul (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (x : ZMod (m * n)) :
    ramanujanSum (m * n) x =
      ramanujanSum m (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) x) *
      ramanujanSum n (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) x) := by
  classical
  let un : (ZMod m)ˣ := ZMod.unitOfCoprime n h.symm
  let um : (ZMod n)ˣ := ZMod.unitOfCoprime m h
  let e : (ZMod m)ˣ × (ZMod n)ˣ ≃ (ZMod (m * n))ˣ :=
    (Equiv.prodCongr (Equiv.mulLeft un) (Equiv.mulLeft um)).trans
      (crtUnitsEquiv h).symm.toEquiv
  unfold ramanujanSum
  rw [sum_unit_filter_eq_sum_units, sum_unit_filter_eq_sum_units,
    sum_unit_filter_eq_sum_units]
  calc
    _ = ∑ ab : (ZMod m)ˣ × (ZMod n)ˣ,
        ZMod.stdAddChar (x * (e ab : ZMod (m * n))) := (Equiv.sum_comp e _).symm
    _ = ∑ ab : (ZMod m)ˣ × (ZMod n)ˣ,
        ZMod.stdAddChar (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) x *
          (ab.1 : ZMod m)) *
        ZMod.stdAddChar (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) x *
          (ab.2 : ZMod n)) := by
      apply sum_congr rfl
      intro ab _
      exact crtUnitsEquiv_scaled_phase h ab.1 ab.2 x
    _ = _ := by rw [Fintype.sum_prod_type, sum_mul_sum]

theorem quadraticRamanujanSum_coprime_mul (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (x : ZMod (m * n)) :
    quadraticRamanujanSum (m * n) x =
      quadraticRamanujanSum m (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) x) *
      quadraticRamanujanSum n (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) x) := by
  classical
  unfold quadraticRamanujanSum
  rw [sum_unit_filter_eq_sum_units, sum_unit_filter_eq_sum_units,
    sum_unit_filter_eq_sum_units]
  calc
    _ = ∑ ab : (ZMod m)ˣ × (ZMod n)ˣ,
        ramanujanSum (m * n) (x - ((crtUnitsEquiv h).symm ab : ZMod (m * n)) ^ 2) :=
      (Equiv.sum_comp (crtUnitsEquiv h).symm.toEquiv _).symm
    _ = ∑ ab : (ZMod m)ˣ × (ZMod n)ˣ,
        ramanujanSum m (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) x -
          (ab.1 : ZMod m) ^ 2) *
        ramanujanSum n (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) x -
          (ab.2 : ZMod n) ^ 2) := by
      apply sum_congr rfl
      intro ab _
      rw [ramanujanSum_coprime_mul m n h]
      have hc := crtUnitsEquiv_cast h ((crtUnitsEquiv h).symm ab)
      simp only [MulEquiv.apply_symm_apply] at hc
      simp only [map_sub, map_pow, ← hc.1, ← hc.2]
    _ = _ := by rw [Fintype.sum_prod_type, sum_mul_sum]

end PrimeSquares
