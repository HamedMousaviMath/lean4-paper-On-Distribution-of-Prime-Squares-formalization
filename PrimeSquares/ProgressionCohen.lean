import PrimeSquares.LinearCohen

/-!
# Cohen identity in an arithmetic progression

Source: Draft5, Lemma 3.11 (`l:progressioncohen`). Congruence is expressed by
the canonical reduction ZMod q -> ZMod g for g | q. The unrestricted sum is
over the actual units modulo q; no equidistribution assumption is used.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace PrimeSquares

/-- The left side of Lemma 3.11, with congruence imposed by canonical reduction. -/
noncomputable def progressionRamanujanSum (q g : ℕ) [NeZero q] [NeZero g]
    (hg : g ∣ q) (b : ZMod g) (x : ZMod q) : ℂ :=
  ∑ r : (ZMod q)ˣ,
    if ZMod.castHom hg (ZMod g) (r : ZMod q) = b
    then ramanujanSum q (x - (r : ZMod q)) else 0

/-- A nonzero square-zero translation preserving the congruence class kills the sum. -/
theorem progressionRamanujanSum_eq_zero_of_square_zero (q g : ℕ) [NeZero q] [NeZero g]
    (hg : g ∣ q) (b : ZMod g) (x t : ZMod q)
    (ht : t ^ 2 = 0) (hnt : t ≠ 0) (hgt : ZMod.castHom hg (ZMod g) t = 0) :
    progressionRamanujanSum q g hg b x = 0 := by
  classical
  let ρ := ZMod.castHom hg (ZMod g)
  have hGauss (a : (ZMod q)ˣ) :
      (∑ r : (ZMod q)ˣ, if ρ (r : ZMod q) = b then
        ZMod.stdAddChar ((x - (r : ZMod q)) * (a : ZMod q)) else 0) = 0 := by
    let f (r : (ZMod q)ˣ) : ℂ := if ρ (r : ZMod q) = b then
      ZMod.stdAddChar ((x - (r : ZMod q)) * (a : ZMod q)) else 0
    have hphase : ZMod.stdAddChar (-(t * (a : ZMod q))) ≠ (1 : ℂ) := by
      intro h
      have hz : -(t * (a : ZMod q)) = 0 := ZMod.injective_stdAddChar
        (h.trans (AddChar.map_zero_eq_one _).symm)
      exact hnt (a.isUnit.mul_left_eq_zero.mp (neg_eq_zero.mp hz))
    have hshift : (∑ r, f r) = ZMod.stdAddChar (-(t * (a : ZMod q))) * ∑ r, f r := by
      calc
        _ = ∑ r : (ZMod q)ˣ, f (nilpotentAddEquiv t ht r) :=
          (Equiv.sum_comp (nilpotentAddEquiv t ht) f).symm
        _ = ∑ r : (ZMod q)ˣ, ZMod.stdAddChar (-(t * (a : ZMod q))) * f r := by
          apply sum_congr rfl
          intro r _
          change (if ρ ((r : ZMod q) + t) = b then
            ZMod.stdAddChar ((x - ((r : ZMod q) + t)) * (a : ZMod q)) else 0) = _
          rw [map_add, hgt, add_zero]
          dsimp only [f]
          split_ifs
          · rw [← AddChar.map_add_eq_mul]
            congr 1
            ring
          · rw [mul_zero]
        _ = _ := (mul_sum ..).symm
    have hprod : (ZMod.stdAddChar (-(t * (a : ZMod q))) - 1) * (∑ r, f r) = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hphase)
  unfold progressionRamanujanSum
  simp only [ramanujanSum, sum_unit_filter_eq_sum_units]
  simp_rw [ite_sum_zero]
  rw [sum_comm]
  exact sum_eq_zero fun a _ => hGauss a

/-- Shared prime factors supply precisely such a translation. -/
theorem progressionRamanujanSum_non_coprime (g h : ℕ) [NeZero g] [NeZero h]
    (hc : ¬g.Coprime h) (b : ZMod g) (x : ZMod (g * h)) :
    progressionRamanujanSum (g * h) g (Nat.dvd_mul_right g h) b x = 0 := by
  obtain ⟨p, hp, hpg, hph⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  obtain ⟨l, hl⟩ := hpg
  obtain ⟨k, hk⟩ := hph
  have hkpos : 0 < k := by
    by_contra! hz
    have : h = 0 := by rw [hk, show k = 0 by omega, mul_zero]
    exact NeZero.ne h this
  have htpos : 0 < g * k := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne g)) hkpos
  let t : ZMod (g * h) := (g * k : ℕ)
  have ht : t ^ 2 = 0 := by
    dsimp [t]
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    refine ⟨l * k, ?_⟩
    rw [hl, hk]
    ring
  have hnt : t ≠ 0 := by
    dsimp [t]
    rw [ZMod.natCast_eq_zero_iff]
    apply Nat.not_dvd_of_pos_of_lt htpos
    calc
      g * k < (g * k) * p := by
        simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hp.one_lt htpos
      _ = g * h := by rw [hk]; ring
  have hgt : ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g) t = 0 := by
    change ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g) ((g * k : ℕ) : ZMod (g * h)) = 0
    rw [map_natCast, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  exact progressionRamanujanSum_eq_zero_of_square_zero _ _ _ b x t ht hnt hgt

/-- CRT fixes the first coordinate and leaves the complementary unit coordinate free. -/
theorem progressionRamanujanSum_coprime (g h : ℕ) [NeZero g] [NeZero h]
    (hc : g.Coprime h) (b : (ZMod g)ˣ) (x : ZMod (g * h)) :
    progressionRamanujanSum (g * h) g (Nat.dvd_mul_right g h) (b : ZMod g) x =
      (μ h : ℂ) *
        ramanujanSum h (ZMod.castHom (Nat.dvd_mul_left h g) (ZMod h) x) *
        ramanujanSum g (ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g) x - b) := by
  classical
  unfold progressionRamanujanSum
  calc
    _ = ∑ ab : (ZMod g)ˣ × (ZMod h)ˣ,
        if ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g)
          (((crtUnitsEquiv hc).symm ab : (ZMod (g * h))ˣ) : ZMod (g * h)) = (b : ZMod g)
        then ramanujanSum (g * h)
          (x - (((crtUnitsEquiv hc).symm ab : (ZMod (g * h))ˣ) : ZMod (g * h))) else 0 :=
      (Equiv.sum_comp (crtUnitsEquiv hc).symm.toEquiv _).symm
    _ = ∑ ab : (ZMod g)ˣ × (ZMod h)ˣ,
        if ab.1 = b then
          ramanujanSum g (ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g) x - b) *
          ramanujanSum h (ZMod.castHom (Nat.dvd_mul_left h g) (ZMod h) x -
            (ab.2 : ZMod h)) else 0 := by
      apply sum_congr rfl
      intro ab _
      have hc' := crtUnitsEquiv_cast hc ((crtUnitsEquiv hc).symm ab)
      simp only [MulEquiv.apply_symm_apply] at hc'
      rw [← hc'.1, ramanujanSum_coprime_mul g h hc]
      simp only [map_sub, ← hc'.1, ← hc'.2, Units.val_inj]
      split_ifs with he
      · rw [he]
      · rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
      rw [← mul_sum, linear_cohen_identity]
      ring

/-- Product-modulus form of Lemma 3.11, with both branches and all moduli. -/
theorem progression_cohen_identity_mul (g h : ℕ) [NeZero g] [NeZero h]
    (b : (ZMod g)ˣ) (x : ZMod (g * h)) :
    progressionRamanujanSum (g * h) g (Nat.dvd_mul_right g h) (b : ZMod g) x =
      if g.Coprime h then (μ h : ℂ) *
        ramanujanSum h (ZMod.castHom (Nat.dvd_mul_left h g) (ZMod h) x) *
        ramanujanSum g (ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g) x - b)
      else 0 := by
  classical
  by_cases hc : g.Coprime h
  · rw [ite_eq_left hc]
    exact progressionRamanujanSum_coprime g h hc b x
  · rw [ite_eq_right hc]
    exact progressionRamanujanSum_non_coprime g h hc b x

/-- The paper's divisor/quotient notation and integer input. The nonzero quotient
instance follows from g | q and q>0; it only makes the residue-ring type explicit. -/
theorem progression_cohen_identity (q g : ℕ) [NeZero q] [NeZero g] [hdiv : NeZero (q / g)]
    (hg : g ∣ q) (b : ZMod g) (hb : IsUnit b) (n : ℤ) :
    progressionRamanujanSum q g hg b (n : ZMod q) =
      if g.Coprime (q / g) then (μ (q / g) : ℂ) *
        ramanujanSum (q / g) (n : ZMod (q / g)) *
        ramanujanSum g ((n : ZMod g) - b) else 0 := by
  obtain ⟨h, rfl⟩ := hg
  have : NeZero h := ⟨fun hz => NeZero.ne (g * h) (by rw [hz, mul_zero])⟩
  revert hdiv
  rw [Nat.mul_div_right h (Nat.pos_of_ne_zero (NeZero.ne g))]
  intro hdiv
  simpa only [map_intCast, hb.unit_spec] using
    progression_cohen_identity_mul g h hb.unit (n : ZMod (g * h))

/-- Integer congruence classes with the usual coprimality hypothesis. -/
theorem progression_cohen_identity_int (q g : ℕ) [NeZero q] [NeZero g] [NeZero (q / g)]
    (hg : g ∣ q) (b n : ℤ) (hb : IsCoprime (g : ℤ) b) :
    progressionRamanujanSum q g hg (b : ZMod g) (n : ZMod q) =
      if g.Coprime (q / g) then (μ (q / g) : ℂ) *
        ramanujanSum (q / g) (n : ZMod (q / g)) *
        ramanujanSum g ((n - b : ℤ) : ZMod g) else 0 := by
  simpa only [Int.cast_sub] using progression_cohen_identity q g hg (b : ZMod g)
    ((ZMod.coe_int_isUnit_iff_isCoprime b g).mpr hb) n

/-- The same identity for arbitrary residues, with the two reductions explicit. -/
theorem progression_cohen_identity_residue (q g : ℕ) [NeZero q] [NeZero g]
    [NeZero (q / g)] (hg : g ∣ q) (b : ZMod g) (hb : IsUnit b) (x : ZMod q) :
    progressionRamanujanSum q g hg b x =
      if g.Coprime (q / g) then (μ (q / g) : ℂ) *
        ramanujanSum (q / g) (ZMod.castHom (Nat.div_dvd_of_dvd hg) (ZMod (q / g)) x) *
        ramanujanSum g (ZMod.castHom hg (ZMod g) x - b) else 0 := by
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  simpa only [map_intCast] using progression_cohen_identity q g hg b hb n

end PrimeSquares
