import PrimeSquares.InducedTwistCRT
import PrimeSquares.TwistedGaussBound
import PrimeSquares.CohenProduct

/-!
# The actual weighted Fourier correlation

This is the first expression in Lemma 3.27. Fourier expansion exposes a
character-weighted Ramanujan sum; induced-character CRT separates it into
the original twist and a coprime principal factor.
-/

open Finset

namespace PrimeSquares

noncomputable def twistedSquareCorrelation (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ZMod q) : ℂ :=
  ∑ a : (ZMod q)ˣ, twistedSquareSum q χ a * ZMod.stdAddChar ((a : ZMod q) * x)

theorem twistedSquareCorrelation_as_ramanujan (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ZMod q) :
    twistedSquareCorrelation q χ x = (q.totient : ℂ)⁻¹ *
      ∑ r : (ZMod q)ˣ, χ r * ramanujanSum q (x - (r : ZMod q) ^ 2) := by
  classical
  simp only [twistedSquareCorrelation, twistedSquareSum, twistedUnitQuadraticGaussSum]
  rw [mul_sum]
  calc
    _ = (q.totient : ℂ)⁻¹ * ∑ a : (ZMod q)ˣ, ∑ r : (ZMod q)ˣ,
        χ r * ZMod.stdAddChar ((x - (r : ZMod q) ^ 2) * (a : ZMod q)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      rw [mul_assoc, sum_mul]
      congr 1
      apply sum_congr rfl
      intro r _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      rw [show -(a : ZMod q) * (r : ZMod q) ^ 2 + (a : ZMod q) * x =
        (x - (r : ZMod q) ^ 2) * (a : ZMod q) by ring]
    _ = _ := by
      rw [sum_comm]
      simp only [ramanujanSum, sum_unit_filter_eq_sum_units, mul_sum]

theorem twistedSquareCorrelation_principal (q : ℕ) [NeZero q] (x : ZMod q) :
    twistedSquareCorrelation q 1 x = (q.totient : ℂ)⁻¹ * quadraticRamanujanSum q x := by
  rw [twistedSquareCorrelation_as_ramanujan]
  simp only [MulChar.one_apply_coe, one_mul, quadraticRamanujanSum,
    sum_unit_filter_eq_sum_units]

theorem induced_twistedCorrelation_coprime_mul (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (χ : DirichletCharacter ℂ m) (x : ZMod (m * n)) :
    twistedSquareCorrelation (m * n)
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ) x =
      twistedSquareCorrelation m χ (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) x) *
      twistedSquareCorrelation n 1 (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) x) := by
  classical
  rw [twistedSquareCorrelation_as_ramanujan, twistedSquareCorrelation_as_ramanujan,
    twistedSquareCorrelation_principal]
  have he : (∑ r : (ZMod (m * n))ˣ,
      DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ r *
        ramanujanSum (m * n) (x - (r : ZMod (m * n)) ^ 2)) =
      (∑ r : (ZMod m)ˣ, χ r * ramanujanSum m
        (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) x - (r : ZMod m) ^ 2)) *
      quadraticRamanujanSum n (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) x) := by
    calc
      _ = ∑ ab : (ZMod m)ˣ × (ZMod n)ˣ,
          (χ ab.1 * ramanujanSum m
            (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) x - (ab.1 : ZMod m) ^ 2)) *
          ramanujanSum n
            (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) x - (ab.2 : ZMod n) ^ 2) := by
        rw [← Equiv.sum_comp (crtUnitsEquiv h).symm.toEquiv]
        apply sum_congr rfl
        intro ab _
        change DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ
          ((crtUnitsEquiv h).symm ab : (ZMod (m * n))ˣ) *
          ramanujanSum (m * n)
            (x - (((crtUnitsEquiv h).symm ab : (ZMod (m * n))ˣ) : ZMod (m * n)) ^ 2) = _
        rw [induced_character_crt_value m n h, ramanujanSum_coprime_mul m n h]
        have ht := crtUnitsEquiv_cast h ((crtUnitsEquiv h).symm ab)
        simp only [MulEquiv.apply_symm_apply] at ht
        simp only [map_sub, map_pow, ← ht.1, ← ht.2]
        ring
      _ = _ := by
        simp only [quadraticRamanujanSum, sum_unit_filter_eq_sum_units]
        rw [Fintype.sum_prod_type, sum_mul_sum]
  rw [he, Nat.totient_mul h, Nat.cast_mul, mul_inv_rev]
  ring

/-- A coarse conductor bound suffices; no primitive-character classification is needed. -/
theorem norm_twistedCorrelation_finite_bound (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ZMod q) :
    ‖twistedSquareCorrelation q χ x‖ ≤ (8 : ℝ) ^ q.primeFactors.card * Real.sqrt q := by
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos q)
  have hφ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hq : Real.sqrt (q : ℝ) ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
  calc
    _ ≤ ∑ a : (ZMod q)ˣ,
        ‖twistedSquareSum q χ a * ZMod.stdAddChar ((a : ZMod q) * x)‖ := norm_sum_le _ _
    _ ≤ ∑ _ : (ZMod q)ˣ, (8 : ℝ) ^ q.primeFactors.card / Real.sqrt q := by
      apply sum_le_sum
      intro a _
      simpa only [norm_mul, norm_stdAddChar, mul_one] using
        norm_twistedSquareSum_finite_bound q χ a a.isUnit
    _ = (q.totient : ℝ) * ((8 : ℝ) ^ q.primeFactors.card / Real.sqrt q) := by
      simp [ZMod.card_units_eq_totient]
    _ ≤ (q : ℝ) * ((8 : ℝ) ^ q.primeFactors.card / Real.sqrt q) :=
      mul_le_mul_of_nonneg_right hφ (by positivity)
    _ = _ := by field_simp; nlinarith [hq]

end PrimeSquares
