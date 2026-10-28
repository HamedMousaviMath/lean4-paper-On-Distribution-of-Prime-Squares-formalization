import PrimeSquares.GaussCRT
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Genuine character-twisted quadratic sums

The source's character, minus sign and totient normalization are retained.
The finite estimates below apply to every complex Dirichlet character, hence
in particular to real characters. No real-character classification is assumed.
-/

open Finset

namespace PrimeSquares

noncomputable def twistedUnitQuadraticGaussSum (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) : ℂ :=
  ∑ u : (ZMod q)ˣ, χ u * ZMod.stdAddChar (a * (u : ZMod q) ^ 2)

noncomputable def twistedSquareSum (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) : ℂ :=
  (q.totient : ℂ)⁻¹ * twistedUnitQuadraticGaussSum q χ (-a)

theorem twistedUnitQuadraticGaussSum_principal (q : ℕ) [NeZero q] (a : ZMod q) :
    twistedUnitQuadraticGaussSum q 1 a = unitQuadraticGaussSum q a := by
  simp only [twistedUnitQuadraticGaussSum, MulChar.one_apply (Units.isUnit _), one_mul,
    unitQuadraticGaussSum]

theorem twistedSquareSum_principal (q : ℕ) [NeZero q] (a : ZMod q) :
    twistedSquareSum q 1 a = principalSquareSum q a := by
  rw [twistedSquareSum, twistedUnitQuadraticGaussSum_principal, principalSquareSum_as_unitGauss]

theorem norm_twistedSquareSum (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    ‖twistedSquareSum q χ a‖ = ‖twistedUnitQuadraticGaussSum q χ (-a)‖ / (q.totient : ℝ) := by
  rw [twistedSquareSum, norm_mul, norm_inv, norm_natCast]
  ring

theorem norm_twistedSquareSum_le_one (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) : ‖twistedSquareSum q χ a‖ ≤ 1 := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [norm_twistedSquareSum]
  apply (div_le_iff₀ hφ).mpr
  calc
    _ ≤ ∑ u : (ZMod q)ˣ, ‖χ u * ZMod.stdAddChar (-a * (u : ZMod q) ^ 2)‖ :=
      norm_sum_le _ _
    _ = _ := by simp [ZMod.card_units_eq_totient]

theorem twistedUnitQuadraticGaussSum_mul_unit_sq (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) (v : (ZMod q)ˣ) :
    χ v * twistedUnitQuadraticGaussSum q χ (a * (v : ZMod q) ^ 2) =
      twistedUnitQuadraticGaussSum q χ a := by
  classical
  rw [twistedUnitQuadraticGaussSum, mul_sum]
  calc
    _ = ∑ u : (ZMod q)ˣ, χ (v * u : (ZMod q)ˣ) *
        ZMod.stdAddChar (a * ((v * u : (ZMod q)ˣ) : ZMod q) ^ 2) := by
      apply sum_congr rfl
      intro u _
      have he : (a * (v : ZMod q) ^ 2) * (u : ZMod q) ^ 2 =
          a * ((v : ZMod q) * (u : ZMod q)) ^ 2 := by ring
      simp only [Units.val_mul, map_mul]
      rw [← he]
      ring
    _ = _ := by
      exact Equiv.sum_comp (Equiv.mulLeft v)
        (fun u : (ZMod q)ˣ => χ u * ZMod.stdAddChar (a * (u : ZMod q) ^ 2))

theorem norm_twistedUnitQuadraticGaussSum_mul_unit_sq (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) (v : (ZMod q)ˣ) :
    ‖twistedUnitQuadraticGaussSum q χ (a * (v : ZMod q) ^ 2)‖ =
      ‖twistedUnitQuadraticGaussSum q χ a‖ := by
  have he := congrArg norm (twistedUnitQuadraticGaussSum_mul_unit_sq q χ a v)
  simpa only [norm_mul, χ.unit_norm_eq_one, one_mul] using he

noncomputable def unitSquareRootCount (q : ℕ) : ℕ :=
  Nat.card (powMonoidHom 2 : (ZMod q)ˣ →* (ZMod q)ˣ).ker

theorem unitSquareRootCount_eq_card (q : ℕ) [NeZero q] :
    unitSquareRootCount q = (univ.filter (fun u : (ZMod q)ˣ => u ^ 2 = 1)).card := by
  simp [unitSquareRootCount, Nat.card_eq_fintype_card, Fintype.card_subtype,
    MonoidHom.mem_ker, powMonoidHom_apply]

theorem unitSquareFiber_card_le (q : ℕ) [NeZero q] (a b : ZMod q) (ha : IsUnit a) :
    (univ.filter (fun u : (ZMod q)ˣ => a * (u : ZMod q) ^ 2 = b)).card ≤ unitSquareRootCount q := by
  classical
  by_cases h : ∃ v : (ZMod q)ˣ, a * (v : ZMod q) ^ 2 = b
  · obtain ⟨v, hv⟩ := h
    let f : {u : (ZMod q)ˣ // a * (u : ZMod q) ^ 2 = b} →
        (powMonoidHom 2 : (ZMod q)ˣ →* (ZMod q)ˣ).ker := fun u =>
      ⟨u.val / v, by
        change (u.val / v) ^ 2 = 1
        have he : (u.val : ZMod q) ^ 2 = (v : ZMod q) ^ 2 :=
          ha.mul_left_cancel (u.property.trans hv.symm)
        have he' : u.val ^ 2 = v ^ 2 := Units.ext (by simpa only [Units.val_pow_eq_pow_val] using he)
        rw [div_pow, he']
        simp⟩
    have hf : Function.Injective f := by
      intro u w hfw
      apply Subtype.ext
      have he : u.val / v = w.val / v := congrArg Subtype.val hfw
      exact (div_left_inj).mp he
    have hc := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_subtype, unitSquareRootCount, Nat.card_eq_fintype_card] using hc
  · have he : univ.filter (fun u : (ZMod q)ˣ => a * (u : ZMod q) ^ 2 = b) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro u _ hu
      exact h ⟨u, hu⟩
    rw [he, card_empty]
    exact Nat.zero_le _

end PrimeSquares
