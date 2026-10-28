import PrimeSquares.TwistedEnergy
import PrimeSquares.UnitSquareRoots
import PrimeSquares.PrimeFactorPower

/-!
# Unconditional character-twisted Gauss bound (Lemma 3.24)

The bound is uniform over all complex Dirichlet characters, so it includes
the source's real characters. No PNT, Weil estimate or character classification
is an additional hypothesis.
-/

open Finset

namespace PrimeSquares

theorem norm_twistedSquareSum_le_roots (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) (ha : IsUnit a) :
    ‖twistedSquareSum q χ a‖ ≤ (unitSquareRootCount q : ℝ) * Real.sqrt q / q.totient := by
  rw [norm_twistedSquareSum]
  exact div_le_div_of_nonneg_right
    (norm_twistedUnitQuadraticGaussSum_le_roots q χ (-a) ha.neg) (Nat.cast_nonneg _)

theorem norm_twistedSquareSum_finite_bound (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) (ha : IsUnit a) :
    ‖twistedSquareSum q χ a‖ ≤ (8 : ℝ) ^ q.primeFactors.card / Real.sqrt q := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos q)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg q)
  have hk : (unitSquareRootCount q : ℝ) ≤ (4 : ℝ) ^ q.primeFactors.card := by
    exact_mod_cast unitSquareRootCount_le_pow q (NeZero.ne q)
  have hq : (q : ℝ) ≤ (q.totient : ℝ) * (2 : ℝ) ^ q.primeFactors.card := by
    exact_mod_cast le_totient_mul_two_pow_primeFactors q (NeZero.pos q)
  calc
    _ ≤ (unitSquareRootCount q : ℝ) * Real.sqrt q / q.totient :=
      norm_twistedSquareSum_le_roots q χ a ha
    _ ≤ (4 : ℝ) ^ q.primeFactors.card * Real.sqrt q / q.totient :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hk hs.le) hφ.le
    _ ≤ (8 : ℝ) ^ q.primeFactors.card / Real.sqrt q := by
      apply (div_le_div_iff₀ hφ hs).mpr
      rw [mul_assoc, ← pow_two, hs2]
      calc
        _ ≤ (4 : ℝ) ^ q.primeFactors.card * (q.totient * (2 : ℝ) ^ q.primeFactors.card) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
        _ = _ := by
          rw [show (8 : ℝ) = 4 * 2 by norm_num, mul_pow]
          ring

/-- Lemma 3.24, strengthened to every complex Dirichlet character. The
constant depends only on epsilon and is uniform in q, chi and a. -/
theorem twistedSquareSum_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (a : ZMod q), IsUnit a →
      ‖twistedSquareSum q χ a‖ ≤ C * (q : ℝ) ^ (-(1 / 2 : ℝ) + ε) := by
  obtain ⟨C, hC, hc⟩ := primeFactor_pow_le_rpow 8 (by norm_num) ε hε
  refine ⟨C, hC, ?_⟩
  intro q inst χ a ha
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  calc
    _ ≤ (8 : ℝ) ^ q.primeFactors.card / Real.sqrt q :=
      norm_twistedSquareSum_finite_bound q χ a ha
    _ ≤ (C * (q : ℝ) ^ ε) / Real.sqrt q :=
      div_le_div_of_nonneg_right (hc q (NeZero.pos q)) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, mul_div_assoc, ← Real.rpow_sub hq]
      rw [show ε - (1 / 2 : ℝ) = -(1 / 2) + ε by ring]

theorem twistedSquareSum_uniform_bound_int (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (a : ℤ), IsCoprime (q : ℤ) a →
      ‖twistedSquareSum q χ (a : ZMod q)‖ ≤ C * (q : ℝ) ^ (-(1 / 2 : ℝ) + ε) := by
  obtain ⟨C, hC, hc⟩ := twistedSquareSum_uniform_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro q inst χ a ha
  exact hc q χ (a : ZMod q) ((ZMod.coe_int_isUnit_iff_isCoprime a q).mpr ha)

end PrimeSquares
