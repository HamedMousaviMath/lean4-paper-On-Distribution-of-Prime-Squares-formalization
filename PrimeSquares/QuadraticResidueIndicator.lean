import PrimeSquares.UnitSquareResidues

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def quadraticCharReal (p : ℕ) [Fact p.Prime] (a : ZMod p) : ℝ :=
  (quadraticChar (ZMod p) a : ℤ)

noncomputable def unitSquareIndicator (q : ℕ) [NeZero q] (a : ZMod q) : ℝ :=
  if a ∈ unitSquareResidues q then 1 else 0

theorem unitSquareIndicator_bounds (q : ℕ) [NeZero q] (a : ZMod q) :
    0 ≤ unitSquareIndicator q a ∧ unitSquareIndicator q a ≤ 1 := by
  classical
  unfold unitSquareIndicator
  split_ifs <;> norm_num

theorem unitSquareIndicator_formula (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    unitSquareIndicator p a = (1+quadraticCharReal p a-(if a=0 then 1 else 0))/2 := by
  classical
  by_cases h0 : a=0
  · subst a
    simp [unitSquareIndicator, mem_unitSquareResidues, isUnitSquare_iff,
      quadraticCharReal]
  · by_cases hs : IsSquare a
    · have hm : a ∈ unitSquareResidues p :=
        (mem_unitSquareResidues a).mpr ((isUnitSquare_iff a).mpr ⟨isUnit_iff_ne_zero.mpr h0, hs⟩)
      simp [unitSquareIndicator, hm, quadraticCharReal,
        (quadraticChar_one_iff_isSquare h0).mpr hs, h0]
    · have hm : a ∉ unitSquareResidues p := by
        simpa only [mem_unitSquareResidues, isUnitSquare_iff, not_and_or] using Or.inr hs
      simp [unitSquareIndicator, hm, quadraticCharReal,
        quadraticChar_neg_one_iff_not_isSquare.mpr hs, h0]

theorem sum_unitSquareIndicator (q : ℕ) [NeZero q] :
    ∑ a : ZMod q, unitSquareIndicator q a = ((unitSquareResidues q).card : ℝ) := by
  classical
  simp [unitSquareIndicator]

theorem sum_quadraticCharReal (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∑ a : ZMod p, quadraticCharReal p a = 0 := by
  have h := quadraticChar_sum_zero ((ZMod.ringChar_zmod_n p).substr hp)
  simp only [quadraticCharReal, ←Int.cast_sum, h, Int.cast_zero]

theorem unitSquareResidues_prime_card_real (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ((unitSquareResidues p).card : ℝ) = ((p : ℝ)-1)/2 := by
  classical
  rw [←sum_unitSquareIndicator]
  simp_rw [unitSquareIndicator_formula, sub_div, add_div]
  simp [sum_sub_distrib, sum_add_distrib, ←sum_div, sum_quadraticCharReal p hp]
  ring

theorem unitSquareResidues_prime_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    2*(unitSquareResidues p).card=p-1 := by
  have h := unitSquareResidues_prime_card_real p hp
  have hp1 := (Fact.out : p.Prime).one_le
  have : (2 : ℝ)*(unitSquareResidues p).card = ((p-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hp1]
    norm_num
    linarith
  exact_mod_cast this

theorem unitSquareResidues_prime_density (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (1/3 : ℝ) ≤ (unitSquareResidues p).card/p ∧
      ((unitSquareResidues p).card : ℝ)/p ≤ 1/2 := by
  rw [unitSquareResidues_prime_card_real p hp]
  have hp2 := (Fact.out : p.Prime).two_le
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
  constructor
  · apply (le_div_iff₀ (by positivity : (0 : ℝ)<p)).mpr
    nlinarith
  · apply (div_le_iff₀ (by positivity : (0 : ℝ)<p)).mpr
    nlinarith

end PrimeSquares
