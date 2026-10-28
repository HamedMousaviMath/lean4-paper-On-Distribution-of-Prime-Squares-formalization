import PrimeSquares.UnitSquareMomentCRT
import PrimeSquares.QuadraticCorrelationRelative

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def unitSquareDensity (q : ℕ) : ℝ := (unitSquareCard q : ℝ)/q
noncomputable def unitSquareSpacing (q : ℕ) : ℝ := (q:ℝ)/unitSquareCard q

theorem unitSquareCard_pos (q : ℕ) [NeZero q] : 0 < unitSquareCard q := by
  rw [unitSquareCard_eq]
  exact Finset.card_pos.mpr (unitSquareResidues_nonempty q)

theorem unitSquareDensity_pos (q : ℕ) [NeZero q] : 0 < unitSquareDensity q := by
  unfold unitSquareDensity
  have := unitSquareCard_pos q
  have := NeZero.pos q
  positivity

theorem unitSquareSpacing_pos (q : ℕ) [NeZero q] : 0 < unitSquareSpacing q := by
  unfold unitSquareSpacing
  have := unitSquareCard_pos q
  have := NeZero.pos q
  positivity

theorem unitSquareDensity_inv (q : ℕ) : (unitSquareDensity q)⁻¹=unitSquareSpacing q := by
  simp [unitSquareDensity, unitSquareSpacing]

theorem unitSquareDensity_prime (p : ℕ) [Fact p.Prime] :
    unitSquareDensity p=primeResidueDensity p := by
  rw [unitSquareDensity, unitSquareCard_eq]
  rfl

theorem unitSquareCard_primeProduct (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    unitSquareCard (∏ p ∈ S, p)=∏ p ∈ S, unitSquareCard p := by
  apply multiplicative_prime_product unitSquareCard ?_ ?_ S hS
  · rw [unitSquareCard_eq, unitSquareResidues_one_card]
  · intro q r hq hr hcop
    have : NeZero q := ⟨hq.ne'⟩
    have : NeZero r := ⟨hr.ne'⟩
    rw [unitSquareCard_eq, unitSquareCard_eq, unitSquareCard_eq, unitSquareResidues_mul_card hcop]

theorem unitSquareDensity_primeProduct (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    unitSquareDensity (∏ p ∈ S, p)=∏ p ∈ S, unitSquareDensity p := by
  rw [unitSquareDensity, unitSquareCard_primeProduct S hS, Nat.cast_prod, Nat.cast_prod,
    ←Finset.prod_div_distrib]
  rfl

theorem unitSquareSpacing_primeProduct (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    unitSquareSpacing (∏ p ∈ S, p)=∏ p ∈ S, (unitSquareDensity p)⁻¹ := by
  rw [←unitSquareDensity_inv, unitSquareDensity_primeProduct S hS, Finset.prod_inv_distrib]

theorem unitSquareDensity_primeProduct_bounds (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) :
    (1/3:ℝ)^S.card ≤ unitSquareDensity (∏ p ∈ S, p) ∧
      unitSquareDensity (∏ p ∈ S, p) ≤ (1/2:ℝ)^S.card := by
  have hb (p : ℕ) (hp : p ∈ S) :
      (1/3:ℝ) ≤ unitSquareDensity p ∧ unitSquareDensity p ≤ 1/2 := by
    have : Fact p.Prime := ⟨(hS p hp).1⟩
    rw [unitSquareDensity_prime]
    exact primeResidueDensity_bounds p (hS p hp).2
  rw [unitSquareDensity_primeProduct S (fun p hp => (hS p hp).1)]
  constructor
  · have h := Finset.prod_le_prod₀ (s:=S) (f:=fun _ => (1/3:ℝ))
      (g:=unitSquareDensity) (fun _ _ => by norm_num) (fun p hp => (hb p hp).1)
    simpa only [Finset.prod_const] using h
  · have h := Finset.prod_le_prod₀ (s:=S) (f:=unitSquareDensity)
      (g:=fun _ => (1/2:ℝ)) (fun p hp => by linarith [(hb p hp).1]) (fun p hp => (hb p hp).2)
    simpa only [Finset.prod_const] using h

theorem unitSquareSpacing_primeProduct_bounds (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) :
    (2:ℝ)^S.card ≤ unitSquareSpacing (∏ p ∈ S, p) ∧
      unitSquareSpacing (∏ p ∈ S, p) ≤ (3:ℝ)^S.card := by
  have hb (p : ℕ) (hp : p ∈ S) :
      (2:ℝ) ≤ (unitSquareDensity p)⁻¹ ∧ (unitSquareDensity p)⁻¹ ≤ 3 := by
    have : Fact p.Prime := ⟨(hS p hp).1⟩
    have hd : (1/3:ℝ) ≤ unitSquareDensity p ∧ unitSquareDensity p ≤ 1/2 := by
      rw [unitSquareDensity_prime]
      exact primeResidueDensity_bounds p (hS p hp).2
    have hpos := unitSquareDensity_pos p
    rw [inv_eq_one_div]
    constructor
    · apply (le_div_iff₀ hpos).mpr
      linarith
    · apply (div_le_iff₀ hpos).mpr
      linarith
  rw [unitSquareSpacing_primeProduct S (fun p hp => (hS p hp).1)]
  constructor
  · have h := Finset.prod_le_prod₀ (s:=S) (f:=fun _ => (2:ℝ))
      (g:=fun p => (unitSquareDensity p)⁻¹) (fun _ _ => by norm_num) (fun p hp => (hb p hp).1)
    simpa only [Finset.prod_const] using h
  · have h := Finset.prod_le_prod₀ (s:=S) (f:=fun p => (unitSquareDensity p)⁻¹)
      (g:=fun _ => (3:ℝ)) (fun p hp => by linarith [(hb p hp).1]) (fun p hp => (hb p hp).2)
    simpa only [Finset.prod_const] using h

theorem unitSquareDensity_le_one (q : ℕ) [NeZero q] : unitSquareDensity q ≤ 1 := by
  have hp0 : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  unfold unitSquareDensity
  apply (div_le_iff₀ hp0).mpr
  rw [unitSquareCard_eq]
  simpa only [one_mul, ZMod.card] using
    (show ((unitSquareResidues q).card:ℝ) ≤ Fintype.card (ZMod q) by
      exact_mod_cast Finset.card_le_univ (unitSquareResidues q))

theorem unitSquareSpacing_le_modulus (q : ℕ) [NeZero q] : unitSquareSpacing q ≤ q := by
  have hm : (1:ℝ) ≤ unitSquareCard q := by exact_mod_cast unitSquareCard_pos q
  unfold unitSquareSpacing
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α:=ℝ) q]

end PrimeSquares
