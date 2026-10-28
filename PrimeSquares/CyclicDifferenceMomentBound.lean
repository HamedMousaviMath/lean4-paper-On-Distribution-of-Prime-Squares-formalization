import PrimeSquares.CyclicNearShifts

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem cyclicFarPairFraction_bounds (q : ℕ) [NeZero q] (S : Finset (ZMod q)) (γ : ℝ) :
    0 ≤ cyclicFarPairFraction q S γ ∧ cyclicFarPairFraction q S γ ≤ 1 := by
  classical
  by_cases hS : S=∅
  · simp [hS, cyclicFarPairFraction, cyclicFarPairs]
  · have hm : (0:ℝ)<S.card := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    have hcard : (cyclicFarPairs q S γ).card ≤ S.card^2 := by
      unfold cyclicFarPairs
      simpa only [Finset.card_product, pow_two] using Finset.card_filter_le (s:=S ×ˢ S) _
    constructor
    · unfold cyclicFarPairFraction
      positivity
    · unfold cyclicFarPairFraction
      apply (div_le_iff₀ (by positivity)).mpr
      simpa only [one_mul, Nat.cast_pow] using (show
        ((cyclicFarPairs q S γ).card:ℝ) ≤ (S.card^2:ℕ) by exact_mod_cast hcard)

theorem cyclic_far_pair_triple_bound (q : ℕ) [NeZero q] (S : Finset (ZMod q))
    (hS : S.Nonempty) (γ C : ℝ) (hγ : 0 ≤ γ) (hC : 0 ≤ C)
    (htriple : ∀ d ∈ signedIntegerShifts (γ*((q:ℝ)/S.card)),
      (additiveTripleCount S (d:ZMod q):ℝ) ≤ C*(S.card:ℝ)^3/q) :
    1-2*C*γ-C*(S.card:ℝ)/q ≤ cyclicFarPairFraction q S γ := by
  classical
  let m : ℝ := S.card
  let r : ℝ := γ*((q:ℝ)/m)
  let D := signedIntegerShifts r
  let A : ℤ → Finset (ZMod q × ZMod q) := fun d =>
    (S ×ˢ S).filter (fun uv => uv.1-uv.2-(d:ZMod q) ∈ S)
  have hq : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Finset.card_pos.mpr hS
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hnear : ((cyclicNearPairs q S γ).card:ℝ) ≤ (2*r+1)*(C*m^3/q) := by
    calc
      _ ≤ ((D.biUnion A).card:ℝ) := by
        exact_mod_cast Finset.card_le_card (cyclicNearPairs_subset_shift_union q S γ hγ)
      _ ≤ ∑ d ∈ D, ((A d).card:ℝ) := by
        exact_mod_cast Finset.card_biUnion_le (s:=D) (t:=A)
      _ ≤ ∑ _d ∈ D, C*m^3/q := Finset.sum_le_sum (fun d hd => htriple d hd)
      _ = (D.card:ℝ)*(C*m^3/q) := by simp
      _ ≤ (2*r+1)*(C*m^3/q) := mul_le_mul_of_nonneg_right
        (signedIntegerShifts_card_bound r hr) (by positivity)
  have hcancel : ((q:ℝ)/m)*(m^3/q)=m^2 := by field_simp
  have hidentity : (2*r+1)*(C*m^3/q)=(2*C*γ+C*m/q)*m^2 := by
    calc
      _ = 2*C*γ*(((q:ℝ)/m)*(m^3/q))+C*m^3/q := by dsimp [r]; ring
      _ = 2*C*γ*m^2+C*m^3/q := by rw [hcancel]
      _ = _ := by ring
  rw [hidentity] at hnear
  have hparts : ((cyclicFarPairs q S γ).card:ℝ)+((cyclicNearPairs q S γ).card:ℝ)=m^2 := by
    dsimp [m]
    exact_mod_cast cyclicFarPairs_add_near_card q S γ
  unfold cyclicFarPairFraction
  apply (le_div_iff₀ (pow_pos hm 2)).mpr
  change (1-2*C*γ-C*m/q)*m^2 ≤ ((cyclicFarPairs q S γ).card:ℝ)
  nlinarith

end PrimeSquares
