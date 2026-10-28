import PrimeSquares.CyclicThickening
import PrimeSquares.FiniteSpacingCounterexample

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def signedIntegerShifts (r : ℝ) : Finset ℤ :=
  Finset.Icc (-(⌊r⌋₊:ℤ)) (⌊r⌋₊:ℤ)

theorem signedIntegerShifts_card (r : ℝ) :
    (signedIntegerShifts r).card=2*⌊r⌋₊+1 := by
  simp only [signedIntegerShifts, Int.card_Icc, sub_neg_eq_add]
  omega

theorem signedIntegerShifts_card_bound (r : ℝ) (hr : 0 ≤ r) :
    ((signedIntegerShifts r).card:ℝ) ≤ 2*r+1 := by
  rw [signedIntegerShifts_card]
  push_cast
  linarith [Nat.floor_le hr]

theorem cyclic_distance_short_shift (q : ℕ) [NeZero q] (z : ZMod q) (r : ℝ)
    (hr : 0 ≤ r) (hz : (cyclicDistanceNat q z 0:ℝ) ≤ r) :
    ∃ d ∈ signedIntegerShifts r, (d:ZMod q)=z := by
  simp only [cyclicDistanceNat, sub_zero, zero_sub, Nat.cast_min] at hz
  rcases min_le_iff.mp hz with hp | hn
  · have hf : z.val ≤ ⌊r⌋₊ := (Nat.le_floor_iff hr).mpr hp
    refine ⟨(z.val:ℤ), Finset.mem_Icc.mpr ⟨by omega, by exact_mod_cast hf⟩, ?_⟩
    simp
  · have hf : (-z).val ≤ ⌊r⌋₊ := (Nat.le_floor_iff hr).mpr hn
    refine ⟨-((-z).val:ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    simp

noncomputable def cyclicFarPairs (q : ℕ) [NeZero q] (S : Finset (ZMod q)) (γ : ℝ) :
    Finset (ZMod q × ZMod q) :=
  (S ×ˢ S).filter (fun uv => ∀ w ∈ S,
    γ*((q:ℝ)/S.card) < (cyclicDistanceNat q (uv.1-uv.2) w:ℝ))

noncomputable def cyclicNearPairs (q : ℕ) [NeZero q] (S : Finset (ZMod q)) (γ : ℝ) :
    Finset (ZMod q × ZMod q) :=
  (S ×ˢ S).filter (fun uv => ¬ ∀ w ∈ S,
    γ*((q:ℝ)/S.card) < (cyclicDistanceNat q (uv.1-uv.2) w:ℝ))

noncomputable def cyclicFarPairFraction (q : ℕ) [NeZero q] (S : Finset (ZMod q)) (γ : ℝ) : ℝ :=
  ((cyclicFarPairs q S γ).card:ℝ)/(S.card:ℝ)^2

theorem cyclicFarPairs_add_near_card (q : ℕ) [NeZero q] (S : Finset (ZMod q)) (γ : ℝ) :
    (cyclicFarPairs q S γ).card+(cyclicNearPairs q S γ).card=S.card^2 := by
  classical
  unfold cyclicFarPairs cyclicNearPairs
  rw [Finset.card_filter_add_card_filter_not, Finset.card_product]
  ring

theorem cyclicNearPairs_subset_shift_union (q : ℕ) [NeZero q] (S : Finset (ZMod q))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    cyclicNearPairs q S γ ⊆
      (signedIntegerShifts (γ*((q:ℝ)/S.card))).biUnion (fun d =>
        (S ×ˢ S).filter (fun uv => uv.1-uv.2-(d:ZMod q) ∈ S)) := by
  classical
  intro uv huv
  obtain ⟨huvS,hnot⟩ := Finset.mem_filter.mp huv
  push Not at hnot
  obtain ⟨w,hw,hdist⟩ := hnot
  have hdist_eq : cyclicDistanceNat q (uv.1-uv.2-w) 0=
      cyclicDistanceNat q (uv.1-uv.2) w := by
    unfold cyclicDistanceNat
    rw [sub_zero, zero_sub]
    congr 1
    congr 1
    abel
  have hr : 0 ≤ γ*((q:ℝ)/S.card) := by positivity
  obtain ⟨d,hd,heq⟩ := cyclic_distance_short_shift q (uv.1-uv.2-w)
    (γ*((q:ℝ)/S.card)) hr (by rw [hdist_eq]; exact hdist)
  refine Finset.mem_biUnion.mpr ⟨d,hd,Finset.mem_filter.mpr ⟨huvS,?_⟩⟩
  rw [heq]
  convert hw using 1; abel

end PrimeSquares
