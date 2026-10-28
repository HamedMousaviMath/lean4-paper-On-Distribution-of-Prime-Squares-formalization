import PrimeSquares.CyclicThickening

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem cyclic_thickening_pair_bound (q : ℕ) [NeZero q] (S : Finset (ZMod q))
    (hS : S.Nonempty) (γ C : ℝ) (hγ : 0 < γ) (hC : 0 ≤ C)
    (hpair : ∀ d ∈ positiveIntegerShifts (γ*((q:ℝ)/S.card)),
      ∀ e ∈ positiveIntegerShifts (γ*((q:ℝ)/S.card)), d ≠ e →
        (additivePairCount S ((d:ZMod q)-(e:ZMod q)) : ℝ) ≤ C*(S.card:ℝ)^2/q) :
    γ-(S.card:ℝ)/q-C/2*γ^2 ≤ cyclicThickeningDensity q S γ ∧
      cyclicThickeningDensity q S γ ≤ γ := by
  let m : ℝ := S.card
  let r : ℝ := γ*((q:ℝ)/m)
  let I := positiveIntegerShifts r
  let F : ℕ → Finset (ZMod q) := fun d => translatedResidues S (d:ZMod q)
  let n : ℝ := I.card
  let B : ℝ := C*m^2/q
  let t : ℝ := n*m/q
  have hq : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast Finset.card_pos.mpr hS
  have hr : 0 < r := by dsimp [r]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hsize (d : ℕ) (_hd : d ∈ I) : ((F d).card:ℝ)=m := by
    dsimp [F,m]
    rw [translatedResidues_card]
  have hinter (d : ℕ) (hd : d ∈ I) (e : ℕ) (he : e ∈ I) (hde : d ≠ e) :
      ((F d ∩ F e).card:ℝ) ≤ B := by
    dsimp [F]
    rw [translatedResidues_inter_card]
    exact hpair d hd e he hde
  have hlow := finite_union_uniform_quadratic_lower I F m B hB hsize hinter
  have hupp := finite_union_uniform_upper I F m hsize
  have hround := positiveIntegerShifts_card_bounds r hr
  have hscale : r*m/q=γ := by
    dsimp [r]
    field_simp
  have htupper : t ≤ γ := by
    calc
      t ≤ r*m/q := by
        apply (div_le_div_iff_of_pos_right hq).mpr
        exact mul_le_mul_of_nonneg_right hround.2 hm.le
      _ = γ := hscale
  have htlower : γ-m/q ≤ t := by
    calc
      γ-m/q = (r-1)*m/q := by rw [sub_mul, sub_div, hscale, one_mul]
      _ ≤ t := by
        apply (div_le_div_iff_of_pos_right hq).mpr
        exact mul_le_mul_of_nonneg_right hround.1 hm.le
  have hlower : t-C/2*t^2 ≤ cyclicThickeningDensity q S γ := by
    change t-C/2*t^2 ≤ ((I.biUnion F).card:ℝ)/q
    have heq : t-C/2*t^2=(n*m-n^2*B/2)/q := by dsimp [t,B]; ring
    rw [heq]
    exact (div_le_div_iff_of_pos_right hq).mpr hlow
  have hupper : cyclicThickeningDensity q S γ ≤ t := by
    change ((I.biUnion F).card:ℝ)/q ≤ n*m/q
    exact (div_le_div_iff_of_pos_right hq).mpr hupp
  have hsquare : t^2 ≤ γ^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr htupper) (by linarith : 0 ≤ γ+t)]
  have hmult := mul_le_mul_of_nonneg_left hsquare (by linarith : 0 ≤ C/2)
  constructor
  · change γ-m/q-C/2*γ^2 ≤ cyclicThickeningDensity q S γ
    linarith
  · exact hupper.trans htupper

end PrimeSquares
