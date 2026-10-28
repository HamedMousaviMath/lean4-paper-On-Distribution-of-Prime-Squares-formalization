import PrimeSquares.RationalArcOverlap
import Mathlib.Data.Finset.Prod

/-!
# The exact finite set of reduced canonical rational centers

The finite box is only a concrete enumeration device. Membership is exactly
0 <= r < 1 and den(r) <= M, including the denominator-one center zero.
-/

open Finset
namespace PrimeSquares

noncomputable def canonicalRationalCenters (M : ℕ) : Finset ℚ := by
  classical
  exact (((range (M+1)).product (range (M+1))).image
    (fun p : ℕ × ℕ => (p.1 : ℚ)/(p.2 : ℚ))).filter
      (fun r => r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ M)

theorem mem_canonicalRationalCenters (M : ℕ) (r : ℚ) :
    r ∈ canonicalRationalCenters M ↔ r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ M := by
  classical
  simp only [canonicalRationalCenters,mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_,h⟩
    have hn0 : (0 : ℤ) ≤ r.num := Rat.num_nonneg.mpr h.1.1
    have hdp : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
    have hnq : (r.num : ℚ) < r.den := (div_lt_one hdp).mp (by
      rw [r.num_div_den]
      exact h.1.2)
    have hni : r.num < (r.den : ℤ) := by exact_mod_cast hnq
    have hnum : r.num.toNat ≤ M := by omega
    apply mem_image.mpr
    refine ⟨(r.num.toNat,r.den),?_,?_⟩
    · exact mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
    · change (r.num.toNat : ℚ)/r.den = r
      have hc : (r.num.toNat : ℚ) = (r.num : ℚ) := by
        exact_mod_cast Int.toNat_of_nonneg hn0
      rw [hc,r.num_div_den]

theorem canonicalRationalCenters_parameters {M : ℕ} {r : ℚ}
    (hr : r ∈ canonicalRationalCenters M) :
    0 < r.den ∧ r.den ≤ M ∧ 0 ≤ r.num ∧ r.num < (r.den : ℤ) := by
  obtain ⟨hcanonical,hd⟩ := (mem_canonicalRationalCenters M r).mp hr
  have hdp : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hn : (r.num : ℚ) < r.den := (div_lt_one hdp).mp (by
    rw [r.num_div_den]
    exact hcanonical.2)
  exact ⟨r.den_pos,hd,Rat.num_nonneg.mpr hcanonical.1,by exact_mod_cast hn⟩

theorem canonicalRationalCenters_mono {M L : ℕ} (hML : M ≤ L) :
    canonicalRationalCenters M ⊆ canonicalRationalCenters L := by
  intro r hr
  rw [mem_canonicalRationalCenters] at hr ⊢
  exact ⟨hr.1,hr.2.trans hML⟩

theorem canonicalRationalCenters_zero : canonicalRationalCenters 0 = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hd := (mem_canonicalRationalCenters 0 r).mp hr
  have hp := r.den_pos
  omega

theorem zero_mem_canonicalRationalCenters (M : ℕ) :
    (0 : ℚ) ∈ canonicalRationalCenters M ↔ 1 ≤ M := by
  norm_num [mem_canonicalRationalCenters]

theorem canonicalRationalCenters_card (M : ℕ) :
    (canonicalRationalCenters M).card ≤ (M+1)^2 := by
  classical
  calc
    _ ≤ (((range (M+1)).product (range (M+1))).image
        (fun p : ℕ × ℕ => (p.1 : ℚ)/(p.2 : ℚ))).card := card_filter_le _ _
    _ ≤ ((range (M+1)).product (range (M+1))).card := card_image_le
    _ = _ := by simp only [Finset.product_eq_sprod,Finset.card_product,card_range,pow_two]

noncomputable def sourceRationalCenters (R : ℝ) : Finset ℚ :=
  canonicalRationalCenters ⌊R⌋₊

theorem mem_sourceRationalCenters {R : ℝ} (hR : 0 ≤ R) (r : ℚ) :
    r ∈ sourceRationalCenters R ↔ r ∈ Set.Ico (0 : ℚ) 1 ∧ (r.den : ℝ) ≤ R := by
  rw [sourceRationalCenters,mem_canonicalRationalCenters]
  constructor
  · rintro ⟨hr,hd⟩
    exact ⟨hr,(by exact_mod_cast hd : (r.den : ℝ) ≤ ⌊R⌋₊).trans (Nat.floor_le hR)⟩
  · rintro ⟨hr,hd⟩
    exact ⟨hr,Nat.le_floor hd⟩

end PrimeSquares
