import PrimeSquares.GoldbachSquareMajorCounts

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_lcm_quotient_range (k q h : ℕ) (hh : 0<h) (he : k.lcm q=h) :
    h/k∈Icc 1 q := by
  have hk : 0<k := by
    by_contra hk
    have hk0 : k=0 := by omega
    simp only [hk0,Nat.lcm_zero_left] at he
    omega
  have hdk : k∣h := he ▸ Nat.dvd_lcm_left k q
  have hq : 0<q := by
    by_contra hq
    have hq0 : q=0 := by omega
    simp only [hq0,Nat.lcm_zero_right] at he
    omega
  have hp : h/k*k=h := Nat.div_mul_cancel hdk
  have hpos : 0<h/k := Nat.div_pos (Nat.le_of_dvd hh hdk) hk
  have hb : h≤k*q := by rw [←he];exact Nat.lcm_le_mul hk hq
  exact mem_Icc.mpr ⟨hpos,by nlinarith⟩

/-- Fixed-q multiplicity costs at most q, independent of the larger modulus.
This allows the classical unweighted BV theorem to suffice. -/
theorem goldbach_lcm_fibre_card_le_q (K : Finset ℕ) (q h : ℕ) (hh : 0<h) :
    (K.filter (fun k => k.lcm q=h)).card≤q := by
  classical
  let S := K.filter (fun k => k.lcm q=h)
  have hinj : Set.InjOn (fun k => h/k) (↑S : Set ℕ) := by
    intro k hk j hj heq
    have hek := (mem_filter.mp hk).2
    have hej := (mem_filter.mp hj).2
    have hp : 0<h/k := (mem_Icc.mp (goldbach_lcm_quotient_range k q h hh hek)).1
    have hkprod : h/k*k=h := Nat.div_mul_cancel (hek ▸ Nat.dvd_lcm_left k q)
    have hjprod : h/j*j=h := Nat.div_mul_cancel (hej ▸ Nat.dvd_lcm_left j q)
    change h/k=h/j at heq
    rw [←heq] at hjprod
    exact Nat.eq_of_mul_eq_mul_left hp (hkprod.trans hjprod.symm)
  have hs : S.image (fun k => h/k)⊆Icc 1 q := by
    intro d hd
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hd
    exact goldbach_lcm_quotient_range k q h hh (mem_filter.mp hk).2
  calc
    _=(S.image (fun k => h/k)).card := (card_image_iff.mpr hinj).symm
    _≤(Icc 1 q).card := card_le_card hs
    _=q := by simp only [Nat.card_Icc,Nat.add_sub_cancel]

theorem goldbach_lcm_unweighted_sum (K : Finset ℕ) (q H : ℕ) (E : ℕ→ℝ)
    (hmap : ∀ k∈K,k.lcm q∈Icc 1 H) (hE : ∀ h∈Icc 1 H,0≤E h) :
    (∑ k∈K,E (k.lcm q))≤(q:ℝ)*(∑ h∈Icc 1 H,E h) := by
  classical
  rw [←sum_fiberwise_of_maps_to hmap (fun k => E (k.lcm q)),mul_sum]
  apply sum_le_sum
  intro h hh
  calc
    _=∑ _k∈K.filter (fun k => k.lcm q=h),E h := by
      apply sum_congr rfl
      intro k hk
      rw [(mem_filter.mp hk).2]
    _=((K.filter (fun k => k.lcm q=h)).card:ℝ)*E h := by rw [sum_const,nsmul_eq_mul]
    _≤_ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast goldbach_lcm_fibre_card_le_q K q h (mem_Icc.mp hh).1) (hE h hh)

theorem goldbach_major_error_from_unweighted_distribution (K : Finset ℕ) (q H : ℕ)
    (err : ℕ→ℂ) (E : ℕ→ℝ) {R : ℝ} (hqR : (q:ℝ)≤R)
    (hmap : ∀ k∈K,k.lcm q∈Icc 1 H) (hE : ∀ h∈Icc 1 H,0≤E h)
    (herr : ∀ k∈K,‖err k‖≤R^2*E (k.lcm q)) :
    (∑ k∈K,‖err k‖)≤R^3*(∑ h∈Icc 1 H,E h) := by
  have hsum : 0≤∑ h∈Icc 1 H,E h := sum_nonneg hE
  calc
    _≤∑ k∈K,R^2*E (k.lcm q) := sum_le_sum herr
    _=R^2*(∑ k∈K,E (k.lcm q)) := (mul_sum ..).symm
    _≤R^2*((q:ℝ)*(∑ h∈Icc 1 H,E h)) :=
      mul_le_mul_of_nonneg_left (goldbach_lcm_unweighted_sum K q H E hmap hE) (sq_nonneg R)
    _≤R^2*(R*(∑ h∈Icc 1 H,E h)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqR hsum) (sq_nonneg R)
    _=R^3*(∑ h∈Icc 1 H,E h) := by ring

end PrimeSquares
