import PrimeSquares.GoldbachHybridMinorReduction

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_lcm_fibre_subset_divisors (K : Finset ℕ) (q h : ℕ) (hh : 0<h) :
    K.filter (fun k => k.lcm q=h)⊆h.divisors := by
  intro k hk
  have he := (mem_filter.mp hk).2
  exact Nat.mem_divisors.mpr ⟨he ▸ Nat.dvd_lcm_left k q,hh.ne'⟩

theorem goldbach_lcm_fibre_card (K : Finset ℕ) (q h : ℕ) (hh : 0<h) :
    (K.filter (fun k => k.lcm q=h)).card≤h.divisors.card :=
  card_le_card (goldbach_lcm_fibre_subset_divisors K q h hh)

theorem goldbach_lcm_weighted_sum (K : Finset ℕ) (q H : ℕ) (E : ℕ→ℝ)
    (hmap : ∀ k∈K,k.lcm q∈Icc 1 H) (hE : ∀ h∈Icc 1 H,0≤E h) :
    (∑ k∈K,E (k.lcm q))≤∑ h∈Icc 1 H,(h.divisors.card:ℝ)*E h := by
  classical
  rw [←sum_fiberwise_of_maps_to hmap (fun k => E (k.lcm q))]
  apply sum_le_sum
  intro h hh
  calc
    _=∑ _k∈K.filter (fun k => k.lcm q=h),E h := by
      apply sum_congr rfl
      intro k hk
      rw [(mem_filter.mp hk).2]
    _=((K.filter (fun k => k.lcm q=h)).card:ℝ)*E h := by rw [sum_const,nsmul_eq_mul]
    _≤_ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast goldbach_lcm_fibre_card K q h (mem_Icc.mp hh).1) (hE h hh)

theorem goldbach_lcm_weighted_square_divisor_sum (K : Finset ℕ) (q H : ℕ) (E : ℕ→ℝ)
    (hmap : ∀ k∈K,k.lcm q∈Icc 1 H) (hE : ∀ h∈Icc 1 H,0≤E h) :
    (∑ k∈K,E (k.lcm q))≤∑ h∈Icc 1 H,(h.divisors.card:ℝ)^2*E h := by
  exact (goldbach_lcm_weighted_sum K q H E hmap hE).trans (sum_le_sum (fun h hh =>
    mul_le_mul_of_nonneg_right (by
      exact_mod_cast (Nat.le_self_pow (by decide : 2≠0) h.divisors.card)) (hE h hh)))

/-- Elementary major-arc reindexing. The progression error estimate and the
general distribution theorem are separate obligations, not conclusions here. -/
theorem goldbach_major_progression_error_sum (K : Finset ℕ) (q H : ℕ)
    (err : ℕ→ℂ) (E : ℕ→ℝ) (R : ℝ)
    (hmap : ∀ k∈K,k.lcm q∈Icc 1 H) (hE : ∀ h∈Icc 1 H,0≤E h)
    (herr : ∀ k∈K,‖err k‖≤R^2*E (k.lcm q)) :
    (∑ k∈K,‖err k‖)≤R^2*(∑ h∈Icc 1 H,(h.divisors.card:ℝ)^2*E h) := by
  calc
    _≤∑ k∈K,R^2*E (k.lcm q) := sum_le_sum herr
    _=R^2*(∑ k∈K,E (k.lcm q)) := (mul_sum ..).symm
    _≤_ := mul_le_mul_of_nonneg_left
      (goldbach_lcm_weighted_square_divisor_sum K q H E hmap hE) (sq_nonneg R)

end PrimeSquares
