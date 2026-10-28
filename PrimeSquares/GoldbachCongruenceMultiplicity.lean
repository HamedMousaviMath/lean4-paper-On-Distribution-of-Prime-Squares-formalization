import PrimeSquares.GoldbachCongruenceCounting

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachCongruenceMultiplicity (K : Finset ℕ) (a : ℕ→ℕ)
    (t : ℕ) : ℕ := (K.filter (fun k => t%k=a k%k)).card

theorem goldbach_congruence_square_identity (K : Finset ℕ) (a : ℕ→ℕ) (A T : ℕ) :
    (∑ t∈Ico A (A+T),(goldbachCongruenceMultiplicity K a t:ℝ)^2)=
      ∑ k∈K,∑ j∈K,((goldbachSimultaneousCongruences A T k j (a k) (a j)).card:ℝ) := by
  classical
  have hp (t : ℕ) : (goldbachCongruenceMultiplicity K a t:ℝ)^2=
      ∑ k∈K,∑ j∈K,if t%k=a k%k ∧ t%j=a j%j then (1:ℝ) else 0 := by
    simp only [goldbachCongruenceMultiplicity,card_filter,Nat.cast_sum,Nat.cast_ite,
      Nat.cast_one,Nat.cast_zero,pow_two,sum_mul_sum]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro j _
    split_ifs <;> simp_all
  simp_rw [hp]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  rw [sum_comm]
  simp only [goldbachSimultaneousCongruences,card_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero]

theorem goldbach_congruence_square_lcm_bound (K : Finset ℕ) (a : ℕ→ℕ) (A T : ℕ) :
    (∑ t∈Ico A (A+T),(goldbachCongruenceMultiplicity K a t:ℝ)^2)≤
      (T:ℝ)*(∑ k∈K,∑ j∈K,((k.lcm j:ℕ):ℝ)⁻¹)+(K.card:ℝ)^2 := by
  rw [goldbach_congruence_square_identity]
  calc
    _≤∑ k∈K,∑ j∈K,((T:ℝ)/(k.lcm j:ℕ)+1) :=
      sum_le_sum (fun k _ => sum_le_sum (fun j _ =>
        goldbach_simultaneous_congruence_count_real A T k j (a k) (a j)))
    _=_ := by
      simp only [div_eq_mul_inv,mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul]
      ring

theorem goldbach_reciprocal_lcm_subset (K : Finset ℕ) (M : ℕ)
    (hK : K⊆Icc 1 M) :
    (∑ k∈K,∑ j∈K,((k.lcm j:ℕ):ℝ)⁻¹)≤(harmonic M:ℝ)^3 := by
  have he : (∑ x∈K×ˢK,((x.1.lcm x.2:ℕ):ℝ)⁻¹)≤
      ∑ x∈(Icc 1 M)×ˢ(Icc 1 M),((x.1.lcm x.2:ℕ):ℝ)⁻¹ := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx
      exact mem_product.mpr ⟨hK (mem_product.mp hx).1,hK (mem_product.mp hx).2⟩
    · intro x _ _
      positivity
  calc
    _≤∑ k∈Icc 1 M,∑ j∈Icc 1 M,((k.lcm j:ℕ):ℝ)⁻¹ := by
      simpa only [sum_product] using he
    _≤_ := goldbach_reciprocal_lcm_harmonic_cube M

/-- The exact version of e:wellsquare9, retaining the local modulus count. -/
theorem goldbach_congruence_square_harmonic_bound (K : Finset ℕ) (a : ℕ→ℕ)
    (A T M : ℕ) (hK : K⊆Icc 1 M) :
    (∑ t∈Ico A (A+T),(goldbachCongruenceMultiplicity K a t:ℝ)^2)≤
      (T:ℝ)*(harmonic M:ℝ)^3+(K.card:ℝ)^2 := by
  exact (goldbach_congruence_square_lcm_bound K a A T).trans
    (add_le_add (mul_le_mul_of_nonneg_left (goldbach_reciprocal_lcm_subset K M hK)
      (Nat.cast_nonneg T)) le_rfl)

theorem goldbach_congruence_square_strict_real_cutoff (a : ℕ→ℕ) (A T : ℕ)
    {V : ℝ} (hV : 1≤V) :
    (∑ t∈Ico A (A+T),(goldbachCongruenceMultiplicity
      ((range ⌈V⌉₊).filter (fun k => 0<k)) a t:ℝ)^2)≤
      (T:ℝ)*(1+Real.log V)^3+V^2 := by
  let K := (range ⌈V⌉₊).filter (fun k => 0<k)
  have hKT : K⊆Icc 1 ⌊V⌋₊ := by
    intro k hk
    obtain ⟨hkr,hkp⟩ := mem_filter.mp hk
    exact mem_Icc.mpr ⟨hkp,(Nat.le_floor_iff (by linarith : 0≤V)).mpr
      (Nat.lt_ceil.mp (mem_range.mp hkr)).le⟩
  have hc : (K.card:ℝ)≤V := by
    have he := (card_le_card hKT).trans_eq (show (Icc 1 ⌊V⌋₊).card=⌊V⌋₊ by simp)
    exact (show (K.card:ℝ)≤(⌊V⌋₊:ℝ) by exact_mod_cast he).trans
      (Nat.floor_le (by linarith : 0≤V))
  exact (goldbach_congruence_square_lcm_bound K a A T).trans
    (add_le_add (mul_le_mul_of_nonneg_left (goldbach_reciprocal_lcm_strict_real_cutoff hV)
      (Nat.cast_nonneg T)) (pow_le_pow_left₀ (Nat.cast_nonneg K.card) hc 2))

end PrimeSquares
