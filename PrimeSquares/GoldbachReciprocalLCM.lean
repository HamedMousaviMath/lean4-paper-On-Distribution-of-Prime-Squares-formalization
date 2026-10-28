import PrimeSquares.GoldbachProgressionEnergy
import PrimeSquares.ReciprocalMultiples

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_lcm_gcd_quotients {a b : ℕ} (ha : 0<a) :
    a.lcm b=a.gcd b*(a/a.gcd b)*(b/a.gcd b) := by
  have hg := Nat.gcd_pos_of_pos_left b ha
  apply Nat.eq_of_mul_eq_mul_left hg
  calc
    a.gcd b*a.lcm b=a*b := Nat.gcd_mul_lcm a b
    _=(a.gcd b*(a/a.gcd b))*(a.gcd b*(b/a.gcd b)) := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left a b),
        Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]
    _=a.gcd b*(a.gcd b*(a/a.gcd b)*(b/a.gcd b)) := by ring

/-- A pair of positive denominators injects into its gcd and two quotients. -/
theorem goldbach_gcd_quotient_triple_injective :
    Function.Injective (fun x : ℕ×ℕ => (x.1.gcd x.2,(x.1/x.1.gcd x.2,x.2/x.1.gcd x.2))) := by
  intro x y h
  have hg := congrArg Prod.fst h
  have ha := congrArg (fun t : ℕ×(ℕ×ℕ) => t.2.1) h
  have hb := congrArg (fun t : ℕ×(ℕ×ℕ) => t.2.2) h
  dsimp only at hg ha hb
  apply Prod.ext
  · calc
      x.1=x.1.gcd x.2*(x.1/x.1.gcd x.2) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
      _=y.1.gcd y.2*(y.1/y.1.gcd y.2) := by rw [ha,hg]
      _=y.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  · calc
      x.2=x.1.gcd x.2*(x.2/x.1.gcd x.2) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
      _=y.1.gcd y.2*(y.2/y.1.gcd y.2) := by rw [hb,hg]
      _=y.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)

/-- The reciprocal-lcm double sum in the source diagonal and fibre-square bounds. -/
theorem goldbach_reciprocal_lcm_harmonic_cube (V : ℕ) :
    (∑ a∈Icc 1 V,∑ b∈Icc 1 V,((a.lcm b:ℕ):ℝ)⁻¹)≤(harmonic V:ℝ)^3 := by
  classical
  let S := Icc 1 V
  let e : ℕ×ℕ→ℕ×(ℕ×ℕ) := fun x => (x.1.gcd x.2,(x.1/x.1.gcd x.2,x.2/x.1.gcd x.2))
  let g : ℕ×(ℕ×ℕ)→ℝ := fun x => (x.1:ℝ)⁻¹*(x.2.1:ℝ)⁻¹*(x.2.2:ℝ)⁻¹
  have hmem : (S×ˢS).image e⊆S×ˢ(S×ˢS) := by
    intro t ht
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    obtain ⟨ha,hb⟩ := mem_product.mp hx
    obtain ⟨ha0,haV⟩ := mem_Icc.mp ha
    obtain ⟨hb0,hbV⟩ := mem_Icc.mp hb
    have hg : 0<x.1.gcd x.2 := Nat.gcd_pos_of_pos_left _ ha0
    have hga := Nat.gcd_le_left x.2 ha0
    have hgb := Nat.gcd_le_right x.1 hb0
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨hg,hga.trans haV⟩,
      mem_product.mpr ⟨mem_Icc.mpr ⟨Nat.div_pos hga hg,(Nat.div_le_self _ _).trans haV⟩,
        mem_Icc.mpr ⟨Nat.div_pos hgb hg,(Nat.div_le_self _ _).trans hbV⟩⟩⟩
  have he : (∑ x∈S×ˢS,((x.1.lcm x.2:ℕ):ℝ)⁻¹)≤∑ t∈S×ˢ(S×ˢS),g t := by
    apply sum_le_sum_of_injOn e goldbach_gcd_quotient_triple_injective.injOn hmem
    · intro x hx
      have ha0 := (mem_Icc.mp (mem_product.mp hx).1).1
      rw [goldbach_lcm_gcd_quotients ha0,Nat.cast_mul,Nat.cast_mul,mul_inv_rev,mul_inv_rev]
      dsimp only [e,g]
      exact le_of_eq (by ring)
    · intro t _ _
      dsimp only [g]
      positivity
  have hH : (∑ t∈S×ˢ(S×ˢS),g t)=(harmonic V:ℝ)^3 := by
    simp only [sum_product,g]
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    simp only [Rat.cast_inv,Rat.cast_natCast]
    rw [show (3:ℕ)=2+1 by decide,pow_succ,pow_two]
    simp only [sum_mul,mul_sum,S]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    apply sum_congr rfl
    intro c _
    ring
  simpa only [sum_product] using he.trans_eq hH

theorem goldbach_reciprocal_lcm_log_cube (V : ℕ) :
    (∑ a∈Icc 1 V,∑ b∈Icc 1 V,((a.lcm b:ℕ):ℝ)⁻¹)≤(1+Real.log V)^3 := by
  have hH : (0:ℝ)≤harmonic V := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    exact sum_nonneg (fun i _ => by simp only [Rat.cast_inv,Rat.cast_natCast]; positivity)
  exact (goldbach_reciprocal_lcm_harmonic_cube V).trans
    (pow_le_pow_left₀ hH (harmonic_le_one_add_log V) 3)

theorem goldbach_reciprocal_lcm_strict_real_cutoff {V : ℝ} (hV : 1≤V) :
    (∑ a∈(range ⌈V⌉₊).filter (fun k => 0<k),
      ∑ b∈(range ⌈V⌉₊).filter (fun k => 0<k),((a.lcm b:ℕ):ℝ)⁻¹)≤
      (1+Real.log V)^3 := by
  classical
  let S := (range ⌈V⌉₊).filter (fun k => 0<k)
  let T := Icc 1 ⌊V⌋₊
  have hST : S⊆T := by
    intro k hk
    obtain ⟨hkr,hkp⟩ := mem_filter.mp hk
    exact mem_Icc.mpr ⟨hkp,(Nat.le_floor_iff (by linarith : 0≤V)).mpr
      (Nat.lt_ceil.mp (mem_range.mp hkr)).le⟩
  have he : (∑ x∈S×ˢS,((x.1.lcm x.2:ℕ):ℝ)⁻¹)≤
      ∑ x∈T×ˢT,((x.1.lcm x.2:ℕ):ℝ)⁻¹ := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx
      exact mem_product.mpr ⟨hST (mem_product.mp hx).1,hST (mem_product.mp hx).2⟩
    · intro x _ _
      positivity
  have hH : (0:ℝ)≤harmonic ⌊V⌋₊ := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    exact sum_nonneg (fun i _ => by simp only [Rat.cast_inv,Rat.cast_natCast]; positivity)
  calc
    _≤∑ a∈Icc 1 ⌊V⌋₊,∑ b∈Icc 1 ⌊V⌋₊,((a.lcm b:ℕ):ℝ)⁻¹ := by
      simpa only [S,T,sum_product] using he
    _≤(harmonic ⌊V⌋₊:ℝ)^3 := goldbach_reciprocal_lcm_harmonic_cube _
    _≤_ := pow_le_pow_left₀ hH (harmonic_floor_le_one_add_log V hV) 3

end PrimeSquares
