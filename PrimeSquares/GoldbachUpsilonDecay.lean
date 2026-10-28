import PrimeSquares.GoldbachUpsilonReduction

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_upsilon_int_modulus_congr (q q' k : ℕ) [NeZero q] [NeZero q']
    (h : q=q') (b c : ℤ) : upsilon q k b (c:ZMod q)=upsilon q' k b (c:ZMod q') := by
  subst q'
  rfl

theorem goldbach_progression_exponential_primitive_norm (q g : ℕ) [NeZero q] [NeZero g]
    (hg : g∣q) (b : ZMod g) (hb : IsUnit b) (α : ZMod q) (hα : IsUnit α) :
    ‖progressionExponentialSum q g hg b α‖≤1 := by
  obtain ⟨h,rfl⟩ := hg
  have : NeZero h := ⟨fun hh => NeZero.ne (g*h) (by rw [hh,mul_zero])⟩
  by_cases hc : g.Coprime h
  · simpa only [hb.unit_spec] using goldbach_progression_exponential_coprime_norm g h hc hb.unit α hα
  · rw [goldbach_progression_exponential_noncoprime g h hc b α hα,norm_zero]
    norm_num

theorem goldbach_upsilon_primitive_decay (q k b : ℕ) [NeZero q] [NeZero k]
    (hb : b.Coprime k) (α : ZMod q) (hα : IsUnit α) :
    ‖upsilon q k (b:ℤ) α‖≤(q.gcd k:ℝ)/(q.totient:ℝ) := by
  have hbu : IsUnit (b:ZMod (q.gcd k)) := by
    exact (ZMod.isUnit_iff_coprime b (q.gcd k)).mpr
      (hb.of_dvd_right (Nat.gcd_dvd_right q k))
  rw [goldbach_upsilon_gcd_normalization,norm_mul,norm_div,Complex.norm_natCast,Complex.norm_natCast]
  simp only [Int.cast_natCast]
  calc
    _≤((q.gcd k).totient:ℝ)/(q.totient:ℝ)*1 :=
      mul_le_mul_of_nonneg_left (goldbach_progression_exponential_primitive_norm q (q.gcd k)
        (Nat.gcd_dvd_left q k) (b:ZMod (q.gcd k)) hbu α hα) (by positivity)
    _≤(q.gcd k:ℝ)/(q.totient:ℝ) := by
      rw [mul_one]
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.totient_le (q.gcd k)) (Nat.cast_nonneg _)

theorem goldbach_reciprocal_totient_divisor_bound (q : ℕ) (hq : 0<q) :
    (q.totient:ℝ)⁻¹≤(q.divisors.card:ℝ)/(q:ℝ) := by
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hh : (q:ℝ)≤(q.totient:ℝ)*(2:ℝ)^q.primeFactors.card := by
    exact_mod_cast le_totient_mul_two_pow_primeFactors q hq
  have hb := hh.trans (mul_le_mul_of_nonneg_left (goldbach_two_pow_primeFactors_le_divisors q hq) hφ.le)
  apply (le_div_iff₀ hqR).mpr
  simpa only [div_eq_mul_inv,mul_comm] using (div_le_iff₀ hφ).mpr (by simpa only [mul_comm] using hb)

theorem goldbach_upsilon_gcd_divisor_decay (q k b ℓ : ℕ) [NeZero q] [NeZero k]
    (hb : b.Coprime k) (α : ZMod q) (hα : IsUnit α) :
    ‖upsilon q k (b:ℤ) (α*(ℓ:ZMod q))‖≤
      (q.divisors.card:ℝ)*(q.gcd (k*ℓ):ℝ)/(q:ℝ) := by
  let d := q.gcd ℓ
  let q₀ := q/d
  have hd : 0<d := Nat.gcd_pos_of_pos_left _ (NeZero.pos q)
  have hqd : q₀*d=q := Nat.div_mul_cancel (Nat.gcd_dvd_left q ℓ)
  have hq₀ : 0<q₀ := Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) (Nat.gcd_dvd_left q ℓ)) hd
  have : NeZero d := ⟨hd.ne'⟩
  have : NeZero q₀ := ⟨hq₀.ne'⟩
  have hdiv : q₀∣q := ⟨d,hqd.symm⟩
  let β : ℤ := (α.val:ℤ)*(ℓ/d:ℕ)
  have hα₀ : IsUnit (α.val:ZMod q₀) := by
    have hm := hα.map (ZMod.castHom hdiv (ZMod q₀))
    rwa [←goldbach_reduction_val hdiv α] at hm
  have hℓ₀ : IsUnit ((ℓ/d:ℕ):ZMod q₀) :=
    (ZMod.isUnit_iff_coprime (ℓ/d) q₀).mpr (Nat.coprime_div_gcd_div_gcd hd).symm
  have hβ : IsUnit (β:ZMod q₀) := by
    simpa only [β,Int.cast_mul,Int.cast_natCast] using hα₀.mul hℓ₀
  have hfreq : (((d:ℤ)*β:ℤ):ZMod q)=α*(ℓ:ZMod q) := by
    have he : (d:ZMod q)*((ℓ/d:ℕ):ZMod q)=(ℓ:ZMod q) := by
      have hh : d*(ℓ/d)=ℓ := Nat.mul_div_cancel' (Nat.gcd_dvd_right q ℓ)
      simpa only [Nat.cast_mul] using congrArg (fun z : ℕ => (z:ZMod q)) hh
    dsimp only [β]
    simp only [Int.cast_mul,Int.cast_natCast]
    calc
      _=(α.val:ZMod q)*((d:ZMod q)*((ℓ/d:ℕ):ZMod q)) := by ring
      _=_ := by rw [he,ZMod.natCast_zmod_val]
  have hreduce : upsilon q k (b:ℤ) (((d:ℤ)*β:ℤ):ZMod q)=upsilon q₀ k (b:ℤ) (β:ZMod q₀) := by
    exact (goldbach_upsilon_int_modulus_congr (q₀*d) q k hqd (b:ℤ) ((d:ℤ)*β)).symm.trans
      (goldbach_upsilon_frequency_reduction q₀ d k b hb β)
  rw [hfreq] at hreduce
  have hτ : (q₀.divisors.card:ℝ)≤(q.divisors.card:ℝ) := by
    exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd (NeZero.ne q) hdiv)
  have hG : (q₀.gcd k:ℝ)*(d:ℝ)≤(q.gcd (k*ℓ):ℝ) := by
    have hv : q₀.gcd k*d∣q.gcd (k*ℓ) := Nat.dvd_gcd
      (hqd ▸ Nat.mul_dvd_mul (Nat.gcd_dvd_left q₀ k) (dvd_refl d))
      (Nat.mul_dvd_mul (Nat.gcd_dvd_right q₀ k) (Nat.gcd_dvd_right q ℓ))
    exact_mod_cast Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (NeZero.pos q)) hv
  rw [hreduce]
  calc
    _≤(q₀.gcd k:ℝ)/(q₀.totient:ℝ) := goldbach_upsilon_primitive_decay q₀ k b hb (β:ZMod q₀) hβ
    _≤(q₀.gcd k:ℝ)*((q₀.divisors.card:ℝ)/(q₀:ℝ)) := by
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left
        (goldbach_reciprocal_totient_divisor_bound q₀ hq₀) (Nat.cast_nonneg (q₀.gcd k))
    _≤(q₀.gcd k:ℝ)*((q.divisors.card:ℝ)/(q₀:ℝ)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hτ (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    _=(q.divisors.card:ℝ)*((q₀.gcd k:ℝ)*(d:ℝ))/(q:ℝ) := by
      rw [←hqd,Nat.cast_mul]
      have hdR : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
      field_simp
    _≤_ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

end PrimeSquares
