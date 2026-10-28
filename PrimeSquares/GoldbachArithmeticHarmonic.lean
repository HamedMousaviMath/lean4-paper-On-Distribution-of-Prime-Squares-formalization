import PrimeSquares.GoldbachTotientHarmonic

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_gcd_weighted_divisor_sum (q D : ℕ) (hq : 0<q) (w : ℕ→ℝ) :
    (∑ n∈Icc 1 D,(q.gcd n:ℝ)*w n)=
      ∑ d∈q.divisors,(d.totient:ℝ)*(∑ n∈(Icc 1 D).filter (fun n => d∣n),w n) := by
  classical
  simp_rw [goldbach_gcd_totient_divisor_expansion q _ hq,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [sum_filter,mul_sum]
  apply sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem goldbach_gcd_reciprocal_sum (q D : ℕ) (hq : 0<q) :
    (∑ n∈Icc 1 D,(q.gcd n:ℝ)/(n:ℝ))≤(q.divisors.card:ℝ)*(harmonic D:ℝ) := by
  classical
  have hH : (0:ℝ)≤harmonic D := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    exact sum_nonneg (fun n _ => by simp only [Rat.cast_inv,Rat.cast_natCast];positivity)
  simp only [div_eq_mul_inv]
  rw [goldbach_gcd_weighted_divisor_sum q D hq]
  calc
    _≤∑ d∈q.divisors,(d.totient:ℝ)*((d:ℝ)⁻¹*(harmonic D:ℝ)) := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (reciprocal_multiples_bound d D
        (Nat.pos_of_mem_divisors hd)) (Nat.cast_nonneg _)
    _≤∑ _d∈q.divisors,(harmonic D:ℝ) := by
      apply sum_le_sum
      intro d hd
      have hdR : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_mem_divisors hd
      have hφ : (d.totient:ℝ)≤d := by exact_mod_cast Nat.totient_le d
      calc
        _=((d.totient:ℝ)/d)*(harmonic D:ℝ) := by ring
        _≤1*(harmonic D:ℝ) := mul_le_mul_of_nonneg_right ((div_le_one hdR).mpr hφ) hH
        _=_ := one_mul _
    _=_ := by rw [sum_const,nsmul_eq_mul]

theorem goldbach_gcd_reciprocal_totient_sum (q D : ℕ) (hq : 0<q) :
    (∑ n∈Icc 1 D,(q.gcd n:ℝ)/(n.totient:ℝ))≤
      (q.divisors.card:ℝ)*(Real.exp 2*(harmonic D:ℝ)) := by
  classical
  simp only [div_eq_mul_inv]
  rw [goldbach_gcd_weighted_divisor_sum q D hq]
  calc
    _≤∑ d∈q.divisors,(d.totient:ℝ)*
        ((d.totient:ℝ)⁻¹*(Real.exp 2*(harmonic D:ℝ))) := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (goldbach_reciprocal_totient_multiples d D
        (Nat.pos_of_mem_divisors hd)) (Nat.cast_nonneg _)
    _=∑ _d∈q.divisors,(Real.exp 2*(harmonic D:ℝ)) := by
      apply sum_congr rfl
      intro d hd
      have hφ : (d.totient:ℝ)≠0 := by
        exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_mem_divisors hd)).ne'
      rw [←mul_assoc,mul_inv_cancel₀ hφ,one_mul]
    _=_ := by rw [sum_const,nsmul_eq_mul]

theorem goldbach_gcd_product_bound (q a b : ℕ) (hq : 0<q) :
    q.gcd (a*b)≤q.gcd a*q.gcd b :=
  Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ hq) (Nat.gcd_pos_of_pos_left _ hq))
    (gcd_mul_dvd_mul_gcd q a b)

theorem goldbach_arithmetic_harmonic_rectangle (q D : ℕ) (hq : 0<q)
    (I : Finset (ℕ×ℕ)) (hI : I⊆Icc 1 D×ˢIcc 1 D) :
    (∑ i∈I,(q.gcd (i.1*i.2):ℝ)/((i.1:ℝ)*(i.2.totient:ℝ)))≤
      Real.exp 2*(q.divisors.card:ℝ)^2*(harmonic D:ℝ)^2 := by
  classical
  have hH : (0:ℝ)≤harmonic D := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    exact sum_nonneg (fun n _ => by simp only [Rat.cast_inv,Rat.cast_natCast];positivity)
  calc
    _≤∑ i∈Icc 1 D×ˢIcc 1 D,(q.gcd (i.1*i.2):ℝ)/((i.1:ℝ)*(i.2.totient:ℝ)) :=
      sum_le_sum_of_subset_of_nonneg hI (fun i _ _ => by positivity)
    _≤∑ i∈Icc 1 D×ˢIcc 1 D,
        ((q.gcd i.1:ℝ)/(i.1:ℝ))*((q.gcd i.2:ℝ)/(i.2.totient:ℝ)) := by
      apply sum_le_sum
      intro i _
      have hh : (q.gcd (i.1*i.2):ℝ)≤(q.gcd i.1:ℝ)*(q.gcd i.2:ℝ) := by
        exact_mod_cast goldbach_gcd_product_bound q i.1 i.2 hq
      simpa only [mul_div_mul_comm] using div_le_div_of_nonneg_right hh
        (show 0≤(i.1:ℝ)*(i.2.totient:ℝ) by positivity)
    _=(∑ a∈Icc 1 D,(q.gcd a:ℝ)/(a:ℝ))*
        (∑ b∈Icc 1 D,(q.gcd b:ℝ)/(b.totient:ℝ)) := by
      rw [sum_product,sum_mul_sum]
    _≤((q.divisors.card:ℝ)*(harmonic D:ℝ))*
        ((q.divisors.card:ℝ)*(Real.exp 2*(harmonic D:ℝ))) :=
      mul_le_mul (goldbach_gcd_reciprocal_sum q D hq)
        (goldbach_gcd_reciprocal_totient_sum q D hq)
        (sum_nonneg (fun _ _ => by positivity)) (by positivity)
    _=_ := by ring

theorem goldbach_source_arithmetic_harmonic (N q : ℕ) (hN : 1≤N) (hq : 0<q)
    (hlog : 1≤Real.log N) (L B : ℝ) (V : ℕ→ℝ) (hB : 0≤B) (hL : L≤(N:ℝ)^2)
    (hV : ∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L →
      V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) :
    (∑ i∈goldbachCoefficientIndices L V,
      (q.gcd (i.1*i.2):ℝ)/((i.1:ℝ)*(i.2.totient:ℝ)))≤
        (9*Real.exp 2)*(q.divisors.card:ℝ)^2*(Real.log N)^2 := by
  have hpow : (Real.log N)^(-B)≤1 := Real.rpow_le_one_of_one_le_of_nonpos hlog (by linarith)
  have hv (ℓ : ℕ) (hℓ : 0<ℓ) (hℓL : (ℓ:ℝ)<L) :
      V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ) := (hV ℓ hℓ hℓL).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _))
  obtain ⟨hI,hK,_⟩ := goldbach_source_energy_numerical_ranges N L V hL hv
  have hrect : goldbachCoefficientIndices L V⊆Icc 1 (N^2)×ˢIcc 1 (N^2) := by
    intro i hi
    have hk := hK i.1 (mem_image.mpr ⟨i,hi,rfl⟩) ((mem_goldbachModuliAt _ _ _).mpr hi)
    exact mem_product.mpr ⟨mem_Icc.mpr (hI i hi),mem_Icc.mpr
      ⟨(mem_Icc.mp hk).1,(mem_Icc.mp hk).2.trans (by nlinarith)⟩⟩
  have hH : (harmonic (N^2):ℝ)≤3*Real.log N := by
    have hh := harmonic_le_one_add_log (N^2)
    have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    have he : Real.log (N^2:ℕ)=2*Real.log N := by
      rw [Nat.cast_pow,Real.log_pow]
      norm_num
    rw [he] at hh
    linarith
  have hH0 : (0:ℝ)≤harmonic (N^2) := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    exact sum_nonneg (fun n _ => by simp only [Rat.cast_inv,Rat.cast_natCast];positivity)
  calc
    _≤Real.exp 2*(q.divisors.card:ℝ)^2*(harmonic (N^2):ℝ)^2 :=
      goldbach_arithmetic_harmonic_rectangle q (N^2) hq _ hrect
    _≤Real.exp 2*(q.divisors.card:ℝ)^2*(3*Real.log N)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0 hH 2) (by positivity)
    _=_ := by ring

end PrimeSquares
