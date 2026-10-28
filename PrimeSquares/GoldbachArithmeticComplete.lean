import PrimeSquares.GoldbachUpsilonDecay

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_upsilon_canonical_residue (q k : ℕ) [NeZero q] [NeZero k]
    (b : ℤ) (α : ZMod q) :
    upsilon q k b α=upsilon q k (((b:ZMod k).val:ℕ):ℤ) α := by
  have he : ((((b:ZMod k).val:ℕ):ℤ):ZMod (q.gcd k))=(b:ZMod (q.gcd k)) := by
    simpa only [Int.cast_natCast,map_intCast] using
      goldbach_reduction_val (Nat.gcd_dvd_right q k) (b:ZMod k)
  simp only [upsilon,progressionExponentialSum,he]

theorem goldbach_upsilon_integer_gcd_decay (q k ℓ : ℕ) [NeZero q] [NeZero k]
    (b : ℤ) (hb : IsCoprime (k:ℤ) b) (α : ZMod q) (hα : IsUnit α) :
    ‖upsilon q k b (α*(ℓ:ZMod q))‖≤(q.divisors.card:ℝ)*(q.gcd (k*ℓ):ℝ)/(q:ℝ) := by
  have hbu : IsUnit (b:ZMod k) := (ZMod.coe_int_isUnit_iff_isCoprime b k).mpr hb
  have hbc : (b:ZMod k).val.Coprime k := (ZMod.isUnit_iff_coprime _ k).mp (by
    simpa only [ZMod.natCast_zmod_val] using hbu)
  rw [goldbach_upsilon_canonical_residue]
  exact goldbach_upsilon_gcd_divisor_decay q k (b:ZMod k).val ℓ hbc α hα

theorem goldbach_divisor_card_one_le (q : ℕ) [NeZero q] : (1:ℝ)≤q.divisors.card := by
  have hc : 0<q.divisors.card := card_pos.mpr ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,NeZero.ne q⟩⟩
  exact_mod_cast hc

theorem goldbach_arithmetic_uniform_bounds (q k ℓ : ℕ) [NeZero q] [NeZero k]
    (b n : ℤ) (hb : IsCoprime (k:ℤ) b) (α : ZMod q) (hα : IsUnit α) :
    ‖principalSquareSum q α‖≤(q.divisors.card:ℝ)^9/Real.sqrt q ∧
    ‖upsilon q k b (α*(ℓ:ZMod q))‖≤(q.divisors.card:ℝ)^9*(q.gcd (k*ℓ):ℝ)/(q:ℝ) ∧
    ‖generalCoefficient q k (ℓ:ℤ) b n‖≤(q.divisors.card:ℝ)^9*(q.gcd (k*ℓ):ℝ)/(q:ℝ) := by
  have hτ := goldbach_divisor_card_one_le q
  refine ⟨(goldbach_principal_square_divisor_bound q α hα).trans
    (div_le_div_of_nonneg_right (pow_le_pow_right₀ hτ (by decide : 3≤9)) (Real.sqrt_nonneg _)),?_,
    goldbach_general_coefficient_divisor_bound q k ℓ b n hb⟩
  have hp : (q.divisors.card:ℝ)≤(q.divisors.card:ℝ)^9 := by
    simpa only [pow_one] using pow_le_pow_right₀ hτ (by decide : 1≤9)
  exact (goldbach_upsilon_integer_gcd_decay q k ℓ b hb α hα).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)) (Nat.cast_nonneg _))

theorem goldbach_arithmetic_harmonic_common_exponent (N q : ℕ) [NeZero q] (hN : 1≤N)
    (hlog : 1≤Real.log N) (L B : ℝ) (V : ℕ→ℝ) (hB : 0≤B) (hL : L≤(N:ℝ)^2)
    (hV : ∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L →V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) :
    (∑ i∈goldbachCoefficientIndices L V,(q.gcd (i.1*i.2):ℝ)/((i.1:ℝ)*(i.2.totient:ℝ)))≤
      (9*Real.exp 2)*(q.divisors.card:ℝ)^9*(Real.log N)^2 := by
  exact (goldbach_source_arithmetic_harmonic N q hN (NeZero.pos q) hlog L B V hB hL hV).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (goldbach_divisor_card_one_le q) (by decide : 2≤9)) (by positivity)) (sq_nonneg _))

theorem goldbach_odd_prime_power_series (p k : ℕ) [Fact p.Prime] [NeZero k]
    (hp2 : p≠2) (ℓ b n : ℤ) :
    (∑' j : ℕ,generalCoefficient (p^(j+1)) k ℓ b n)=generalCoefficient p k ℓ b n := by
  classical
  rw [tsum_eq_sum (s:=range 1)]
  · simp only [sum_range_succ,sum_range_zero,zero_add,pow_one]
  · intro j hj
    have hj1 : 1≤j := by simpa only [mem_range,not_lt] using hj
    exact generalCoefficient_odd_prime_sq (p^(j+1)) k p hp2 (Nat.pow_dvd_pow p (by omega : 2≤j+1)) ℓ b n

theorem goldbach_two_prime_power_series (k : ℕ) [NeZero k] (ℓ b n : ℤ) :
    (∑' j : ℕ,generalCoefficient (2^(j+1)) k ℓ b n)=
      generalCoefficient 2 k ℓ b n+generalCoefficient 4 k ℓ b n+generalCoefficient 8 k ℓ b n := by
  classical
  rw [tsum_eq_sum (s:=range 3)]
  · norm_num [sum_range_succ]
  · intro j hj
    have hj3 : 3≤j := by simpa only [mem_range,not_lt] using hj
    exact generalCoefficient_sixteen_dvd (2^(j+1)) k (Nat.pow_dvd_pow 2 (by omega : 4≤j+1)) ℓ b n

theorem goldbach_all_primes_euler_series {R : ℝ} (hR : 2≤R) (k : ℕ) [NeZero k] (ℓ b n : ℤ) :
    (∑' q : ℕ,goldbachSmoothCoefficient R k ℓ b n q)=
      ∏ p∈Nat.primesLE ⌊R⌋₊,(1+∑' j : ℕ,generalCoefficient (p^(j+1)) k ℓ b n) := by
  classical
  have hQ : 3≤⌊R⌋₊+1 := by
    have hf : 2≤⌊R⌋₊ := (Nat.le_floor_iff (by linarith : 0≤R)).mpr hR
    omega
  have hs : Nat.primesLE ⌊R⌋₊=insert 2 (oddPrimesBelow (⌊R⌋₊+1)) := by
    ext p
    simp only [Nat.mem_primesLE,mem_insert,oddPrimesBelow,mem_filter,mem_range]
    constructor
    · rintro ⟨hpR,hp⟩
      by_cases he : p=2
      · exact Or.inl he
      · exact Or.inr ⟨by omega,hp,by have := hp.two_le;omega⟩
    · rintro (rfl | ⟨hpR,hp,hp2⟩)
      · exact ⟨by omega,Nat.prime_two⟩
      · exact ⟨by omega,hp⟩
  have he := smoothGeneralSeries_euler_product (⌊R⌋₊+1) k ℓ b n hQ
  have hleft : (∑' q : ℕ,goldbachSmoothCoefficient R k ℓ b n q)=smoothGeneralSeries (⌊R⌋₊+1) k ℓ b n := by
    simp only [goldbachSmoothCoefficient,smoothGeneralSeries,goldbach_prime_inclusive_cutoff (by linarith : 0≤R)]
  rw [hleft,he,hs,prod_insert (by simp [oddPrimesBelow]),goldbach_two_prime_power_series]
  have hodd : (∏ p∈oddPrimesBelow (⌊R⌋₊+1),(1+generalCoefficient p k ℓ b n))=
      ∏ p∈oddPrimesBelow (⌊R⌋₊+1),(1+∑' j : ℕ,generalCoefficient (p^(j+1)) k ℓ b n) := by
    apply prod_congr rfl
    intro p hp
    have : Fact p.Prime := ⟨(mem_filter.mp hp).2.1⟩
    rw [goldbach_odd_prime_power_series p k (by have hh := (mem_filter.mp hp).2.2;omega)]
  rw [hodd]
  ring

theorem goldbach_arithmetic_euler_complete {R : ℝ} (hR : 2≤R)
    (k : ℕ) [NeZero k] (ℓ b n : ℤ) (hb : IsCoprime (k:ℤ) b) :
    Summable (fun q : ℕ => ‖goldbachSmoothCoefficient R k ℓ b n q‖) ∧
    (∑' q : ℕ,goldbachSmoothCoefficient R k ℓ b n q)=
      (∏ p∈Nat.primesLE ⌊R⌋₊,(1+∑' j : ℕ,generalCoefficient (p^(j+1)) k ℓ b n)) ∧
    (∑' q : ℕ,goldbachSmoothCoefficient R k ℓ b n q)=goldbachArithmeticFactor R k ℓ b n :=
  ⟨goldbach_smooth_coefficient_abs_summable hR k ℓ b n,goldbach_all_primes_euler_series hR k ℓ b n,
    goldbach_arithmetic_factor_euler hR k ℓ b n hb⟩

end PrimeSquares
