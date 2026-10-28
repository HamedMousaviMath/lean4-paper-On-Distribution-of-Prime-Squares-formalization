import PrimeSquares.GoldbachArithmeticPrime

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_upsilon_gcd_normalization (q k : ℕ) [NeZero q] [NeZero k]
    (b : ℤ) (a : ZMod q) :
    upsilon q k b a=((q.gcd k).totient:ℂ)/(q.totient:ℂ)*
      progressionExponentialSum q (q.gcd k) (Nat.gcd_dvd_left q k) (b:ZMod (q.gcd k)) a := by
  have hq : (q.totient:ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hl : ((k.lcm q).totient:ℂ)≠0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.lcm_pos (NeZero.pos k) (NeZero.pos q))).ne'
  have ht : ((k.lcm q).totient:ℂ)*((q.gcd k).totient:ℂ)=(q.totient:ℂ)*(k.totient:ℂ) := by
    exact_mod_cast (by simpa only [Nat.lcm_comm k q] using totient_lcm_mul_totient_gcd q k)
  unfold upsilon
  congr 1
  field_simp
  linear_combination -ht

theorem goldbach_progression_exponential_trivial (q g : ℕ) [NeZero q]
    (hg : g∣q) (b : ZMod g) (a : ZMod q) :
    ‖progressionExponentialSum q g hg b a‖≤(q.totient:ℝ) := by
  classical
  unfold progressionExponentialSum
  calc
    _≤∑ v : (ZMod q)ˣ,‖if ZMod.castHom hg (ZMod g) (v:ZMod q)=b
      then ZMod.stdAddChar (-(a*(v:ZMod q))) else 0‖ := norm_sum_le _ _
    _≤∑ _v : (ZMod q)ˣ,(1:ℝ) := by
      apply sum_le_sum
      intro v _
      split_ifs
      · rw [norm_stdAddChar]
      · norm_num
    _=_ := by simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,ZMod.card_units_eq_totient]

theorem goldbach_upsilon_trivial_gcd (q k : ℕ) [NeZero q] [NeZero k]
    (b : ℤ) (a : ZMod q) : ‖upsilon q k b a‖≤((q.gcd k).totient:ℝ) := by
  have hq : (q.totient:ℝ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  rw [goldbach_upsilon_gcd_normalization,norm_mul,norm_div,Complex.norm_natCast,Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left (goldbach_progression_exponential_trivial q _ _ _ a) (by positivity)).trans_eq
  field_simp

theorem goldbach_general_coefficient_trivial (q k : ℕ) [NeZero q] [NeZero k] (ℓ b n : ℤ) :
    ‖generalCoefficient q k ℓ b n‖≤(q:ℝ)^2 := by
  have hφq : (q.totient:ℝ)≤q := by exact_mod_cast Nat.totient_le q
  have hφg : ((q.gcd k).totient:ℝ)≤q := by
    exact_mod_cast (Nat.totient_le (q.gcd k)).trans (Nat.gcd_le_left k (NeZero.pos q))
  rw [generalCoefficient_eq]
  calc
    _≤∑ a : (ZMod q)ˣ,‖upsilon q k b ((a:ZMod q)*(ℓ:ZMod q))*principalSquareSum q a*
        ZMod.stdAddChar ((a:ZMod q)*(n:ZMod q))‖ := norm_sum_le _ _
    _≤∑ _a : (ZMod q)ˣ,(q:ℝ) := by
      apply sum_le_sum
      intro a _
      rw [norm_mul,norm_stdAddChar,mul_one,norm_mul]
      calc
        _≤((q.gcd k).totient:ℝ)*1 := mul_le_mul (goldbach_upsilon_trivial_gcd q k b _)
          (norm_principalSquareSum_le_one q a) (norm_nonneg _) (show (0:ℝ)≤(q.gcd k).totient from Nat.cast_nonneg _)
        _≤q := by simpa only [mul_one] using hφg
    _=(q.totient:ℝ)*(q:ℝ) := by
      rw [sum_const,card_univ,nsmul_eq_mul,ZMod.card_units_eq_totient]
    _≤(q:ℝ)^2 := by nlinarith [show (0:ℝ)≤q from Nat.cast_nonneg _]

theorem goldbach_general_coefficient_small_two_power (k ℓ a : ℕ) [NeZero k]
    (ha : a≤3) (b n : ℤ) :
    ‖generalCoefficient (2^a) k (ℓ:ℤ) b n‖≤
      512*((2^a).gcd (k*ℓ):ℝ)/((2^a:ℕ):ℝ) := by
  have hq : (0:ℝ)<(2^a:ℕ) := by positivity
  have hq8 : ((2^a:ℕ):ℝ)≤8 := by exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤2) ha)
  have hd : (1:ℝ)≤(2^a).gcd (k*ℓ) := by exact_mod_cast Nat.gcd_pos_of_pos_left (k*ℓ) (by positivity : 0<2^a)
  apply (goldbach_general_coefficient_trivial (2^a) k (ℓ:ℤ) b n).trans
  apply (le_div_iff₀ hq).mpr
  have hp := pow_le_pow_left₀ hq.le hq8 3
  nlinarith

theorem goldbach_general_coefficient_prime_power (p a k ℓ : ℕ)
    [Fact p.Prime] [NeZero k] (ha : 0<a) (b n : ℤ) (hb : IsCoprime (k:ℤ) b) :
    ‖generalCoefficient (p^a) k (ℓ:ℤ) b n‖≤
      512*((p^a).gcd (k*ℓ):ℝ)/((p^a:ℕ):ℝ) := by
  by_cases hp2 : p=2
  · subst p
    by_cases hsmall : a≤3
    · exact goldbach_general_coefficient_small_two_power k ℓ a hsmall b n
    · have hz := generalCoefficient_sixteen_dvd (2^a) k (Nat.pow_dvd_pow 2 (by omega : 4≤a)) (ℓ:ℤ) b n
      rw [hz,norm_zero]
      positivity
  · by_cases ha1 : a=1
    · subst a
      simp only [pow_one]
      apply (goldbach_general_coefficient_odd_prime_bound p k ℓ hp2 b n hb).trans
      exact div_le_div_of_nonneg_right (by nlinarith [show (0:ℝ)≤p.gcd (k*ℓ) from Nat.cast_nonneg _]) (Nat.cast_nonneg p)
    · have hz := generalCoefficient_odd_prime_sq (p^a) k p hp2
        (Nat.pow_dvd_pow p (by omega : 2≤a)) (ℓ:ℤ) b n
      rw [hz,norm_zero]
      positivity

end PrimeSquares
