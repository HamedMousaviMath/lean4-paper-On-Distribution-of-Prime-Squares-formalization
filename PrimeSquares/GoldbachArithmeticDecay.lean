import PrimeSquares.GoldbachPrimePowerBounds
import PrimeSquares.DivisorProductGrowth

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_gcd_ratio_multiplicative (c m n : ℕ) (hc : m.Coprime n) :
    ((m*n).gcd c:ℝ)/((m*n:ℕ):ℝ)=((m.gcd c:ℝ)/(m:ℝ))*((n.gcd c:ℝ)/(n:ℝ)) := by
  have hg : (m*n).gcd c=m.gcd c*n.gcd c := by
    simpa only [Nat.gcd_comm] using hc.gcd_mul c
  simp only [hg,Nat.cast_mul,mul_div_mul_comm]

theorem goldbach_gcd_ratio_factorization (q c : ℕ) (hq : 0<q) :
    (q.gcd c:ℝ)/(q:ℝ)=
      ∏ p∈q.primeFactors,((p^q.factorization p).gcd c:ℝ)/((p^q.factorization p:ℕ):ℝ) := by
  exact Nat.multiplicative_factorization (fun n : ℕ => (n.gcd c:ℝ)/(n:ℝ))
    (fun m n h => goldbach_gcd_ratio_multiplicative c m n h) (by simp) hq.ne'

theorem goldbach_two_pow_primeFactors_le_divisors (q : ℕ) (hq : 0<q) :
    (2:ℝ)^q.primeFactors.card≤(q.divisors.card:ℝ) := by
  rw [divisors_card_primePower_product q hq,←prod_const]
  apply prod_le_prod₀
  · intro p _;norm_num
  · intro p hp
    have hf : q.factorization p≠0 := by
      change p∈q.factorization.support at hp
      exact Finsupp.mem_support_iff.mp hp
    have hh : (1:ℝ)≤q.factorization p := by exact_mod_cast (show 1≤q.factorization p by omega)
    linarith

theorem goldbach_prime_factor_weight_le_divisors (q j : ℕ) (hq : 0<q) :
    ((2:ℝ)^j)^q.primeFactors.card≤(q.divisors.card:ℝ)^j := by
  rw [←pow_mul,Nat.mul_comm j q.primeFactors.card,pow_mul]
  exact pow_le_pow_left₀ (by positivity) (goldbach_two_pow_primeFactors_le_divisors q hq) j

theorem goldbach_general_coefficient_factor_bound (q k ℓ : ℕ) [NeZero q] [NeZero k]
    (b n : ℤ) (hb : IsCoprime (k:ℤ) b) :
    ‖generalCoefficient q k (ℓ:ℤ) b n‖≤
      (512:ℝ)^q.primeFactors.card*(q.gcd (k*ℓ):ℝ)/(q:ℝ) := by
  classical
  have he := Nat.multiplicative_factorization (fun q => generalCoefficient q k (ℓ:ℤ) b n)
    (fun m t h => generalCoefficient_mul m t k h (ℓ:ℤ) b n)
    (generalCoefficient_one k (ℓ:ℤ) b n) (NeZero.ne q)
  change generalCoefficient q k (ℓ:ℤ) b n=
    ∏ p∈q.primeFactors,generalCoefficient (p^q.factorization p) k (ℓ:ℤ) b n at he
  rw [he,norm_prod]
  calc
    _≤∏ p∈q.primeFactors,512*
        (((p^q.factorization p).gcd (k*ℓ):ℝ)/((p^q.factorization p:ℕ):ℝ)) := by
      apply prod_le_prod₀
      · intro p _;exact norm_nonneg _
      · intro p hp
        have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
        have hf : 0<q.factorization p := by
          have hz : q.factorization p≠0 := Finsupp.mem_support_iff.mp hp
          omega
        simpa only [mul_div_assoc] using
          goldbach_general_coefficient_prime_power p (q.factorization p) k ℓ hf b n hb
    _=(512:ℝ)^q.primeFactors.card*((q.gcd (k*ℓ):ℝ)/(q:ℝ)) := by
      rw [prod_mul_distrib,prod_const,←goldbach_gcd_ratio_factorization q (k*ℓ) (NeZero.pos q)]
    _=_ := by ring

theorem goldbach_general_coefficient_divisor_bound (q k ℓ : ℕ) [NeZero q] [NeZero k]
    (b n : ℤ) (hb : IsCoprime (k:ℤ) b) :
    ‖generalCoefficient q k (ℓ:ℤ) b n‖≤
      (q.divisors.card:ℝ)^9*(q.gcd (k*ℓ):ℝ)/(q:ℝ) := by
  have hw : (512:ℝ)^q.primeFactors.card≤(q.divisors.card:ℝ)^9 := by
    simpa only [show (2:ℝ)^9=512 by norm_num] using
      goldbach_prime_factor_weight_le_divisors q 9 (NeZero.pos q)
  exact (goldbach_general_coefficient_factor_bound q k ℓ b n hb).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg _)) (Nat.cast_nonneg _))

theorem goldbach_principal_square_divisor_bound (q : ℕ) [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    ‖principalSquareSum q a‖≤(q.divisors.card:ℝ)^3/Real.sqrt q := by
  have hw : (8:ℝ)^q.primeFactors.card≤(q.divisors.card:ℝ)^3 := by
    simpa only [show (2:ℝ)^3=8 by norm_num] using
      goldbach_prime_factor_weight_le_divisors q 3 (NeZero.pos q)
  have hg := norm_twistedSquareSum_finite_bound q 1 a ha
  rw [twistedSquareSum_principal] at hg
  exact hg.trans (div_le_div_of_nonneg_right hw (Real.sqrt_nonneg _))

end PrimeSquares
