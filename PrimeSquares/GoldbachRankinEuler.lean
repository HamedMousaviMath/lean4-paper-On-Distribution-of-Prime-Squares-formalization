import PrimeSquares.GoldbachPositiveSingularComplete
import PrimeSquares.RenDivisorBudget

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachRankinWeight (σ : ℝ) (q : ℕ) : ℝ :=
  (q.divisors.card:ℝ)^11*(q:ℝ)^(-1+σ)

theorem goldbach_rankin_weight_nonnegative (σ : ℝ) (q : ℕ) : 0≤goldbachRankinWeight σ q := by
  unfold goldbachRankinWeight
  positivity

theorem goldbach_rankin_weight_multiplicative (σ : ℝ) (m n : ℕ) (h : m.Coprime n) :
    goldbachRankinWeight σ (m*n)=goldbachRankinWeight σ m*goldbachRankinWeight σ n := by
  simp only [goldbachRankinWeight,h.card_divisors_mul,Nat.cast_mul,mul_pow,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

theorem goldbach_rankin_weight_prime_power (σ : ℝ) (p j : ℕ) (hp : p.Prime) :
    goldbachRankinWeight σ (p^j)=((j:ℝ)+1)^11*((p:ℝ)^(-1+σ))^j := by
  rw [goldbachRankinWeight,Nat.divisors_prime_pow hp,card_map,card_range,
    Nat.cast_add,Nat.cast_one,Nat.cast_pow,←Real.rpow_pow_comm (Nat.cast_nonneg p)]

theorem goldbach_rankin_divisor_euler (σ : ℝ) (D : ℕ) (hD : D≠0) :
    (∑ q∈D.divisors,goldbachRankinWeight σ q)=
      ∏ p∈D.primeFactors,∑ j∈range (D.factorization p+1),
        ((j:ℝ)+1)^11*((p:ℝ)^(-1+σ))^j := by
  have he := sum_divisors_multiplicative (goldbachRankinWeight σ)
    (by simp [goldbachRankinWeight]) (by simp [goldbachRankinWeight])
    (goldbach_rankin_weight_multiplicative σ) D hD
  rw [he]
  apply prod_congr rfl
  intro p hp
  apply sum_congr rfl
  intro j _
  exact goldbach_rankin_weight_prime_power σ p j (Nat.prime_of_mem_primeFactors hp)

theorem goldbach_rankin_pointwise {σ Y : ℝ} (hσ : 0<σ) (hY : 0<Y)
    (q : ℕ) (hq : Y<(q:ℝ)) :
    (q.divisors.card:ℝ)^11/(q:ℝ)≤Y^(-σ)*goldbachRankinWeight σ q := by
  have hqp : (0:ℝ)<q := hY.trans hq
  have hb := Real.rpow_le_rpow_of_nonpos hY hq.le (by linarith : -σ≤0)
  have he : (q.divisors.card:ℝ)^11/(q:ℝ)=(q:ℝ)^(-σ)*goldbachRankinWeight σ q := by
    symm
    unfold goldbachRankinWeight
    calc
      _=(q.divisors.card:ℝ)^11*((q:ℝ)^(-σ)*(q:ℝ)^(-1+σ)) := by ring
      _=(q.divisors.card:ℝ)^11*(q:ℝ)^(-1:ℝ) := by
        rw [←Real.rpow_add hqp,show -σ+(-1+σ)=(-1:ℝ) by ring]
      _=_ := by rw [Real.rpow_neg_one];ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hb (goldbach_rankin_weight_nonnegative σ q)

theorem goldbach_finite_rankin_euler_bound {σ Y : ℝ} (hσ : 0<σ) (hY : 0<Y)
    (D : ℕ) (hD : D≠0) (S : Finset ℕ)
    (hS : ∀ q∈S,q∈D.divisors ∧ Y<(q:ℝ)) :
    (∑ q∈S,(q.divisors.card:ℝ)^11/(q:ℝ))≤
      Y^(-σ)*(∏ p∈D.primeFactors,∑ j∈range (D.factorization p+1),
        ((j:ℝ)+1)^11*((p:ℝ)^(-1+σ))^j) := by
  calc
    _≤∑ q∈S,Y^(-σ)*goldbachRankinWeight σ q :=
      sum_le_sum (fun q hq=>goldbach_rankin_pointwise hσ hY q (hS q hq).2)
    _=Y^(-σ)*(∑ q∈S,goldbachRankinWeight σ q) := by rw [mul_sum]
    _≤Y^(-σ)*(∑ q∈D.divisors,goldbachRankinWeight σ q) :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg
        (fun q hq=>(hS q hq).1) (fun q _ _=>goldbach_rankin_weight_nonnegative σ q))
        (Real.rpow_nonneg hY.le _)
    _=_ := by rw [goldbach_rankin_divisor_euler σ D hD]

end PrimeSquares
