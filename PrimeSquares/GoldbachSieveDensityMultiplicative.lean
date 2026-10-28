import PrimeSquares.GoldbachSieveDensityBounds

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachPrimeDensityProduct (f : ℕ→ℝ) (d : ℕ) : ℝ :=
  ∏ p∈d.primeFactors,f p

noncomputable def goldbachSieveOmega (f : ℕ→ℝ) (d : ℕ) : ℝ :=
  (d:ℝ)*goldbachPrimeDensityProduct f d

theorem goldbach_sieve_omega_one (f : ℕ→ℝ) : goldbachSieveOmega f 1=1 := by
  simp only [goldbachSieveOmega,goldbachPrimeDensityProduct,Nat.primeFactors_one,
    prod_empty,Nat.cast_one,mul_one]

theorem goldbach_sieve_omega_prime (f : ℕ→ℝ) (p : ℕ) (hp : p.Prime) :
    goldbachSieveOmega f p/(p:ℝ)=f p := by
  have hp' : (p:ℝ)≠0 := by exact_mod_cast hp.ne_zero
  simp only [goldbachSieveOmega,goldbachPrimeDensityProduct,hp.primeFactors,prod_singleton]
  exact mul_div_cancel_left₀ (f p) hp'

theorem goldbach_sieve_omega_mul (f : ℕ→ℝ) (a b : ℕ) (hab : a.Coprime b) :
    goldbachSieveOmega f (a*b)=goldbachSieveOmega f a*goldbachSieveOmega f b := by
  by_cases ha : a=0
  · simp only [ha,goldbachSieveOmega,Nat.cast_zero,zero_mul]
  by_cases hb : b=0
  · simp only [hb,goldbachSieveOmega,Nat.cast_zero,mul_zero,zero_mul]
  rw [goldbachSieveOmega,goldbachSieveOmega,goldbachSieveOmega,
    goldbachPrimeDensityProduct,goldbachPrimeDensityProduct,goldbachPrimeDensityProduct,
    Nat.primeFactors_mul ha hb,prod_union hab.disjoint_primeFactors,Nat.cast_mul]
  ring

theorem goldbach_sieve_omega_div (f : ℕ→ℝ) (d : ℕ) (hd : d≠0) :
    goldbachSieveOmega f d/(d:ℝ)=∏ p∈d.primeFactors,f p := by
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hd)

end PrimeSquares
