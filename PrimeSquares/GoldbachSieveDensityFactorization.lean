import PrimeSquares.GoldbachSievePrimeAdjunction
import PrimeSquares.GoldbachSieveDensityMultiplicative

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_normalized_factor_prime_product (R : ℝ) (hR : 3≤R)
    (K ℓ : ℕ) [NeZero K] (h24 : 24∣ℓ*K) (b n c : ℤ)
    (hn : ((n-(ℓ:ℤ)*b:ℤ):ZMod 24)=1) (S : Finset ℕ)
    (hS : ∀ p∈S,p.Prime ∧ 3 < p ∧ p.Coprime K ∧
      IsUnit ((ℓ:ℤ):ZMod p) ∧ ((ℓ:ℤ):ZMod p)*(b:ZMod p)=(c:ZMod p))
    (hb : IsCoprime ((K*(∏ p∈S,p):ℕ):ℤ) b) :
    goldbachArithmeticFactor R (K*(∏ p∈S,p)) (ℓ:ℤ) b n/
        ((K*(∏ p∈S,p)).totient:ℂ)=
      goldbachArithmeticFactor R K (ℓ:ℤ) b n/(K.totient:ℂ)*
        (∏ p∈S,(goldbachLocalDensity R p (n-c) n:ℂ)) := by
  classical
  revert hS hb
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    simp only [prod_empty,mul_one]
  | @insert p S hpS ih =>
    intro hS hb
    obtain ⟨hprime,hp,hpK,hℓ,hbc⟩ := hS p (mem_insert_self p S)
    have : Fact p.Prime := ⟨hprime⟩
    have hS' : ∀ q∈S,q.Prime ∧ 3 < q ∧ q.Coprime K ∧
        IsUnit ((ℓ:ℤ):ZMod q) ∧ ((ℓ:ℤ):ZMod q)*(b:ZMod q)=(c:ZMod q) :=
      fun q hq=>hS q (mem_insert_of_mem hq)
    let d := ∏ q∈S,q
    have hd0 : d≠0 := prod_ne_zero_iff.mpr (fun q hq=>(hS' q hq).1.ne_zero)
    have : NeZero d := ⟨hd0⟩
    have hpD : p.Coprime d := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply (Nat.coprime_primes hprime (hS' q hq).1).mpr
      intro heq
      exact hpS (heq ▸ hq)
    have hpKd : p.Coprime (K*d) := hpK.mul_right hpD
    have hmul : K*(∏ q∈insert p S,q)=(K*d)*p := by
      rw [prod_insert hpS]
      dsimp only [d]
      ring
    rw [hmul] at hb ⊢
    have hb₀ : IsCoprime ((K*d:ℕ):ℤ) b :=
      integer_coprime_of_nat_dvd (K*d) (K*d*p) b hb (dvd_mul_right (K*d) p)
    have h24' : 24∣ℓ*(K*d) := by simpa only [mul_assoc] using h24.mul_right d
    rw [goldbach_normalized_factor_adjoin_prime R hR p (K*d) ℓ hp hpKd h24' b n c hb hn hℓ hbc,
      ih hS' hb₀,prod_insert hpS]
    ring

theorem goldbach_sieve_density_factorization (R : ℝ) (hR : 3≤R)
    (K ℓ d : ℕ) [NeZero K] (hd : Squarefree d) (hKd : K.Coprime d)
    (h24 : 24∣ℓ*K) (b n c : ℤ)
    (hn : ((n-(ℓ:ℤ)*b:ℤ):ZMod 24)=1)
    (hS : ∀ p∈d.primeFactors,3 < p ∧ IsUnit ((ℓ:ℤ):ZMod p) ∧
      ((ℓ:ℤ):ZMod p)*(b:ZMod p)=(c:ZMod p))
    (hb : IsCoprime ((K*d:ℕ):ℤ) b) :
    goldbachArithmeticFactor R (K*d) (ℓ:ℤ) b n/((K*d).totient:ℂ)=
      goldbachArithmeticFactor R K (ℓ:ℤ) b n/(K.totient:ℂ)*
        ((goldbachSieveOmega (fun p=>goldbachLocalDensity R p (n-c) n) d/(d:ℝ):ℝ):ℂ) := by
  have hS' : ∀ p∈d.primeFactors,p.Prime ∧ 3 < p ∧ p.Coprime K ∧
      IsUnit ((ℓ:ℤ):ZMod p) ∧ ((ℓ:ℤ):ZMod p)*(b:ZMod p)=(c:ZMod p) := by
    intro p hp
    obtain ⟨hlarge,hunit,hphase⟩ := hS p hp
    exact ⟨Nat.prime_of_mem_primeFactors hp,hlarge,
      Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_primeFactors hp) hKd.symm,hunit,hphase⟩
  have hb' : IsCoprime ((K*(∏ p∈d.primeFactors,p):ℕ):ℤ) b := by
    simpa only [Nat.prod_primeFactors_of_squarefree hd] using hb
  have h := goldbach_normalized_factor_prime_product R hR K ℓ h24 b n c hn d.primeFactors hS' hb'
  rw [Nat.prod_primeFactors_of_squarefree hd] at h
  rw [goldbach_sieve_omega_div _ d hd.ne_zero]
  push_cast
  exact h

end PrimeSquares
