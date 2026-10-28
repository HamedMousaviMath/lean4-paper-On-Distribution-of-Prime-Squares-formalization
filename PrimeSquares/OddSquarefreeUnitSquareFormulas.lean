import PrimeSquares.UniformUnitSquareFibers
import PrimeSquares.UnitSquareDensityProducts

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem unitSquareCard_primeProduct_totient (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) :
    2^S.card*unitSquareCard (∏ p ∈ S, p)=(∏ p ∈ S, p).totient := by
  have hphi : (∏ p ∈ S, p).totient=∏ p ∈ S, p.totient :=
    multiplicative_prime_product Nat.totient Nat.totient_one
      (fun _ _ _ _ h => Nat.totient_mul h) S (fun p hp => (hS p hp).1)
  rw [hphi, unitSquareCard_primeProduct S (fun p hp => (hS p hp).1)]
  calc
    _ = ∏ p ∈ S, 2*unitSquareCard p := by rw [Finset.prod_mul_distrib,Finset.prod_const]
    _ = ∏ p ∈ S, p.totient := by
      apply Finset.prod_congr rfl
      intro p hp
      have : Fact p.Prime := ⟨(hS p hp).1⟩
      rw [unitSquareCard_eq,unitSquareResidues_prime_card p (hS p hp).2,
        Nat.totient_prime (hS p hp).1]

theorem odd_primeFactors (q : ℕ) (hq : Odd q) :
    ∀ p ∈ q.primeFactors, p.Prime ∧ p ≠ 2 := by
  intro p hp
  refine ⟨Nat.prime_of_mem_primeFactors hp,?_⟩
  intro he
  exact hq.not_two_dvd_nat (he ▸ Nat.dvd_of_mem_primeFactors hp)

theorem oddSquarefree_unitSquareCard_factor (q : ℕ) (hq : Odd q) (hs : Squarefree q) :
    2^q.primeFactors.card*unitSquareCard q=q.totient := by
  have h := unitSquareCard_primeProduct_totient q.primeFactors (odd_primeFactors q hq)
  simpa only [Nat.prod_primeFactors_of_squarefree hs] using h

theorem oddSquarefree_unitSquareCard_real (q : ℕ) [NeZero q] (hq : Odd q)
    (hs : Squarefree q) :
    ((unitSquareResidues q).card:ℝ)=(q.totient:ℝ)/(2:ℝ)^q.primeFactors.card := by
  have h : (2:ℝ)^q.primeFactors.card*(unitSquareCard q:ℝ)=(q.totient:ℝ) := by
    exact_mod_cast oddSquarefree_unitSquareCard_factor q hq hs
  rw [unitSquareCard_eq] at h
  apply (eq_div_iff (by positivity : (2:ℝ)^q.primeFactors.card≠0)).mpr
  nlinarith

theorem oddSquarefree_unitSquareRoots_card (q : ℕ) [NeZero q] (hq : Odd q)
    (hs : Squarefree q) (a : ZMod q) (ha : a ∈ unitSquareResidues q) :
    (unitSquareRoots q a).card=2^q.primeFactors.card := by
  have h1 := unitSquareRoots_kernel_factor q
  have h2 := oddSquarefree_unitSquareCard_factor q hq hs
  rw [unitSquareCard_eq] at h2
  rw [unitSquareRoots_card_eq_kernel q a ha]
  exact Nat.eq_of_mul_eq_mul_right (Finset.card_pos.mpr (unitSquareResidues_nonempty q))
    (h1.trans h2.symm)

theorem oddSquarefree_unitSquareSpacing (q : ℕ) [NeZero q] (hq : Odd q)
    (hs : Squarefree q) :
    unitSquareSpacing q=∏ p ∈ q.primeFactors, (2*(p:ℝ))/((p:ℝ)-1) := by
  have hS := odd_primeFactors q hq
  have h := unitSquareSpacing_primeProduct q.primeFactors (fun p hp => (hS p hp).1)
  rw [Nat.prod_primeFactors_of_squarefree hs] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro p hp
  have : Fact p.Prime := ⟨(hS p hp).1⟩
  rw [unitSquareDensity_prime,primeResidueDensity_formula p (hS p hp).2]
  simp only [inv_div]

end PrimeSquares
