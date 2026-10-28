import PrimeSquares.GoldbachRankinLocal
import PrimeSquares.ElementaryPrimeProduct

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachPrimeProductConstant : ℝ := 12+2/Real.log 3

theorem goldbachPrimeProductConstant_pos : 0<goldbachPrimeProductConstant := by
  have h : 0<Real.log (3:ℝ) := Real.log_pos (by norm_num)
  unfold goldbachPrimeProductConstant
  positivity

theorem goldbach_rankin_prime_rpow {R σ : ℝ} (_hR : 2≤R) (hσ : 0≤σ)
    (hbudget : σ*Real.log R≤1) (p : ℕ) (hp : p.Prime) (hpR : (p:ℝ)≤R) :
    (p:ℝ)^(-1+σ)≤Real.exp 1/(p:ℝ) := by
  have hpp : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hlogs := Real.log_le_log hpp hpR
  have hb : (p:ℝ)^σ≤Real.exp 1 := by
    rw [Real.rpow_def_of_pos hpp]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hlogs hσ])
  calc
    _=(p:ℝ)^(-1:ℝ)*(p:ℝ)^σ := by rw [←Real.rpow_add hpp]
    _≤(p:ℝ)^(-1:ℝ)*Real.exp 1 := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hpp.le _)
    _=_ := by rw [Real.rpow_neg_one];ring

theorem goldbach_prime_subset_inclusive_log {R : ℝ} (hR : 2≤R) (S : Finset ℕ)
    (hS : ∀ p∈S,p.Prime ∧ (p:ℝ)≤R) :
    primeSubsetMass S≤goldbachPrimeProductConstant*Real.log (2*R) := by
  have hf : 2≤⌊R⌋₊ := (Nat.le_floor_iff (by linarith : 0≤R)).mpr hR
  have hQ : 3≤⌊R⌋₊+1 := by omega
  have hb := primeSubsetMass_le_log S (⌊R⌋₊+1) hQ (fun p hp=>⟨(hS p hp).1,by
    have hh : p≤⌊R⌋₊ := (Nat.le_floor_iff (by linarith : 0≤R)).mpr (hS p hp).2
    omega⟩)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ goldbachPrimeProductConstant_pos.le
  apply Real.log_le_log (by positivity)
  have hfloor := Nat.floor_le (by linarith : 0≤R)
  push_cast
  linarith

theorem goldbach_rankin_euler_log :
    ∃ K : ℕ,0<K ∧ ∀ R σ : ℝ,2≤R →0≤σ →σ≤1/2 →σ*Real.log R≤1 →
      ∀ D : ℕ,D≠0 →(∀ p∈D.primeFactors,(p:ℝ)≤R) →
      (∑ q∈D.divisors,goldbachRankinWeight σ q)≤
        (goldbachPrimeProductConstant*Real.log (2*R))^K := by
  obtain ⟨C,hC,hlocal⟩ := goldbach_rankin_local_uniform
  let K := ⌈C*Real.exp 1⌉₊+1
  have hK : 0<K := by dsimp [K];omega
  have hCK : C*Real.exp 1≤(K:ℝ) := (Nat.le_ceil _).trans (by dsimp [K];push_cast;linarith)
  refine ⟨K,hK,?_⟩
  intro R σ hR hσ0 hσ1 hσR D hD hDR
  have hfactor (p : ℕ) (hpD : p∈D.primeFactors) :
      (∑ j∈range (D.factorization p+1),((j:ℝ)+1)^11*((p:ℝ)^(-1+σ))^j)≤
        (1+1/(p:ℝ))^K := by
    have hp := Nat.prime_of_mem_primeFactors hpD
    have hpp : (0:ℝ)<p := by exact_mod_cast hp.pos
    calc
      _≤1+C*(p:ℝ)^(-1+σ) := hlocal p hp σ hσ1 _
      _≤1+C*(Real.exp 1/(p:ℝ)) := by
        linarith [mul_le_mul_of_nonneg_left (goldbach_rankin_prime_rpow hR hσ0 hσR p hp (hDR p hpD)) hC.le]
      _=1+(C*Real.exp 1)/(p:ℝ) := by ring
      _≤1+(K:ℝ)/(p:ℝ) := by linarith [div_le_div_of_nonneg_right hCK hpp.le]
      _≤_ := by
        simpa only [mul_one_div] using one_add_mul_le_pow
          (by linarith [div_nonneg (by norm_num : (0:ℝ)≤1) hpp.le] : (-2:ℝ)≤1/(p:ℝ)) K
  rw [goldbach_rankin_divisor_euler σ D hD]
  calc
    _≤∏ p∈D.primeFactors,(1+1/(p:ℝ))^K :=
      prod_le_prod₀ (fun p _=>sum_nonneg (fun j _=>by positivity)) hfactor
    _=(primeSubsetMass D.primeFactors)^K := by simp only [primeSubsetMass,one_div,prod_pow]
    _≤_ := pow_le_pow_left₀ (by unfold primeSubsetMass;positivity)
      (goldbach_prime_subset_inclusive_log hR D.primeFactors
        (fun p hp=>⟨Nat.prime_of_mem_primeFactors hp,hDR p hp⟩)) K

theorem goldbach_rankin_tail_log_bound :
    ∃ K : ℕ,0<K ∧ ∀ R σ Y : ℝ,2≤R →0<σ →σ≤1/2 →σ*Real.log R≤1 →0<Y →
      ∀ D : ℕ,D≠0 →(∀ p∈D.primeFactors,(p:ℝ)≤R) →∀ S : Finset ℕ,
      (∀ q∈S,q∈D.divisors ∧ Y<(q:ℝ)) →
      (∑ q∈S,(q.divisors.card:ℝ)^11/(q:ℝ))≤
        Y^(-σ)*(goldbachPrimeProductConstant*Real.log (2*R))^K := by
  obtain ⟨K,hK,hbound⟩ := goldbach_rankin_euler_log
  refine ⟨K,hK,?_⟩
  intro R σ Y hR hσ hσ1 hσR hY D hD hDR S hS
  have h := goldbach_finite_rankin_euler_bound hσ hY D hD S hS
  rw [←goldbach_rankin_divisor_euler σ D hD] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hbound R σ hR hσ.le hσ1 hσR D hD hDR)
    (Real.rpow_nonneg hY.le _))

end PrimeSquares
