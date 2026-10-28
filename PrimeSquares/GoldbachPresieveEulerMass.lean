import PrimeSquares.GoldbachPresieveDecay

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_presieve_density_prime_product (P : Finset ℕ) (g : ℕ→ℝ)
    (hg1 : g 1=1)
    (hgmul : ∀ d e : ℕ,Squarefree d→Squarefree e→d.Coprime e→
      d.primeFactors⊆P→e.primeFactors⊆P→g (d*e)=g d*g e)
    (d : ℕ) (hd : Squarefree d) (hsupp : d.primeFactors⊆P) :
    g d=∏ p∈d.primeFactors,g p := by
  classical
  have hprod : ∀ S : Finset ℕ,(∀ p∈S,p.Prime)→S⊆P→
      g (∏ p∈S,p)=∏ p∈S,g p := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ _
      simp only [prod_empty,hg1]
    | @insert p S hpS ih =>
      intro hprime hsub
      have hp := hprime p (mem_insert_self p S)
      have hS : ∀ q∈S,q.Prime := fun q hq=>hprime q (mem_insert_of_mem hq)
      have hSP : S⊆P := fun q hq=>hsub (mem_insert_of_mem hq)
      have hcop : p.Coprime (∏ q∈S,q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        exact (Nat.coprime_primes hp (hS q hq)).mpr (fun heq=>hpS (heq ▸ hq))
      have hsq : Squarefree (∏ q∈S,q) := by
        apply Finset.squarefree_prod_of_pairwise_isCoprime
        · intro q hq r hr hqr
          exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hS q hq) (hS r hr)).mpr hqr)
        · intro q hq
          exact (hS q hq).squarefree
      have hpP : p.primeFactors⊆P := by
        rw [hp.primeFactors]
        exact singleton_subset_iff.mpr (hsub (mem_insert_self p S))
      have hdP : (∏ q∈S,q).primeFactors⊆P := by rw [Nat.primeFactors_prod hS];exact hSP
      rw [prod_insert hpS,hgmul p _ hp.squarefree hsq hcop hpP hdP,ih hS hSP,prod_insert hpS]
  have h := hprod d.primeFactors (fun p hp=>Nat.prime_of_mem_primeFactors hp) hsupp
  rw [Nat.prod_primeFactors_of_squarefree hd] at h
  exact h

theorem goldbach_presieve_outer_mass (D P : Finset ℕ) (u g : ℕ→ℝ)
    (hsq : ∀ d∈D,Squarefree d) (hsupp : ∀ d∈D,d.primeFactors⊆P)
    (hu : ∀ d∈D,|u d|≤1) (hg : ∀ p∈P,0≤g p)
    (heval : ∀ d∈D,g d=∏ p∈d.primeFactors,g p) :
    (∑ d∈D,|u d| * g d)≤∏ p∈P,(1+g p) := by
  classical
  have hinj : Set.InjOn Nat.primeFactors (↑D : Set ℕ) := by
    intro d hd e he hde
    rw [←Nat.prod_primeFactors_of_squarefree (hsq d hd),hde,
      Nat.prod_primeFactors_of_squarefree (hsq e he)]
  have hsub : D.image Nat.primeFactors⊆P.powerset := by
    intro S hS
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hS
    exact mem_powerset.mpr (hsupp d hd)
  calc
    _≤∑ d∈D,g d := by
      apply sum_le_sum
      intro d hd
      have hgd : 0≤g d := by
        rw [heval d hd]
        exact prod_nonneg (fun p hp=>hg p (hsupp d hd hp))
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hu d hd) hgd
    _=∑ d∈D,∏ p∈d.primeFactors,g p := sum_congr rfl heval
    _=∑ S∈D.image Nat.primeFactors,∏ p∈S,g p := by rw [sum_image hinj]
    _≤∑ S∈P.powerset,∏ p∈S,g p := sum_le_sum_of_subset_of_nonneg hsub (by
      intro S hS _
      exact prod_nonneg (fun p hp=>hg p ((mem_powerset.mp hS) hp)))
    _=_ := (prod_one_add P).symm

theorem goldbach_presieve_outer_product (P : Finset ℕ) (g : ℕ→ℝ)
    (hg : ∀ p∈P,0≤g p ∧ g p < 1) :
    0 < (∏ p∈P,(1-g p)) ∧
      (∏ p∈P,(1+g p))≤(∏ p∈P,(1-g p))⁻¹ := by
  refine ⟨prod_pos (fun p hp=>sub_pos.mpr (hg p hp).2),?_⟩
  have hpoint (p : ℕ) (hp : p∈P) : 1+g p≤(1-g p)⁻¹ := by
    rw [←one_div]
    apply (le_div_iff₀ (sub_pos.mpr (hg p hp).2)).mpr
    nlinarith [sq_nonneg (g p)]
  have h := prod_le_prod₀ (fun p hp=>by linarith [(hg p hp).1]) hpoint
  simpa only [prod_inv_distrib] using h

theorem goldbach_presieve_outer_mass_ratio (D P : Finset ℕ) (u g : ℕ→ℝ)
    (hsq : ∀ d∈D,Squarefree d) (hsupp : ∀ d∈D,d.primeFactors⊆P)
    (hu : ∀ d∈D,|u d|≤1) (hg : ∀ p∈P,0≤g p ∧ g p < 1)
    (heval : ∀ d∈D,g d=∏ p∈d.primeFactors,g p) :
    (∑ d∈D,|u d| * g d)/(∏ p∈P,(1-g p))≤((∏ p∈P,(1-g p))⁻¹)^2 := by
  have hM := (goldbach_presieve_outer_mass D P u g hsq hsupp hu (fun p hp=>(hg p hp).1) heval).trans
    (goldbach_presieve_outer_product P g hg).2
  have hV := (goldbach_presieve_outer_product P g hg).1
  apply (div_le_div_of_nonneg_right hM hV.le).trans_eq
  field_simp

theorem goldbach_presieve_inverse_polylog (V N z A K κ : ℝ)
    (hN : 1 < N) (hz : 2≤z) (hA : 0≤A) (hK : 0≤K) (hκ : 0≤κ)
    (hlog : Real.log z≤A*Real.log N)
    (hInv : V⁻¹≤K*(Real.log z/Real.log 2)^κ) :
    V⁻¹≤(K*(A/Real.log 2)^κ)*(Real.log N)^κ := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN0 := (Real.log_pos hN).le
  have hratio0 : 0≤Real.log z/Real.log 2 := div_nonneg (Real.log_nonneg (by linarith)) h2.le
  have hratio : Real.log z/Real.log 2≤(A/Real.log 2)*Real.log N := by
    apply (div_le_div_of_nonneg_right hlog h2.le).trans_eq
    ring
  calc
    _≤K*((A/Real.log 2)*Real.log N)^κ :=
      hInv.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hratio0 hratio hκ) hK)
    _=_ := by rw [Real.mul_rpow (div_nonneg hA h2.le) hN0];ring

end PrimeSquares
