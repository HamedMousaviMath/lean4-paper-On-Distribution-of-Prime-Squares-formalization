import PrimeSquares.GoldbachHardMajorIdentity

set_option autoImplicit false
open Finset MeasureTheory
open scoped SchwartzMap
namespace PrimeSquares

noncomputable def goldbachCompletionDivisors (R : ℝ) : Finset ℕ :=
  (smoothEulerBound (⌊R⌋₊+1)).divisors

theorem goldbach_completion_bound_nezero (R : ℝ) : smoothEulerBound (⌊R⌋₊+1)≠0 :=
  pow_ne_zero _ (Nat.factorial_ne_zero _)

theorem goldbach_completion_bound_primes {R : ℝ} (hR : 2≤R) :
    ∀ p∈(smoothEulerBound (⌊R⌋₊+1)).primeFactors,(p:ℝ)≤R := by
  have hQ : 3≤⌊R⌋₊+1 := by
    have hh : 2≤⌊R⌋₊ := (Nat.le_floor_iff (by linarith : 0≤R)).mpr hR
    omega
  intro p hp
  exact (goldbach_prime_inclusive_cutoff (by linarith) p).mpr
    (smoothEulerBound_divisor_smooth _ hQ _ (dvd_refl _) p hp)

theorem goldbach_initial_coefficients_divisor_sum {R : ℝ} (hR : 2≤R)
    (k : ℕ) [NeZero k] (ℓ b n : ℤ) :
    (∑ q∈Icc 1 ⌊R⌋₊,generalCoefficient q k ℓ b n)=
      ∑ q∈(goldbachCompletionDivisors R).filter (fun q : ℕ=>(q:ℝ)≤R),generalCoefficient q k ℓ b n := by
  classical
  symm
  apply sum_subset
  · intro q hq
    obtain ⟨hd,hqR⟩ := mem_filter.mp hq
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,(Nat.le_floor_iff (by linarith : 0≤R)).mpr hqR⟩
  · intro q hq hn
    have hqp : 0<q := (mem_Icc.mp hq).1
    have hqR : (q:ℝ)≤R := (Nat.le_floor_iff (by linarith : 0≤R)).mp (mem_Icc.mp hq).2
    have hnd : q∉goldbachCompletionDivisors R := fun hd=>hn (mem_filter.mpr ⟨hd,hqR⟩)
    have hs : ∀ p∈q.primeFactors,(p:ℝ)≤R := by
      intro p hp
      have hpq : p≤q := Nat.le_of_dvd hqp (Nat.dvd_of_mem_primeFactors hp)
      exact (by exact_mod_cast hpq : (p:ℝ)≤q).trans hqR
    have hz := goldbach_smooth_coefficient_zero_off_bound hR k ℓ b n q hnd
    simpa only [goldbachSmoothCoefficient,ite_eq_left hs] using hz

theorem goldbach_completion_arithmetic_split {R Y : ℝ} (hR : 2≤R) (hRY : R≤Y)
    (k : ℕ) [NeZero k] (ℓ b n : ℤ) (hb : IsCoprime (k:ℤ) b) :
    goldbachArithmeticFactor R k ℓ b n=
      (∑ q∈Icc 1 ⌊R⌋₊,generalCoefficient q k ℓ b n)+
      (∑ q∈(goldbachCompletionDivisors R).filter (fun q : ℕ=>R<(q:ℝ) ∧ (q:ℝ)≤Y),generalCoefficient q k ℓ b n)+
      ∑ q∈(goldbachCompletionDivisors R).filter (fun q : ℕ=>Y<(q:ℝ)),generalCoefficient q k ℓ b n := by
  classical
  rw [goldbach_arithmetic_factor_finite_split hR k ℓ b n hb Y,goldbach_initial_coefficients_divisor_sum hR]
  congr 1
  have hpart := sum_filter_add_sum_filter_not
    ((goldbachCompletionDivisors R).filter (fun q : ℕ=>(q:ℝ)≤Y))
    (fun q : ℕ=>(q:ℝ)≤R) (fun q : ℕ=>generalCoefficient q k ℓ b n)
  have hsmall : ((goldbachCompletionDivisors R).filter (fun q : ℕ=>(q:ℝ)≤Y)).filter (fun q : ℕ=>(q:ℝ)≤R)=
      (goldbachCompletionDivisors R).filter (fun q : ℕ=>(q:ℝ)≤R) := by
    ext q
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨hq,_⟩,hr⟩;exact ⟨hq,hr⟩
    · rintro ⟨hq,hr⟩;exact ⟨⟨hq,hr.trans hRY⟩,hr⟩
  have hadded : ((goldbachCompletionDivisors R).filter (fun q : ℕ=>(q:ℝ)≤Y)).filter (fun q : ℕ=>¬(q:ℝ)≤R)=
      (goldbachCompletionDivisors R).filter (fun q : ℕ=>R<(q:ℝ) ∧ (q:ℝ)≤Y) := by
    ext q
    simp only [mem_filter,not_le]
    tauto
  rw [hsmall,hadded] at hpart
  exact hpart.symm

theorem goldbach_added_moduli_filter {R Y : ℝ} (hY : 0≤Y) :
    (Icc 1 ⌊Y⌋₊).filter (fun q : ℕ=>R<(q:ℝ) ∧ q∈goldbachCompletionDivisors R)=
      (goldbachCompletionDivisors R).filter (fun q : ℕ=>R<(q:ℝ) ∧ (q:ℝ)≤Y) := by
  classical
  ext q
  simp only [mem_filter,mem_Icc]
  constructor
  · rintro ⟨⟨_,hqY⟩,hr,hd⟩
    exact ⟨hd,hr,(Nat.le_floor_iff hY).mp hqY⟩
  · rintro ⟨hd,hr,hqY⟩
    exact ⟨⟨Nat.pos_of_mem_divisors hd,(Nat.le_floor_iff hY).mpr hqY⟩,hr,hd⟩

noncomputable def goldbachAddedCompletionCenters (R Y : ℝ) : Finset ℚ :=
  (sourceRationalCenters Y).filter (fun r : ℚ=>R<(r.den:ℝ) ∧ r.den∈goldbachCompletionDivisors R)

theorem goldbach_added_completion_centers_subset (R Y : ℝ) :
    goldbachAddedCompletionCenters R Y⊆(sourceRationalCenters Y).filter (fun r : ℚ=>R<(r.den:ℝ)) := by
  intro r hr
  exact mem_filter.mpr ⟨(mem_filter.mp hr).1,(mem_filter.mp hr).2.1⟩

theorem goldbach_added_completion_identity (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (N : ℕ) (hN : 0<N) (I : Finset (ℕ×ℕ)) (hI : ∀ i∈I,0 < i.1)
    (b : ℕ×ℕ→ℤ) (d : ℕ×ℕ→ℂ) {U W Y : ℝ} (hU : 2≤U) (hUN : U≤N) (hW : 2≤W)
    (hY : 0≤Y) (R : ℝ) (n : ℤ) :
    (∑ r∈goldbachAddedCompletionCenters R Y,realFourierPhase (-(n:ℝ)*(r:ℝ))*
      (∫ γ : ℝ,goldbachSmoothMajorFamilyIntegrand ψ N R I b d U W r γ*realFourierPhase (-(n:ℝ)*γ)))=
      ∑ i∈I,(d i*goldbachSingularIntegral ψ N i.1 R (n:ℝ) U W)/((i.1:ℂ)*(i.2.totient:ℂ))*
        (∑ q∈(goldbachCompletionDivisors R).filter (fun q : ℕ=>R<(q:ℝ) ∧ (q:ℝ)≤Y),
          generalCoefficient q i.2 (i.1:ℤ) (b i) n) := by
  classical
  let β := fun q : ℕ=>if R<(q:ℝ) ∧ q∈goldbachCompletionDivisors R then (1:ℂ) else 0
  have h := goldbach_smoothed_major_family_identity ψ hψ N hN I hI b d hU hUN hW R Y β n
  have hl : (∑ r∈sourceRationalCenters Y,β r.den*realFourierPhase (-(n:ℝ)*(r:ℝ))*
      (∫ γ : ℝ,goldbachSmoothMajorFamilyIntegrand ψ N R I b d U W r γ*realFourierPhase (-(n:ℝ)*γ)))=
      ∑ r∈goldbachAddedCompletionCenters R Y,realFourierPhase (-(n:ℝ)*(r:ℝ))*
        (∫ γ : ℝ,goldbachSmoothMajorFamilyIntegrand ψ N R I b d U W r γ*realFourierPhase (-(n:ℝ)*γ)) := by
    rw [goldbachAddedCompletionCenters,sum_filter]
    apply sum_congr rfl
    intro r _
    dsimp only [β]
    split_ifs <;> simp
  rw [←hl,h]
  apply sum_congr rfl
  intro i _
  congr 1
  rw [←goldbach_added_moduli_filter hY,sum_filter]
  apply sum_congr rfl
  intro q _
  dsimp only [β]
  split_ifs <;> simp

end PrimeSquares
