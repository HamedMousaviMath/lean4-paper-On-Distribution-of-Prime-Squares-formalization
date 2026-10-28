import PrimeSquares.CircleFourier

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

/-- Prime cutoffs at arbitrary real endpoints, including endpoints at primes. -/
noncomputable def goldbachPrimeCutoff (U : ℝ) : Finset ℕ :=
  (range (⌊U⌋₊+1)).filter Nat.Prime

theorem mem_goldbachPrimeCutoff {U : ℝ} (hU : 0≤U) (m : ℕ) :
    m∈goldbachPrimeCutoff U ↔ m.Prime ∧ (m:ℝ)≤U := by
  simp only [goldbachPrimeCutoff,mem_filter,mem_range,Nat.lt_succ_iff,
    Nat.le_floor_iff hU]
  exact and_comm

noncomputable def goldbachProgressionCutoff (N ℓ k a : ℕ) (W : ℝ) : Finset ℕ :=
  (goldbachPrimeCutoff W).filter (fun t => ℓ*t<N^2 ∧ t%k=a%k)

theorem mem_goldbachProgressionCutoff {N ℓ k a : ℕ} {W : ℝ}
    (hW : 0≤W) (t : ℕ) : t∈goldbachProgressionCutoff N ℓ k a W ↔
      t.Prime ∧ (t:ℝ)≤W ∧ ℓ*t<N^2 ∧ t%k=a%k := by
  simp only [goldbachProgressionCutoff,mem_filter,mem_goldbachPrimeCutoff hW]
  tauto

noncomputable def goldbachPrimeSquarePolynomial (U : ℝ) : C(PrimeCircle,ℂ) :=
  ∑ m∈goldbachPrimeCutoff U,fourier ((m^2:ℕ):ℤ)

noncomputable def goldbachProgressionPolynomial (N ℓ k a : ℕ) (W : ℝ) :
    C(PrimeCircle,ℂ) :=
  ∑ t∈goldbachProgressionCutoff N ℓ k a W,fourier ((ℓ*t:ℕ):ℤ)

noncomputable def goldbachCutoffPrimePairs (N ℓ k a n : ℕ) (U W : ℝ) :
    Finset (ℕ×ℕ) :=
  ((goldbachPrimeCutoff U)×ˢ(goldbachProgressionCutoff N ℓ k a W)).filter
    (fun x => x.1^2+ℓ*x.2=n)

theorem goldbach_finite_character_integral (j : ℤ) :
    (∫ θ : PrimeCircle,fourier j θ ∂AddCircle.haarAddCircle)=
      if j=0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T:=(1:ℝ)) j) 0
  simpa only [fourierCoeff,neg_zero,fourier_zero,one_smul,Pi.single_apply,
    eq_comm] using h

theorem goldbachPrimeSquarePolynomial_mul (N ℓ k a : ℕ) (U W : ℝ) :
    goldbachPrimeSquarePolynomial U*goldbachProgressionPolynomial N ℓ k a W=
      ∑ x∈(goldbachPrimeCutoff U)×ˢ(goldbachProgressionCutoff N ℓ k a W),
        fourier ((x.1^2+ℓ*x.2:ℕ):ℤ) := by
  ext θ
  simp only [goldbachPrimeSquarePolynomial,goldbachProgressionPolynomial,
    ContinuousMap.mul_apply,ContinuousMap.sum_apply,sum_product,sum_mul,mul_sum,
    Nat.cast_add,fourier_add]
  exact sum_comm

/-- Literal finite Fourier inversion for the unweighted prime-square/progression pair. -/
theorem goldbach_cutoff_fourier_inversion (N ℓ k a n : ℕ) (U W : ℝ) :
    (∫ θ : PrimeCircle,goldbachPrimeSquarePolynomial U θ*
      goldbachProgressionPolynomial N ℓ k a W θ*fourier (-(n:ℤ)) θ
        ∂AddCircle.haarAddCircle)=
      ((goldbachCutoffPrimePairs N ℓ k a n U W).card:ℂ) := by
  classical
  have hexp (θ : PrimeCircle) : goldbachPrimeSquarePolynomial U θ*
      goldbachProgressionPolynomial N ℓ k a W θ*fourier (-(n:ℤ)) θ=
      ∑ x∈(goldbachPrimeCutoff U)×ˢ(goldbachProgressionCutoff N ℓ k a W),
        fourier (((x.1^2+ℓ*x.2:ℕ):ℤ)-(n:ℤ)) θ := by
    have he := congrArg (fun f : C(PrimeCircle,ℂ) => f θ)
      (goldbachPrimeSquarePolynomial_mul N ℓ k a U W)
    change goldbachPrimeSquarePolynomial U θ*goldbachProgressionPolynomial N ℓ k a W θ=_ at he
    rw [he]
    simp only [ContinuousMap.sum_apply,sum_mul,sub_eq_add_neg,fourier_add]
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun x _ => (fourier _).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  simp only [goldbach_finite_character_integral,sub_eq_zero,Nat.cast_inj]
  simp only [goldbachCutoffPrimePairs,card_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero]

theorem mem_goldbachCutoffPrimePairs {N ℓ k a n : ℕ} {U W : ℝ}
    (hU : 0≤U) (hW : 0≤W) (m t : ℕ) :
    (m,t)∈goldbachCutoffPrimePairs N ℓ k a n U W ↔
      m.Prime ∧ (m:ℝ)≤U ∧ t.Prime ∧ (t:ℝ)≤W ∧
        ℓ*t<N^2 ∧ t%k=a%k ∧ m^2+ℓ*t=n := by
  simp only [goldbachCutoffPrimePairs,mem_filter,mem_product,
    mem_goldbachPrimeCutoff hU,mem_goldbachProgressionCutoff hW]
  tauto

/-- The literal untruncated natural-number representation count; the equation
itself supplies these finite bounds when the multiplier is positive. -/
noncomputable def goldbachProgressionPairs (ℓ k a n : ℕ) : Finset (ℕ×ℕ) :=
  ((range (n+1))×ˢ(range (n+1))).filter
    (fun x => x.1.Prime ∧ x.2.Prime ∧ x.2%k=a%k ∧ x.1^2+ℓ*x.2=n)

theorem goldbach_full_cutoffs_redundant {N ℓ k a n : ℕ} (hℓ : 1≤ℓ)
    (hn : n<N^2) :
    goldbachCutoffPrimePairs N ℓ k a n (N:ℝ) ((N:ℝ)^2)=
      goldbachProgressionPairs ℓ k a n := by
  classical
  ext ⟨m,t⟩
  rw [mem_goldbachCutoffPrimePairs (Nat.cast_nonneg N) (sq_nonneg (N:ℝ))]
  simp only [goldbachProgressionPairs,mem_filter,mem_product,mem_range,
    Nat.lt_succ_iff]
  have hm2 : m≤m^2 := Nat.le_self_pow (by decide) m
  constructor
  · rintro ⟨hm,_,ht,_,_,hres,he⟩
    exact ⟨⟨by omega,by nlinarith⟩,hm,ht,hres,he⟩
  · rintro ⟨⟨_,_⟩,hm,ht,hres,he⟩
    have hmN : m≤N := by nlinarith
    have htN : t≤N^2 := by nlinarith
    refine ⟨hm,by exact_mod_cast hmN,ht,?_,by omega,hres,he⟩
    exact_mod_cast htN

theorem goldbach_full_fourier_inversion {N ℓ k a n : ℕ} (hℓ : 1≤ℓ)
    (hn : n<N^2) :
    (∫ θ : PrimeCircle,goldbachPrimeSquarePolynomial (N:ℝ) θ*
      goldbachProgressionPolynomial N ℓ k a ((N:ℝ)^2) θ*
        fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle)=
      ((goldbachProgressionPairs ℓ k a n).card:ℂ) := by
  rw [goldbach_cutoff_fourier_inversion,goldbach_full_cutoffs_redundant hℓ hn]

end PrimeSquares
