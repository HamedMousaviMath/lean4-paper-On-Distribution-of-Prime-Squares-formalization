import PrimeSquares.GoldbachMinorArcBessel

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

noncomputable def goldbachFrequencyPolynomial {ι : Type*} (S : Finset ι)
    (f : ι→ℤ) (c : ι→ℂ) : C(PrimeCircle,ℂ) :=
  ∑ i∈S,c i • fourier (f i)

/-- Orthogonality opens the actual integral even when frequencies repeat. -/
theorem goldbach_frequency_energy_identity {ι : Type*} (S : Finset ι)
    (f : ι→ℤ) (c : ι→ℂ) :
    (∫ θ : PrimeCircle,‖goldbachFrequencyPolynomial S f c θ‖^2
      ∂AddCircle.haarAddCircle)=
      (∑ i∈S,∑ j∈S,if f i=f j then c i*(starRingEnd ℂ) (c j) else 0).re := by
  classical
  let P := goldbachFrequencyPolynomial S f c
  have hexp (θ : PrimeCircle) : P θ*(starRingEnd ℂ) (P θ)=
      ∑ i∈S,∑ j∈S,(c i*(starRingEnd ℂ) (c j))*fourier (f i-f j) θ := by
    simp only [P,goldbachFrequencyPolynomial,ContinuousMap.sum_apply,
      ContinuousMap.smul_apply,smul_eq_mul,map_sum,map_mul,sum_mul,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [sub_eq_add_neg,fourier_add,fourier_neg]
    ring
  have hi (i j : ι) : Integrable (fun θ : PrimeCircle =>
      (c i*(starRingEnd ℂ) (c j))*fourier (f i-f j) θ)
        AddCircle.haarAddCircle :=
    (continuous_const.mul (fourier _).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint : (∫ θ : PrimeCircle,P θ*(starRingEnd ℂ) (P θ)
      ∂AddCircle.haarAddCircle)=
      ∑ i∈S,∑ j∈S,if f i=f j then c i*(starRingEnd ℂ) (c j) else 0 := by
    simp_rw [hexp]
    rw [integral_finsetSum S (fun i _ => integrable_finsetSum S (fun j _ => hi i j))]
    simp_rw [integral_finsetSum S (fun j _ => hi _ j),integral_const_mul,
      goldbach_finite_character_integral,sub_eq_zero,mul_ite,mul_one,mul_zero]
  have hiP : Integrable (fun θ : PrimeCircle => P θ*(starRingEnd ℂ) (P θ))
      AddCircle.haarAddCircle :=
    (P.continuous.mul (Complex.continuous_conj.comp P.continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _=(∫ θ : PrimeCircle,(P θ*(starRingEnd ℂ) (P θ)).re
      ∂AddCircle.haarAddCircle) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun θ => by
          change ‖P θ‖^2=(P θ*(starRingEnd ℂ) (P θ)).re
          exact (Complex.sq_norm _).trans (congrArg Complex.re (Complex.mul_conj _)).symm)
    _=(∫ θ : PrimeCircle,P θ*(starRingEnd ℂ) (P θ)
      ∂AddCircle.haarAddCircle).re := integral_re hiP
    _=_ := congrArg Complex.re hint

theorem goldbach_frequency_energy_le_collisions {ι : Type*} (S : Finset ι)
    (f : ι→ℤ) (c : ι→ℂ) (hc : ∀ i∈S,‖c i‖≤1) :
    (∫ θ : PrimeCircle,‖goldbachFrequencyPolynomial S f c θ‖^2
      ∂AddCircle.haarAddCircle)≤
      (((S×ˢS).filter (fun x => f x.1=f x.2)).card:ℝ) := by
  classical
  rw [goldbach_frequency_energy_identity]
  have hsum : (∑ i∈S,∑ j∈S,if f i=f j then c i*(starRingEnd ℂ) (c j) else 0).re≤
      ∑ i∈S,∑ j∈S,if f i=f j then (1:ℝ) else 0 := by
    change ((Complex.reCLM : ℂ→L[ℝ] ℝ) (∑ i∈S,∑ j∈S,
      if f i=f j then c i*(starRingEnd ℂ) (c j) else 0))≤_
    simp only [map_sum]
    apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    split_ifs with he
    · exact (Complex.re_le_norm _).trans (by
        rw [norm_mul,Complex.norm_conj]
        calc
          _≤(1:ℝ)*1 := mul_le_mul (hc i hi) (hc j hj) (norm_nonneg _) (by norm_num)
          _=1 := one_mul _)
    · simp
  refine hsum.trans_eq ?_
  simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,sum_product]

/-- A progression event retains its two arithmetic indices and its actual prime. -/
noncomputable def goldbachProgressionEvents (N : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (W : ℝ) : Finset ((ℕ×ℕ)×ℕ) :=
  (I×ˢgoldbachPrimeCutoff W).filter
    (fun x => x.1.1*x.2<N^2 ∧ x.2%x.1.2=a x.1%x.1.2)

theorem mem_goldbachProgressionEvents (N : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (W : ℝ) (i : ℕ×ℕ) (t : ℕ) :
    (i,t)∈goldbachProgressionEvents N I a W ↔
      i∈I ∧ t∈goldbachProgressionCutoff N i.1 i.2 (a i) W := by
  simp only [goldbachProgressionEvents,goldbachProgressionCutoff,mem_filter,mem_product]
  tauto

theorem goldbach_weighted_progression_as_frequency_polynomial (N : ℕ)
    (I : Finset (ℕ×ℕ)) (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (W : ℝ) :
    goldbachWeightedProgressionPolynomial N I a d W=
      goldbachFrequencyPolynomial (goldbachProgressionEvents N I a W)
        (fun x => ((x.1.1*x.2:ℕ):ℤ)) (fun x => d x.1) := by
  classical
  ext θ
  simp only [goldbachWeightedProgressionPolynomial,goldbachProgressionPolynomial,
    goldbachProgressionCutoff,goldbachFrequencyPolynomial,goldbachProgressionEvents,
    ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,sum_filter,
    sum_product,mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro t _
  by_cases h : i.1*t<N^2 ∧ t%i.2=a i%i.2
  · simp only [ite_eq_left h,ContinuousMap.smul_apply,smul_eq_mul]
  · simp only [ite_eq_right h,ContinuousMap.zero_apply,mul_zero]

/-- No divisor or logarithmic estimate is hidden in this exact energy reduction. -/
theorem goldbach_progression_energy_le_collisions (N : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (W : ℝ) (hd : ∀ i∈I,‖d i‖≤1) :
    (∫ θ : PrimeCircle,‖goldbachWeightedProgressionPolynomial N I a d W θ‖^2
      ∂AddCircle.haarAddCircle)≤
      ((((goldbachProgressionEvents N I a W)×ˢ(goldbachProgressionEvents N I a W)).filter
        (fun x => x.1.1.1*x.1.2=x.2.1.1*x.2.2)).card:ℝ) := by
  rw [goldbach_weighted_progression_as_frequency_polynomial]
  have he := goldbach_frequency_energy_le_collisions (goldbachProgressionEvents N I a W)
    (fun x => ((x.1.1*x.2:ℕ):ℤ)) (fun x => d x.1) (fun x hx =>
      hd x.1 ((mem_goldbachProgressionEvents N I a W x.1 x.2).mp hx).1)
  simpa only [Nat.cast_inj] using he

/-- Literal n<N^2 output range, with the actual progression energy eliminated.
The exponential-sum bound and the remaining finite collision estimate must
still be proved to obtain the paper's logarithmic saving. -/
theorem goldbach_actual_minor_collision_bound (N : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (U W : ℝ) (hd : ∀ i∈I,‖d i‖≤1)
    (minor : Set PrimeCircle) (hminor : MeasurableSet minor) {B : ℝ}
    (hP : ∀ θ∈minor,‖goldbachPrimeSquarePolynomial U θ‖≤B) :
    (∑ n∈range (N^2),‖∫ θ : PrimeCircle in minor,goldbachPrimeSquarePolynomial U θ*
      goldbachWeightedProgressionPolynomial N I a d W θ*fourier (-(n:ℤ)) θ
        ∂AddCircle.haarAddCircle‖^2)≤
      B^2*((((goldbachProgressionEvents N I a W)×ˢ(goldbachProgressionEvents N I a W)).filter
        (fun x => x.1.1.1*x.1.2=x.2.1.1*x.2.2)).card:ℝ) := by
  let e : ℕ↪ℤ := ⟨fun n => (n:ℤ),Nat.cast_injective⟩
  have he := goldbach_actual_minor_bessel N I a d U W ((range (N^2)).map e)
    minor hminor hP (goldbach_progression_energy_le_collisions N I a d W hd)
  simpa only [sum_map,e,Function.Embedding.coeFn_mk] using he

theorem goldbach_prime_collision_diagonal {ℓ₁ ℓ₂ t : ℕ} (ht : t.Prime)
    (he : ℓ₁*t=ℓ₂*t) : ℓ₁=ℓ₂ :=
  Nat.eq_of_mul_eq_mul_right ht.pos he

/-- Distinct prime frequencies force exactly the common-factor geometry used
in the source off-diagonal dyadic argument. -/
theorem goldbach_prime_collision_off_diagonal {ℓ₁ ℓ₂ t₁ t₂ : ℕ}
    (hℓ₁ : 0<ℓ₁) (ht₁ : t₁.Prime) (ht₂ : t₂.Prime) (hne : t₁≠t₂)
    (he : ℓ₁*t₁=ℓ₂*t₂) :
    ∃! s : ℕ,0<s ∧ ℓ₁=s*t₂ ∧ ℓ₂=s*t₁ := by
  have hnd : ¬t₂∣t₁ := by
    intro hd
    exact hne ((Nat.prime_dvd_prime_iff_eq ht₂ ht₁).mp hd).symm
  have hd : t₂∣ℓ₁ := (ht₂.dvd_mul.mp (by rw [he]; exact dvd_mul_left _ _)).resolve_right hnd
  obtain ⟨s,hs⟩ := hd
  have h₁ : ℓ₁=s*t₂ := by nlinarith only [hs]
  have h₂ : ℓ₂=s*t₁ := Nat.eq_of_mul_eq_mul_right ht₂.pos (by
    rw [h₁] at he
    nlinarith only [he])
  have hspos : 0<s := by nlinarith only [hℓ₁,h₁]
  refine ⟨s,⟨hspos,h₁,h₂⟩,?_⟩
  intro u hu
  exact Nat.eq_of_mul_eq_mul_right ht₂.pos (hu.2.1.symm.trans h₁)

end PrimeSquares
