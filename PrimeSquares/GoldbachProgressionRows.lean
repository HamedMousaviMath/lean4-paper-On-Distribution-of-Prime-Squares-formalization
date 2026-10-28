import PrimeSquares.GoldbachPrimeFrequencyEnergy

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

noncomputable def goldbachModuliAt (I : Finset (ℕ×ℕ)) (ℓ : ℕ) : Finset ℕ :=
  (I.filter (fun i => i.1=ℓ)).image Prod.snd

theorem mem_goldbachModuliAt (I : Finset (ℕ×ℕ)) (ℓ k : ℕ) :
    k∈goldbachModuliAt I ℓ ↔ (ℓ,k)∈I := by
  classical
  constructor
  · intro hk
    obtain ⟨i,hi,he⟩ := mem_image.mp hk
    obtain ⟨hiI,hiℓ⟩ := mem_filter.mp hi
    have hiEq : i=(ℓ,k) := Prod.ext hiℓ he
    simpa only [hiEq] using hiI
  · intro hi
    exact mem_image.mpr ⟨(ℓ,k),mem_filter.mpr ⟨hi,rfl⟩,rfl⟩

theorem goldbach_index_row_sum {E : Type*} [AddCommMonoid E]
    (I : Finset (ℕ×ℕ)) (f : ℕ×ℕ→E) :
    (∑ i∈I,f i)=∑ ℓ∈I.image Prod.fst,∑ k∈goldbachModuliAt I ℓ,f (ℓ,k) := by
  classical
  have hiℓ (ℓ : ℕ) : (∑ k∈goldbachModuliAt I ℓ,f (ℓ,k))=
      ∑ i∈I.filter (fun i => i.1=ℓ),f i := by
    rw [goldbachModuliAt,sum_image]
    · apply sum_congr rfl
      intro i hi
      rw [←(mem_filter.mp hi).2]
    · intro i hi j hj he
      exact Prod.ext ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm) he
  simp_rw [hiℓ]
  exact (sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem Prod.fst hi) f).symm

noncomputable def goldbachProgressionRowCoefficient (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (ℓ t : ℕ) : ℂ :=
  ∑ k∈(goldbachModuliAt I ℓ).filter (fun k => t%k=a (ℓ,k)%k),d (ℓ,k)

theorem goldbach_progression_row_coefficient_norm (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (hd : ∀ i∈I,‖d i‖≤1) (ℓ t : ℕ) :
    ‖goldbachProgressionRowCoefficient I a d ℓ t‖≤
      (goldbachCongruenceMultiplicity (goldbachModuliAt I ℓ) (fun k => a (ℓ,k)) t:ℝ) := by
  calc
    _≤∑ k∈(goldbachModuliAt I ℓ).filter (fun k => t%k=a (ℓ,k)%k),‖d (ℓ,k)‖ := norm_sum_le _ _
    _≤∑ _k∈(goldbachModuliAt I ℓ).filter (fun k => t%k=a (ℓ,k)%k),(1:ℝ) := by
      apply sum_le_sum
      intro k hk
      exact hd (ℓ,k) ((mem_goldbachModuliAt I ℓ k).mp (mem_filter.mp hk).1)
    _=_ := by simp only [goldbachCongruenceMultiplicity,sum_const,nsmul_eq_mul,mul_one]

noncomputable def goldbachPrimeProductRows (N : ℕ) (I : Finset (ℕ×ℕ)) (W : ℝ) :
    Finset (ℕ×ℕ) :=
  ((I.image Prod.fst)×ˢgoldbachPrimeCutoff W).filter (fun x => x.1*x.2<N^2)

theorem goldbach_progression_polynomial_by_rows (N : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (W : ℝ) :
    goldbachWeightedProgressionPolynomial N I a d W=
      goldbachFrequencyPolynomial (goldbachPrimeProductRows N I W)
        (fun x => ((x.1*x.2:ℕ):ℤ))
        (fun x => goldbachProgressionRowCoefficient I a d x.1 x.2) := by
  classical
  unfold goldbachWeightedProgressionPolynomial
  rw [goldbach_index_row_sum I]
  ext θ
  simp only [goldbachProgressionPolynomial,goldbachProgressionCutoff,
    goldbachFrequencyPolynomial,goldbachPrimeProductRows,
    ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,sum_filter,sum_product,mul_sum]
  apply sum_congr rfl
  intro ℓ _
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  by_cases hp : ℓ*t<N^2
  · simp only [hp,true_and,ite_true,goldbachProgressionRowCoefficient,sum_filter,
      ContinuousMap.smul_apply,smul_eq_mul,sum_mul]
    apply sum_congr rfl
    intro k _
    by_cases hr : t%k=a (ℓ,k)%k
    · simp only [hr,ite_true]
    · simp only [hr,ite_false,ContinuousMap.zero_apply,mul_zero,zero_mul]
  · simp only [hp,false_and,ite_false,ContinuousMap.zero_apply,mul_zero,sum_const_zero]

theorem goldbach_progression_energy_by_row_squares (N : ℕ) (hN : 1≤N)
    (I : Finset (ℕ×ℕ)) (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (W : ℝ)
    (hI : ∀ i ∈ I, 0 < (i.1 : ℕ)) (hd : ∀ i∈I,‖d i‖≤1) :
    (∫ θ : PrimeCircle,‖goldbachWeightedProgressionPolynomial N I a d W θ‖^2
      ∂AddCircle.haarAddCircle)≤
      (Real.log (N^2:ℕ)/Real.log 2)*
        (∑ ℓ∈I.image Prod.fst,∑ t∈Icc 1 (N^2/ℓ),
          (goldbachCongruenceMultiplicity (goldbachModuliAt I ℓ)
            (fun k => a (ℓ,k)) t:ℝ)^2) := by
  classical
  let S := goldbachPrimeProductRows N I W
  let c : ℕ×ℕ→ℂ := fun x => goldbachProgressionRowCoefficient I a d x.1 x.2
  have hrows (x : ℕ×ℕ) (hx : x∈S) :
      x.1∈I.image Prod.fst ∧ x.2.Prime ∧ x.1*x.2<N^2 := by
    obtain ⟨hxp,hprod⟩ := mem_filter.mp hx
    obtain ⟨hxl,hxt⟩ := mem_product.mp hxp
    exact ⟨hxl,(mem_filter.mp hxt).2,hprod⟩
  have hℓpos (ℓ : ℕ) (hℓ : ℓ∈I.image Prod.fst) : 0<ℓ := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hℓ
    exact hI i hi
  have he := goldbach_prime_product_energy S c (fun x hx => (hrows x hx).2.1)
    (fun x hx => hℓpos x.1 (hrows x hx).1) (N^2) (fun x hx => (hrows x hx).2.2.le)
  have hs : (∑ x∈S,‖c x‖^2)≤
      ∑ ℓ∈I.image Prod.fst,∑ t∈Icc 1 (N^2/ℓ),
        (goldbachCongruenceMultiplicity (goldbachModuliAt I ℓ) (fun k => a (ℓ,k)) t:ℝ)^2 := by
    rw [←sum_fiberwise_of_maps_to (fun x hx => (hrows x hx).1) (fun x => ‖c x‖^2)]
    apply sum_le_sum
    intro ℓ hℓ
    apply sum_le_sum_of_injOn Prod.snd
    · intro x hx y hy hxy
      exact Prod.ext ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) hxy
    · intro t ht
      obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
      obtain ⟨hxS,hxℓ⟩ := mem_filter.mp hx
      have hp := (hrows x hxS).2.1
      have heprod : x.2*ℓ≤N^2 := by
        simpa only [←hxℓ,mul_comm] using (hrows x hxS).2.2.le
      exact mem_Icc.mpr ⟨hp.one_le,(Nat.le_div_iff_mul_le (hℓpos ℓ hℓ)).mpr heprod⟩
    · intro x hx
      have hh := pow_le_pow_left₀ (norm_nonneg (c x))
        (goldbach_progression_row_coefficient_norm I a d hd x.1 x.2) 2
      simpa only [c,(mem_filter.mp hx).2] using hh
    · intro t _ _
      positivity
  have hR : 0≤Real.log (N^2:ℕ)/Real.log 2 := div_nonneg
    (Real.log_nonneg (by exact_mod_cast (show 1≤N^2 by nlinarith)))
    (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  rw [goldbach_progression_polynomial_by_rows]
  exact he.trans (mul_le_mul_of_nonneg_left hs hR)

end PrimeSquares
