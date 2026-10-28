import PrimeSquares.GoldbachCongruenceMultiplicity
import PrimeSquares.PrimeFactorEstimates
import PrimeSquares.WeightedFiniteSquareSum

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

theorem goldbach_frequency_polynomial_regroup {ι : Type*} (S : Finset ι)
    (f : ι→ℤ) (c : ι→ℂ) :
    goldbachFrequencyPolynomial S f c=
      goldbachFrequencyPolynomial (S.image f) id
        (fun n => ∑ i∈S.filter (fun i => f i=n),c i) := by
  classical
  unfold goldbachFrequencyPolynomial
  symm
  calc
    _=∑ n∈S.image f,∑ i∈S.filter (fun i => f i=n),c i • fourier (f i) := by
      apply sum_congr rfl
      intro n _
      change (∑ i∈S.filter (fun i => f i=n),c i) • fourier n=_
      ext θ
      simp only [ContinuousMap.smul_apply,ContinuousMap.sum_apply,smul_eq_mul,sum_mul]
      apply sum_congr rfl
      intro i hi
      rw [(mem_filter.mp hi).2]
    _=_ := sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem f hi) _

theorem goldbach_distinct_frequency_energy (S : Finset ℤ) (c : ℤ→ℂ) :
    (∫ θ : PrimeCircle,‖goldbachFrequencyPolynomial S id c θ‖^2
      ∂AddCircle.haarAddCircle)=∑ n∈S,‖c n‖^2 := by
  classical
  rw [goldbach_frequency_energy_identity]
  have he : (∑ n∈S,∑ i∈S,if id n=id i then c n*(starRingEnd ℂ) (c i) else 0)=
      ∑ n∈S,c n*(starRingEnd ℂ) (c n) := by
    apply sum_congr rfl
    intro n hn
    simp only [id_eq,sum_ite_eq,ite_eq_left hn]
  rw [he,Complex.re_sum]
  apply sum_congr rfl
  intro n hn
  exact (congrArg Complex.re (Complex.mul_conj _)).trans (Complex.sq_norm _).symm

theorem goldbach_finite_sum_square {ι : Type*} (S : Finset ι) (c : ι→ℂ) :
    ‖∑ i∈S,c i‖^2≤(S.card:ℝ)*(∑ i∈S,‖c i‖^2) := by
  simpa only [sum_const,nsmul_eq_mul,mul_one,div_one] using
    norm_finset_sum_square_weighted S c (fun _ => (1:ℝ)) (fun _ _ => by norm_num)

/-- Frequency multiplicity is counted after grouping the arithmetic moduli. -/
theorem goldbach_frequency_energy_multiplicity {ι : Type*} (S : Finset ι)
    (f : ι→ℤ) (c : ι→ℂ) {B : ℝ}
    (hB : ∀ n∈S.image f,((S.filter (fun i => f i=n)).card:ℝ)≤B) :
    (∫ θ : PrimeCircle,‖goldbachFrequencyPolynomial S f c θ‖^2
      ∂AddCircle.haarAddCircle)≤B*(∑ i∈S,‖c i‖^2) := by
  rw [goldbach_frequency_polynomial_regroup,goldbach_distinct_frequency_energy]
  calc
    _≤∑ n∈S.image f,((S.filter (fun i => f i=n)).card:ℝ)*
      (∑ i∈S.filter (fun i => f i=n),‖c i‖^2) :=
        sum_le_sum (fun n _ => goldbach_finite_sum_square _ _)
    _≤∑ n∈S.image f,B*(∑ i∈S.filter (fun i => f i=n),‖c i‖^2) :=
      sum_le_sum (fun n hn => mul_le_mul_of_nonneg_right (hB n hn)
        (sum_nonneg (fun i _ => sq_nonneg _)))
    _=_ := by
      rw [←mul_sum,sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem f hi)]

theorem goldbach_prime_factor_count_log {m X : ℕ} (hm : 0<m) (hmX : m≤X) :
    (m.primeFactors.card:ℝ)≤Real.log X/Real.log 2 := by
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
  calc
    _=∑ _p∈m.primeFactors,Real.log 2 := by rw [sum_const,nsmul_eq_mul]
    _≤∑ p∈m.primeFactors,Real.log (p:ℝ) := by
      apply sum_le_sum
      intro p hp
      exact Real.log_le_log (by norm_num) (by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)
    _≤Real.log m := primeFactors_log_budget m hm
    _≤Real.log X := Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmX)

theorem goldbach_prime_product_fibre_card (S : Finset (ℕ×ℕ))
    (hprime : ∀ x∈S,x.2.Prime) {m : ℕ} (hm : 0<m) :
    (S.filter (fun x => x.1*x.2=m)).card≤m.primeFactors.card := by
  classical
  apply card_le_card_of_injOn Prod.snd
  · intro x hx
    obtain ⟨hxS,he⟩ := mem_filter.mp hx
    exact Nat.mem_primeFactors.mpr ⟨hprime x hxS,he ▸ dvd_mul_left x.2 x.1,hm.ne'⟩
  · intro x hx y hy he
    obtain ⟨hxS,hxprod⟩ := mem_filter.mp hx
    obtain ⟨_,hyprod⟩ := mem_filter.mp hy
    apply Prod.ext
    · have hmul : x.1*x.2=y.1*x.2 := by
        simpa only [←he] using hxprod.trans hyprod.symm
      exact Nat.eq_of_mul_eq_mul_right (hprime x hxS).pos hmul
    · exact he

theorem goldbach_prime_product_energy (S : Finset (ℕ×ℕ)) (c : ℕ×ℕ→ℂ)
    (hprime : ∀ x∈S,x.2.Prime) (hpos : ∀ x∈S,0<x.1)
    (X : ℕ) (hX : ∀ x∈S,x.1*x.2≤X) :
    (∫ θ : PrimeCircle,‖goldbachFrequencyPolynomial S
      (fun x => ((x.1*x.2:ℕ):ℤ)) c θ‖^2 ∂AddCircle.haarAddCircle)≤
        (Real.log X/Real.log 2)*(∑ x∈S,‖c x‖^2) := by
  classical
  apply goldbach_frequency_energy_multiplicity
  intro n hn
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
  have hm : 0<x.1*x.2 := Nat.mul_pos (hpos x hx) (hprime x hx).pos
  have hc : ((S.filter (fun y => ((y.1*y.2:ℕ):ℤ)=((x.1*x.2:ℕ):ℤ))).card:ℝ)≤
      ((x.1*x.2).primeFactors.card:ℝ) := by
    simpa only [Nat.cast_inj] using
      (show ((S.filter (fun y => y.1*y.2=x.1*x.2)).card:ℝ)≤
        ((x.1*x.2).primeFactors.card:ℝ) by
          exact_mod_cast goldbach_prime_product_fibre_card S hprime hm)
  exact hc.trans (goldbach_prime_factor_count_log hm (hX x hx))

end PrimeSquares
