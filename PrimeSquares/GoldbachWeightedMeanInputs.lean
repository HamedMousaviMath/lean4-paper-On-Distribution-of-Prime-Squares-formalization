import PrimeSquares.GoldbachWeightedEulerProducts
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachHalfMeanConstant : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant/2)/Real.sqrt Real.pi

noncomputable def goldbachBaselinePrimeValue (p : ℕ) : ℝ :=
  if p%4=1 then ((p:ℝ)-1)/((p:ℝ)-2) else 0

/- Independent classical inputs. Neither statement mentions a Goldbach
   sequence, its local root counts, its multiplier set, or its main terms.
   The mean-value input is the nonnegative strongly multiplicative,
   half-dimensional upper corollary of Tenenbaum, Theorem1.2, (1.18).
   Its constants are uniform in the function. See the source review. -/
structure ClassicalHalfMeanValueInput : Prop where
  bound : ∃ K δ : ℝ,0<K ∧ 0<δ ∧ ∀ (r : ℕ→ℝ),
    r 0=0→ r 1=1→(∀ a b : ℕ,a.Coprime b→ r (a*b)=r a*r b)→
    (∀ a : ℕ,0≤r a)→(∀ p : ℕ,p.Prime→ r p≤6)→
    (∀ p j : ℕ,p.Prime→ r (p^(j+1))=r p)→
    ∀ x ε : ℝ,Real.exp 16<x→1/Real.sqrt (Real.log x)<ε→ε≤1/2→
    (∀ y : ℝ,x^ε<y→y≤x→
      |∑ p∈goldbachPrimeCutoff y,(r p-1/2)*Real.log p/(p:ℝ)|≤ε*Real.log y)→
    (∑ u∈range (⌊x⌋₊+1),r u)≤
      (goldbachHalfMeanConstant+K*ε^δ)*x/Real.log x*
        ∏ p∈goldbachPrimeCutoff x,(1+r p/((p:ℝ)-1))

structure ClassicalPrimeLogMertens (K : ℝ) : Prop where
  all : ∀ x : ℝ,2≤x→
    |(∑ p∈goldbachPrimeCutoff x,Real.log p/(p:ℝ))-Real.log x|≤K
  one : ∀ x : ℝ,2≤x→
    |(∑ p∈(goldbachPrimeCutoff x).filter (fun p : ℕ=>p%4=1),
      Real.log p/(p:ℝ))-Real.log x/2|≤K
  convergent : ∀ x : ℝ,2≤x→
    (∑ p∈goldbachPrimeCutoff x,Real.log p/(p:ℝ)^2)≤K

theorem goldbach_half_mean_constant_positive : 0<goldbachHalfMeanConstant := by
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr Real.pi_pos)

theorem goldbach_weighted_prime_power (R : ℝ) (n : ℤ) (p j : ℕ) (hp : p.Prime) :
    goldbachWeightedMultiplicative R n (p^(j+1))=goldbachWeightedPrimeValue R n p := by
  classical
  simp only [goldbachWeightedMultiplicative,pow_ne_zero _ hp.ne_zero,ite_false,
    Nat.primeFactors_prime_pow (by omega : j+1≠0) hp,prod_singleton]

theorem goldbach_weighted_at_prime (R : ℝ) (n : ℤ) (p : ℕ) (hp : p.Prime) :
    goldbachWeightedMultiplicative R n p=goldbachWeightedPrimeValue R n p := by
  simpa only [zero_add,pow_one] using goldbach_weighted_prime_power R n p 0 hp

theorem goldbach_weighted_prime_above (R : ℝ) (n : ℤ) (p : ℕ) (hpR : R<(p:ℝ)) :
    goldbachWeightedPrimeValue R n p=goldbachBaselinePrimeValue p := by
  simp only [goldbachWeightedPrimeValue,goldbachBaselinePrimeValue,
    ite_eq_right (not_le_of_gt hpR)]

theorem goldbach_baseline_prime_range (p : ℕ) (hp : p.Prime) :
    0≤goldbachBaselinePrimeValue p ∧ goldbachBaselinePrimeValue p≤2 := by
  unfold goldbachBaselinePrimeValue
  by_cases h4 : p%4=1
  · rw [ite_eq_left h4]
    have hpR : (5:ℝ)≤p := by exact_mod_cast (show 5≤p by have := hp.two_le;omega)
    exact ⟨div_nonneg (by linarith) (by linarith),
      (div_le_iff₀ (by linarith : 0<(p:ℝ)-2)).mpr (by linarith)⟩
  · rw [ite_eq_right h4]
    norm_num

theorem goldbach_weighted_prime_difference (R : ℝ) (n : ℤ) (p : ℕ) (hp : p.Prime) :
    |goldbachWeightedPrimeValue R n p-goldbachBaselinePrimeValue p|≤6 := by
  obtain ⟨hb,hb'⟩ := goldbach_baseline_prime_range p hp
  have hr := goldbach_weighted_prime_nonneg R n hp
  have hr' := goldbach_weighted_prime_le_six R n hp
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem goldbach_baseline_prime_log_balance (K : ℝ) (hK : 0≤K)
    (hM : ClassicalPrimeLogMertens K) (x : ℝ) (hx : 2≤x) :
    |∑ p∈goldbachPrimeCutoff x,(goldbachBaselinePrimeValue p-1/2)*Real.log p/(p:ℝ)|≤4*K := by
  classical
  let P := goldbachPrimeCutoff x
  let E := ∑ p∈P,if p%4=1 then Real.log p/((p:ℝ)*((p:ℝ)-2)) else 0
  have hE0 : 0≤E := by
    apply sum_nonneg
    intro p hp
    by_cases h4 : p%4=1
    · rw [ite_eq_left h4]
      have hprime := ((mem_goldbachPrimeCutoff (by linarith) p).mp hp).1
      have hpR : (5:ℝ)≤p := by exact_mod_cast (show 5≤p by have := hprime.two_le;omega)
      exact div_nonneg (Real.log_nonneg (by linarith)) (mul_nonneg (by linarith) (by linarith))
    · rw [ite_eq_right h4]
  have hE : E≤2*K := by
    apply le_trans _ (mul_le_mul_of_nonneg_left (hM.convergent x hx) (by norm_num : (0:ℝ)≤2))
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hprime := ((mem_goldbachPrimeCutoff (by linarith) p).mp hp).1
    have hp2 : (2:ℝ)≤p := by exact_mod_cast hprime.two_le
    have hl : 0≤Real.log p := Real.log_nonneg (by linarith)
    by_cases h4 : p%4=1
    · rw [ite_eq_left h4]
      have hp5 : (5:ℝ)≤p := by exact_mod_cast (show 5≤p by have := hprime.two_le;omega)
      rw [←mul_div_assoc]
      apply (div_le_div_iff₀ (mul_pos (by linarith : (0:ℝ)<p) (by linarith : 0<(p:ℝ)-2))
        (sq_pos_of_pos (by linarith : (0:ℝ)<p))).mpr
      have hd : (p:ℝ)^2≤2*((p:ℝ)*((p:ℝ)-2)) := by nlinarith
      nlinarith only [mul_le_mul_of_nonneg_left hd hl]
    · rw [ite_eq_right h4]
      positivity
  have hid : (∑ p∈P,(goldbachBaselinePrimeValue p-1/2)*Real.log p/(p:ℝ))=
      (∑ p∈P.filter (fun p : ℕ=>p%4=1),Real.log p/(p:ℝ))-
        (∑ p∈P,Real.log p/(p:ℝ))/2+E := by
    rw [sum_filter,sum_div,←sum_sub_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    by_cases h4 : p%4=1
    · have hprime := ((mem_goldbachPrimeCutoff (by linarith) p).mp hp).1
      have hp5 : (5:ℝ)≤p := by exact_mod_cast (show 5≤p by have := hprime.two_le;omega)
      simp only [goldbachBaselinePrimeValue,ite_eq_left h4]
      field_simp [show (p:ℝ)≠0 by linarith,show (p:ℝ)-2≠0 by linarith]
      ring
    · simp only [goldbachBaselinePrimeValue,ite_eq_right h4,zero_sub]
      ring
  rw [hid]
  have h₁ := abs_le.mp (hM.one x hx)
  have h₂ := abs_le.mp (hM.all x hx)
  apply abs_le.mpr
  constructor <;> dsimp only [P] at * <;> linarith

theorem goldbach_weighted_prime_log_balance (K R y : ℝ) (hK : 0≤K)
    (hM : ClassicalPrimeLogMertens K) (hR : 3≤R) (hRy : R≤y) (n : ℤ) :
    |∑ p∈goldbachPrimeCutoff y,
      (goldbachWeightedPrimeValue R n p-1/2)*Real.log p/(p:ℝ)|≤6*Real.log R+10*K := by
  classical
  have hR0 : 0≤R := by linarith
  have hy0 : 0≤y := by linarith
  have hsubset : goldbachPrimeCutoff R⊆goldbachPrimeCutoff y := by
    intro p hp
    obtain ⟨hprime,hpR⟩ := (mem_goldbachPrimeCutoff hR0 p).mp hp
    exact (mem_goldbachPrimeCutoff hy0 p).mpr ⟨hprime,hpR.trans hRy⟩
  let f := fun p : ℕ=>(goldbachWeightedPrimeValue R n p-goldbachBaselinePrimeValue p)*Real.log p/(p:ℝ)
  have hdiff : (∑ p∈goldbachPrimeCutoff y,f p)=∑ p∈goldbachPrimeCutoff R,f p := by
    symm
    apply sum_subset hsubset
    intro p hp hnot
    have hpdata := (mem_goldbachPrimeCutoff hy0 p).mp hp
    have hpR : R<(p:ℝ) := by
      by_contra! h
      exact hnot ((mem_goldbachPrimeCutoff hR0 p).mpr ⟨hpdata.1,h⟩)
    simp only [f,goldbach_weighted_prime_above R n p hpR,sub_self,zero_mul,zero_div]
  have hd : |∑ p∈goldbachPrimeCutoff y,f p|≤6*(Real.log R+K) := by
    rw [hdiff]
    apply (abs_sum_le_sum_abs _ _).trans
    have hsum : (∑ p∈goldbachPrimeCutoff R,Real.log p/(p:ℝ))≤Real.log R+K := by
      have hh := (abs_le.mp (hM.all R (by linarith))).2
      linarith
    apply le_trans _ (mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ)≤6))
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hprime := ((mem_goldbachPrimeCutoff hR0 p).mp hp).1
    have hp0 : (0:ℝ)<p := by exact_mod_cast hprime.pos
    have hp1 : (1:ℝ)≤p := by exact_mod_cast hprime.one_le
    have hl := Real.log_nonneg hp1
    dsimp only [f]
    rw [abs_div,abs_mul,abs_of_nonneg hl,abs_of_pos hp0]
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (goldbach_weighted_prime_difference R n p hprime) hl) hp0.le
  have hb := goldbach_baseline_prime_log_balance K hK hM y (by linarith)
  have he : (∑ p∈goldbachPrimeCutoff y,(goldbachWeightedPrimeValue R n p-1/2)*Real.log p/(p:ℝ))=
      (∑ p∈goldbachPrimeCutoff y,f p)+
        ∑ p∈goldbachPrimeCutoff y,(goldbachBaselinePrimeValue p-1/2)*Real.log p/(p:ℝ) := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro p _
    dsimp only [f]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

theorem goldbach_weighted_mean_from_tenenbaum (hT : ClassicalHalfMeanValueInput)
    (K₀ : ℝ) (hK₀ : 0≤K₀) (hM : ClassicalPrimeLogMertens K₀) :
    ∃ K δ : ℝ,0<K ∧ 0<δ ∧ ∀ R : ℝ,3≤R→∀ n : ℤ,∀ x ε : ℝ,
      Real.exp 16<x→1/Real.sqrt (Real.log x)<ε→ε≤1/2→R≤x^ε→
      6*Real.log R+10*K₀≤ε^2*Real.log x→
      (∑ u∈range (⌊x⌋₊+1),goldbachWeightedMultiplicative R n u)≤
        (goldbachHalfMeanConstant+K*ε^δ)*x/Real.log x*
          ∏ p∈goldbachPrimeCutoff x,(1+goldbachWeightedPrimeValue R n p/((p:ℝ)-1)) := by
  obtain ⟨K,δ,hK,hδ,hbound⟩ := hT.bound
  refine ⟨K,δ,hK,hδ,?_⟩
  intro R hR n x ε hx hε hεB hRx hbudget
  have hx1 : 1<x := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<16)).trans hx
  have hlog : 0<Real.log x := Real.log_pos hx1
  have hε0 : 0<ε := (one_div_pos.mpr (Real.sqrt_pos.mpr hlog)).trans hε
  have happly := hbound (goldbachWeightedMultiplicative R n)
    (by simp only [goldbachWeightedMultiplicative,ite_true])
    (goldbach_weighted_multiplicative_one R n)
    (goldbach_weighted_multiplicative_mul R n)
    (goldbach_weighted_multiplicative_nonneg R n)
    (fun p hp=>by rw [goldbach_weighted_at_prime R n p hp];exact goldbach_weighted_prime_le_six R n hp)
    (fun p j hp=>by rw [goldbach_weighted_prime_power R n p j hp,goldbach_weighted_at_prime R n p hp])
    x ε hx hε hεB
  have he : (∏ p∈goldbachPrimeCutoff x,(1+goldbachWeightedMultiplicative R n p/((p:ℝ)-1)))=
      ∏ p∈goldbachPrimeCutoff x,(1+goldbachWeightedPrimeValue R n p/((p:ℝ)-1)) := by
    apply prod_congr rfl
    intro p hp
    rw [goldbach_weighted_at_prime R n p ((mem_goldbachPrimeCutoff (by linarith) p).mp hp).1]
  rw [←he]
  apply happly
  intro y hy hyx
  have hRy : R≤y := hRx.trans hy.le
  have hyl : ε*Real.log x<Real.log y := by
    have hh := Real.log_lt_log (Real.rpow_pos_of_pos (by linarith : 0<x) ε) hy
    rwa [Real.log_rpow (by linarith : 0<x)] at hh
  have hb := goldbach_weighted_prime_log_balance K₀ R y hK₀ hM hR hRy n
  have he' : (∑ p∈goldbachPrimeCutoff y,
      (goldbachWeightedMultiplicative R n p-1/2)*Real.log p/(p:ℝ))=
      ∑ p∈goldbachPrimeCutoff y,(goldbachWeightedPrimeValue R n p-1/2)*Real.log p/(p:ℝ) := by
    apply sum_congr rfl
    intro p hp
    rw [goldbach_weighted_at_prime R n p ((mem_goldbachPrimeCutoff (by linarith) p).mp hp).1]
  rw [he']
  exact hb.trans (by nlinarith only [hbudget,mul_le_mul_of_nonneg_left hyl.le hε0.le])

end PrimeSquares
