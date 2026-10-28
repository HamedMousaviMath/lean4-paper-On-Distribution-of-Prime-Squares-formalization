import PrimeSquares.GoldbachWeightedNormalization

set_option autoImplicit false
open Finset Filter
namespace PrimeSquares

noncomputable def goldbachWeightedOneInverse (R x : ℝ) : ℝ :=
  ∏ p∈(goldbachPrimeCutoff x).filter (fun p : ℕ=>R<(p:ℝ) ∧ p%4=1),
    (1-1/((p:ℝ)-1))⁻¹

/- Classical ordinary/progression Mertens ratios only; no varying weight
   or main term occurs in these independent input fields. -/
structure ClassicalPrimeMertensRatios (K : ℝ) : Prop where
  full : ∀ R z : ℝ,3≤R→R<z→goldbachWeightedOuterProduct R z 0≤
    (1+K/Real.log R)*Real.log R/Real.log z
  half : ∀ R z : ℝ,3≤R→R<z→
    (1-K/Real.log R)*(Real.sqrt (Real.log R)/Real.sqrt (Real.log z))≤
      goldbachWeightedOuterProduct R z 3
  one : ∀ R x : ℝ,3≤R→R≤x→goldbachWeightedOneInverse R x≤
    (1+K/Real.log R)*Real.sqrt (Real.log x)/Real.sqrt (Real.log R)

theorem goldbach_weighted_correction_product (R : ℝ) (hR : 3≤R) (n : ℤ) :
    (∏ p∈goldbachPrimeCutoff R,(1+goldbachWeightedPrimeValue R n p/((p:ℝ)-1)))=
      goldbachWeightedC R n/goldbachWeightedB R n := by
  classical
  have hsubset : goldbachLargeLocalPrimes R⊆goldbachPrimeCutoff R := by
    intro p hp
    obtain ⟨hprime,_,hpR⟩ := (mem_goldbach_large_local_primes (by linarith) p).mp hp
    exact (mem_goldbachPrimeCutoff (by linarith) p).mpr ⟨hprime,hpR⟩
  have he : (∏ p∈goldbachLargeLocalPrimes R,(1+goldbachWeightedPrimeValue R n p/((p:ℝ)-1)))=
      ∏ p∈goldbachPrimeCutoff R,(1+goldbachWeightedPrimeValue R n p/((p:ℝ)-1)) := by
    apply prod_subset hsubset
    intro p hp hnot
    obtain ⟨hprime,hpR⟩ := (mem_goldbachPrimeCutoff (by linarith) p).mp hp
    have hp3 : p≤3 := by
      by_contra! hh
      exact hnot ((mem_goldbach_large_local_primes (by linarith) p).mpr ⟨hprime,hh,hpR⟩)
    have h4 : p%4≠1 := by have := hprime.two_le;omega
    simp only [goldbachWeightedPrimeValue,ite_eq_right h4,zero_div,add_zero]
  rw [goldbachWeightedC,mul_div_cancel_left₀ _ (goldbach_weighted_B_positive R (by linarith) n).ne']
  exact he.symm

theorem goldbach_weighted_euler_split (R x : ℝ) (hR : 3≤R) (hRx : R≤x) (n : ℤ) :
    (∏ p∈goldbachPrimeCutoff x,(1+goldbachWeightedPrimeValue R n p/((p:ℝ)-1)))=
      goldbachWeightedC R n/goldbachWeightedB R n*goldbachWeightedOneInverse R x := by
  classical
  have hsmall : (goldbachPrimeCutoff x).filter (fun p : ℕ=>(p:ℝ)≤R)=goldbachPrimeCutoff R := by
    ext p
    simp only [mem_filter,mem_goldbachPrimeCutoff (by linarith : (0:ℝ)≤x),
      mem_goldbachPrimeCutoff (by linarith : (0:ℝ)≤R)]
    constructor
    · rintro ⟨⟨hp,_⟩,hpR⟩;exact ⟨hp,hpR⟩
    · rintro ⟨hp,hpR⟩;exact ⟨⟨hp,hpR.trans hRx⟩,hpR⟩
  rw [←prod_filter_mul_prod_filter_not (goldbachPrimeCutoff x) (fun p : ℕ=>(p:ℝ)≤R),
    hsmall,goldbach_weighted_correction_product R hR n]
  congr 1
  have hq : (goldbachPrimeCutoff x).filter (fun p : ℕ=>R<(p:ℝ) ∧ p%4=1)=
      ((goldbachPrimeCutoff x).filter (fun p : ℕ=>R<(p:ℝ))).filter (fun p : ℕ=>p%4=1) := by
    ext p;simp only [mem_filter,and_assoc]
  rw [goldbachWeightedOneInverse,hq]
  have hfilter : (goldbachPrimeCutoff x).filter (fun p : ℕ=>¬(p:ℝ)≤R)=
      (goldbachPrimeCutoff x).filter (fun p : ℕ=>R<(p:ℝ)) := by
    ext p;simp only [mem_filter,not_le]
  rw [hfilter]
  conv_rhs => rw [prod_filter]
  apply prod_congr rfl
  intro p hp
  obtain ⟨hp,hRp⟩ := mem_filter.mp hp
  have hprime := ((mem_goldbachPrimeCutoff (by linarith) p).mp hp).1
  rw [goldbach_weighted_prime_above R n p hRp]
  by_cases h4 : p%4=1
  · rw [goldbachBaselinePrimeValue,ite_eq_left h4,ite_eq_left h4]
    have hpR : (3:ℝ)<p := hR.trans_lt hRp
    field_simp [show (p:ℝ)-1≠0 by linarith,show (p:ℝ)-2≠0 by linarith,
      show (p:ℝ)-1-1≠0 by linarith]
    ring
  · simp only [goldbachBaselinePrimeValue,ite_eq_right h4,zero_div,add_zero]

theorem goldbach_weighted_mean_normalized (hT : ClassicalHalfMeanValueInput)
    (K₀ K₁ : ℝ) (hK₀ : 0≤K₀) (_hK₁ : 0≤K₁)
    (hM : ClassicalPrimeLogMertens K₀) (hV : ClassicalPrimeMertensRatios K₁) :
    ∃ K δ : ℝ,0<K ∧ 0<δ ∧ ∀ R : ℝ,3≤R→∀ n : ℤ,∀ x ε : ℝ,
      Real.exp 16<x→1/Real.sqrt (Real.log x)<ε→ε≤1/2→R≤x^ε→
      6*Real.log R+10*K₀≤ε^2*Real.log x→
      (∑ u∈range (⌊x⌋₊+1),goldbachWeightedMultiplicative R n u)≤
        (goldbachHalfMeanConstant+K*ε^δ)*(1+K₁/Real.log R)*
          (goldbachWeightedC R n/goldbachWeightedB R n)*x/
            (Real.sqrt (Real.log R)*Real.sqrt (Real.log x)) := by
  obtain ⟨K,δ,hK,hδ,hbound⟩ := goldbach_weighted_mean_from_tenenbaum hT K₀ hK₀ hM
  refine ⟨K,δ,hK,hδ,?_⟩
  intro R hR n x ε hx hε hεB hRxε hbudget
  have hx1 : 1<x := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<16)).trans hx
  have hlogx : 0<Real.log x := Real.log_pos hx1
  have hlogR : 0<Real.log R := Real.log_pos (by linarith)
  have hε0 : 0<ε := (one_div_pos.mpr (Real.sqrt_pos.mpr hlogx)).trans hε
  have hRx : R≤x := hRxε.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1.le (show ε≤1 by linarith))
  have hb := hbound R hR n x ε hx hε hεB hRxε hbudget
  rw [goldbach_weighted_euler_split R x hR hRx n] at hb
  have hcoef : 0≤(goldbachHalfMeanConstant+K*ε^δ)*x/Real.log x := by
    have := goldbach_half_mean_constant_positive
    positivity
  have hratio : 0≤goldbachWeightedC R n/goldbachWeightedB R n :=
    div_nonneg (goldbach_weighted_C_positive R (by linarith) n).le
      (goldbach_weighted_B_positive R (by linarith) n).le
  have hprod := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (hV.one R x hR hRx) hratio) hcoef
  apply (hb.trans hprod).trans_eq
  have hsx := (Real.sqrt_pos.mpr hlogx).ne'
  have hsR := (Real.sqrt_pos.mpr hlogR).ne'
  have hBne := (goldbach_weighted_B_positive R (by linarith) n).ne'
  field_simp [hBne]
  rw [Real.sq_sqrt hlogx.le]
  ring

end PrimeSquares
