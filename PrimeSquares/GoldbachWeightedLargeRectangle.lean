import PrimeSquares.GoldbachWeightedDoubleIntegral
import PrimeSquares.GoldbachWeightedDoubleAbel
import PrimeSquares.GoldbachWeightedPrimeEndpoints
import PrimeSquares.GoldbachWeightedMeanCutoffs

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

noncomputable def goldbachWeightedPrimeError (D K : ℝ) : ℝ :=
  2*(2*K+1)/((4/9:ℝ)*D)^3+1/(Real.exp ((4/9:ℝ)*D)*((4/9:ℝ)*D)^2)

theorem goldbach_weighted_large_rectangle (D a R A K : ℝ) (n : ℤ) (P : Finset ℕ)
    (hD : 18≤D) (ha : 2≤a) (haU : a≤Real.exp (D/9)/2) (hA : 0≤A) (hK : 0≤K)
    (hM : ClassicalPrimeLogMertens K)
    (hP : ∀ p∈P,p.Prime ∧ p%4=3 ∧ Real.exp ((4/9:ℝ)*D)≤(p:ℝ) ∧
      a≤goldbachWeightedUBound D p)
    (hmean : ∀ t∈Set.Icc a (Real.exp (D/9)/2),
      goldbachRealSummatory (goldbachWeightedMultiplicative R n) t≤A*t/Real.sqrt (Real.log t)) :
    (∑ p∈P,(1/(p:ℝ))*∑ u∈Ioc ⌊a⌋₊ ⌊goldbachWeightedUBound D p⌋₊,
      goldbachWeightedMultiplicative R n u/
        ((u:ℝ)*(D-Real.log (2*(p:ℝ))-Real.log u)^2))≤
      (A/(2*D^2))*Real.sqrt (1+Real.log 2/Real.log a)*Real.sqrt D*
        (8*Real.sqrt 2*goldbachWeightedW (9/8))+
      A*goldbachWeightedPrimeError D K*
        ((Real.log (Real.exp (D/9)/2)-Real.log a)/Real.sqrt (Real.log a))+
      A/(Real.sqrt (Real.log a)*((4/9:ℝ)*D)^2)*((D/2+K)/((4/9:ℝ)*D)) := by
  classical
  let z := Real.exp ((4/9:ℝ)*D)
  let U := Real.exp (D/9)/2
  let q := fun u : ℝ=>1/(u*Real.sqrt (Real.log u))
  let J := fun u : ℝ=>goldbachWeightedInnerIntegral (Real.log (2*u)/D)
  let S := fun u : ℝ=>∑ p∈P.filter (fun p : ℕ=>u≤goldbachWeightedUBound D p),
    1/((p:ℝ)*(D-Real.log (2*(p:ℝ))-Real.log u)^2)
  have hD0 : 0<D := by linarith
  have hz2 : 2≤z := by
    have hh := Real.add_one_le_exp ((4/9:ℝ)*D)
    dsimp only [z]
    linarith
  have hlogz : Real.log z=(4/9:ℝ)*D := Real.log_exp _
  have hpgeom (p : ℕ) (hp : p∈P) :=
    goldbach_weighted_double_p_geometry D a p hD ha (hP p hp).2.2.1 (hP p hp).2.2.2
  have hpRec : (∑ p∈P,1/(p:ℝ))≤(D/2+K)/((4/9:ℝ)*D) := by
    have hzB : z≤Real.exp (D/2) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hh := goldbach_weighted_prime_reciprocal K z (Real.exp (D/2)) hM hz2 hzB P (by
      intro p hp
      refine ⟨(hP p hp).1,(hP p hp).2.2.1,?_⟩
      apply (Real.log_le_log_iff (hpgeom p hp).1 (Real.exp_pos _)).mp
      rw [Real.log_exp]
      exact (hpgeom p hp).2.2.1)
    simpa only [Real.log_exp,hlogz] using hh
  have hprime : ∀ u∈Set.Icc a U,S u≤(1/(2*D^2))*J u+goldbachWeightedPrimeError D K := by
    intro u hu
    have hu0 : 0<u := by linarith [hu.1]
    have hg := goldbach_weighted_double_u_geometry D a u hD ha hu
    let Q := P.filter (fun p : ℕ=>u≤goldbachWeightedUBound D p)
    have hQ : ∀ p∈Q,p.Prime ∧ p%4=3 ∧ z≤(p:ℝ) ∧ (p:ℝ)≤goldbachWeightedPBound D u := by
      intro p hp
      obtain ⟨hpP,hpu⟩ := mem_filter.mp hp
      exact ⟨(hP p hpP).1,(hP p hpP).2.1,(hP p hpP).2.2.1,
        (goldbach_weighted_double_domain D u p hu0 (hpgeom p hpP).1).mp hpu⟩
    have hh := goldbach_weighted_prime_finite_upper K D (2*u) z (goldbachWeightedPBound D u)
      hK hM hz2 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2 Q hQ
    have hsum : S u=∑ p∈Q,1/((p:ℝ)*(D-Real.log (2*u)-Real.log p)^2) := by
      apply sum_congr rfl
      intro p hp
      have hp0 := (hpgeom p (mem_filter.mp hp).1).1
      rw [Real.log_mul (by norm_num) hp0.ne',Real.log_mul (by norm_num) hu0.ne']
      congr 2
      ring
    have hm := goldbach_weighted_inner_mellin D (Real.log (2*u)/D) hD0 hg.1.le hg.2.1
    have hb : Real.exp (D*(1-Real.log (2*u)/D)/2)=goldbachWeightedPBound D u := by
      dsimp only [goldbachWeightedPBound]
      congr 1
      field_simp
    rw [hb] at hm
    have hi : (∫ t in Set.Ioc z (goldbachWeightedPBound D u),
        1/(t*Real.log t*(D-Real.log (2*u)-Real.log t)^2))=(1/D^2)*J u := by
      rw [←intervalIntegral.integral_of_le hg.2.2.1]
      apply Eq.trans _ hm
      apply intervalIntegral.integral_congr
      intro t ht
      rw [mul_div_cancel₀ _ hD0.ne']
    rw [hsum]
    rw [hi,hlogz] at hh
    dsimp only [goldbachWeightedPrimeError]
    convert hh using 1;dsimp only [J,z];ring
  have hcont := goldbach_weighted_double_integrands_continuous D a hD ha
  have hq : IntegrableOn q (Set.Icc a U) := hcont.2.1.integrableOn_Icc
  have hqJ : IntegrableOn (fun u : ℝ=>q u*J u) (Set.Icc a U) :=
    (hcont.2.1.mul hcont.1).integrableOn_Icc
  have hE : 0≤goldbachWeightedPrimeError D K := by
    dsimp only [goldbachWeightedPrimeError]
    positivity
  have hint : (∫ u in Set.Icc a U,q u*S u)≤
      (1/(2*D^2))*(∫ u in Set.Icc a U,q u*J u)+
        goldbachWeightedPrimeError D K*(∫ u in Set.Icc a U,q u) := by
    have hright : IntegrableOn (fun u : ℝ=>(1/(2*D^2))*(q u*J u)+
        goldbachWeightedPrimeError D K*q u) (Set.Icc a U) :=
      (hqJ.const_mul _).add (hq.const_mul _)
    have hh := integral_mono_of_nonneg (μ:=volume.restrict (Set.Icc a U))
      (f:=fun u=>q u*S u) (g:=fun u=>(1/(2*D^2))*(q u*J u)+goldbachWeightedPrimeError D K*q u)
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
          have hu0 : 0≤u := by linarith [hu.1]
          exact mul_nonneg (by dsimp only [q];positivity)
            (sum_nonneg (fun p _=>one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))))
      hright (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        have hq0 : 0≤q u := by
          have hu0 : 0≤u := by linarith [hu.1]
          dsimp only [q]
          positivity
        have hh := mul_le_mul_of_nonneg_left (hprime u hu) hq0
        nlinarith only [hh])
    simpa only [integral_add (hqJ.const_mul _) (hq.const_mul _),integral_const_mul] using hh
  have hmain := goldbach_weighted_double_integral_le_W D a hD ha haU
  have hmain' : (∫ u in Set.Icc a U,q u*J u)≤
      Real.sqrt (1+Real.log 2/Real.log a)*Real.sqrt D*(8*Real.sqrt 2*goldbachWeightedW (9/8)) := by
    apply le_trans _ hmain
    apply le_of_eq
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp only [q,J]
    ring
  have hsmall := goldbach_weighted_log_harmonic_integral_le a U ha haU
  have hab := goldbach_weighted_double_abel R D a U A ((4/9:ℝ)*D) n P
    (fun p=>goldbachWeightedUBound D p) ha haU hA (by positivity)
    (by intro p hp;exact ⟨(hP p hp).1.pos,(hP p hp).2.2.2,(hpgeom p hp).2.1⟩)
    (fun p hp u hu=>(hpgeom p hp).2.2.2 u hu)
    (by
      intro p hp
      have hp0 := (hpgeom p hp).1
      have hlow := Real.log_le_log (Real.exp_pos ((4/9:ℝ)*D)) (hP p hp).2.2.1
      rw [Real.log_exp] at hlow
      have hh := Real.log_le_log (by linarith : 0<a) (hP p hp).2.2.2
      rw [(goldbach_weighted_u_bound_log D p hp0).2,
        Real.log_mul (by norm_num) hp0.ne'] at *
      linarith) hmean
  have hcoef : 0≤1/(2*D^2) := by positivity
  have hbound := add_le_add (mul_le_mul_of_nonneg_left hmain' hcoef)
    (mul_le_mul_of_nonneg_left hsmall hE)
  have hbdy := mul_le_mul_of_nonneg_left hpRec
    (show 0≤A/(Real.sqrt (Real.log a)*((4/9:ℝ)*D)^2) by positivity)
  have hInt := mul_le_mul_of_nonneg_left (hint.trans hbound) hA
  dsimp only [q,S] at hab hInt
  apply hab.trans
  apply (add_le_add hInt hbdy).trans_eq
  dsimp only [U]
  ring

end PrimeSquares
