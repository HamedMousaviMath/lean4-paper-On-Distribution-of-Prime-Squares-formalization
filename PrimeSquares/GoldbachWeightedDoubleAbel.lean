import PrimeSquares.GoldbachWeightedMeanAbel
import PrimeSquares.GoldbachWeightedFiniteIntegration

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

theorem goldbach_weighted_double_abel (R M a U A L₀ : ℝ) (n : ℤ)
    (P : Finset ℕ) (b : ℕ→ℝ) (ha : 2≤a) (_haU : a≤U) (hA : 0≤A) (hL₀ : 0<L₀)
    (hP : ∀ p∈P,0<p ∧ a≤b p ∧ b p≤U)
    (hL : ∀ p∈P,∀ u∈Set.Icc a U,2≤M-Real.log (2*(p:ℝ))-Real.log u)
    (hLa : ∀ p∈P,L₀≤M-Real.log (2*(p:ℝ))-Real.log a)
    (hmean : ∀ t∈Set.Icc a U,
      goldbachRealSummatory (goldbachWeightedMultiplicative R n) t≤A*t/Real.sqrt (Real.log t)) :
    (∑ p∈P,(1/(p:ℝ))*∑ u∈Ioc ⌊a⌋₊ ⌊b p⌋₊,
      goldbachWeightedMultiplicative R n u/
        ((u:ℝ)*(M-Real.log (2*(p:ℝ))-Real.log u)^2))≤
      A*(∫ u in Set.Icc a U,(1/(u*Real.sqrt (Real.log u)))*
        ∑ p∈P.filter (fun p=>u≤b p),1/((p:ℝ)*(M-Real.log (2*(p:ℝ))-Real.log u)^2))+
      A/(Real.sqrt (Real.log a)*L₀^2)*(∑ p∈P,1/(p:ℝ)) := by
  classical
  let f := fun p : ℕ=>fun u : ℝ=>
    1/((p:ℝ)*u*Real.sqrt (Real.log u)*(M-Real.log (2*(p:ℝ))-Real.log u)^2)
  have hfi : ∀ p∈P,IntegrableOn (f p) (Set.Icc a U) := by
    intro p hp
    apply ContinuousOn.integrableOn_Icc
    intro u hu
    have hp0 : (p:ℝ)≠0 := by exact_mod_cast (hP p hp).1.ne'
    have hu0 : u≠0 := by linarith [hu.1]
    have hs : Real.sqrt (Real.log u)≠0 :=
      (Real.sqrt_pos.mpr (Real.log_pos (by linarith [hu.1]))).ne'
    have hL0 : M-Real.log (2*(p:ℝ))-Real.log u≠0 := by linarith [hL p hp u hu]
    have hd : (p:ℝ)*u*Real.sqrt (Real.log u)*(M-Real.log (2*(p:ℝ))-Real.log u)^2≠0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hp0 hu0) hs) (pow_ne_zero 2 hL0)
    apply ContinuousAt.continuousWithinAt
    dsimp only [f]
    fun_prop
  have hlocal : ∀ p∈P,
      (1/(p:ℝ))*(∑ u∈Ioc ⌊a⌋₊ ⌊b p⌋₊,goldbachWeightedMultiplicative R n u/
        ((u:ℝ)*(M-Real.log (2*(p:ℝ))-Real.log u)^2))≤
      A*(∫ u in Set.Icc a (b p),f p u)+
        A/(Real.sqrt (Real.log a)*L₀^2)*(1/(p:ℝ)) := by
    intro p hp
    have hbp := (hP p hp).2.1
    have hsub : Set.Icc a (b p)⊆Set.Icc a U := Set.Icc_subset_Icc le_rfl (hP p hp).2.2
    have hh := goldbach_weighted_mean_abel R M (2*(p:ℝ)) a (b p) A n ha hbp hA
      (fun u hu=>hL p hp u (hsub hu)) (fun u hu=>hmean u (hsub hu))
    have hp0 : (0:ℝ)<p := by exact_mod_cast (hP p hp).1
    have hloga : 0<Real.log a := Real.log_pos (by linarith)
    have hsq := pow_le_pow_left₀ hL₀.le (hLa p hp) 2
    have hbdy := div_le_div_of_nonneg_left hA
      (mul_pos (Real.sqrt_pos.mpr hloga) (sq_pos_of_pos hL₀))
      (mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg (Real.log a)))
    have hh' := mul_le_mul_of_nonneg_left hh (one_div_nonneg.mpr hp0.le)
    have hbdy' := mul_le_mul_of_nonneg_left hbdy (one_div_nonneg.mpr hp0.le)
    have hi : (1/(p:ℝ))*(∫ u in Set.Ioc a (b p),
        1/(u*Real.sqrt (Real.log u)*(M-Real.log (2*(p:ℝ))-Real.log u)^2))=
        ∫ u in Set.Icc a (b p),f p u := by
      rw [integral_Icc_eq_integral_Ioc,←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      dsimp only [f]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [mul_add] at hh'
    apply (hh'.trans (add_le_add le_rfl hbdy')).trans_eq
    rw [←hi]
    ring
  have hs := sum_le_sum hlocal
  rw [sum_add_distrib,←mul_sum,←mul_sum] at hs
  have hfub := goldbach_finite_variable_interval P a U b f
    (fun p hp=>(hP p hp).2.2) hfi
  rw [hfub] at hs
  apply hs.trans_eq
  congr 2
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  dsimp only
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  dsimp only [f]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end PrimeSquares
