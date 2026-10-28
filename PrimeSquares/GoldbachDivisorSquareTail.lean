import PrimeSquares.GoldbachRadialMajorIdentity
import Mathlib.Analysis.SumIntegralComparisons

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

theorem goldbach_inverse_three_halves_interval (J M : ℕ) (hJ : 1≤J) (hJM : J≤M) :
    (∑ q∈Icc (J+1) M,(q:ℝ)^(-(3/2:ℝ)))≤2/Real.sqrt J := by
  have hJp : (0:ℝ)<J := by exact_mod_cast hJ
  have hs : Icc (J+1) M=Ico (J+1) (M+1) := by ext q;simp only [mem_Icc,mem_Ico];omega
  have hshift : (∑ q∈Icc (J+1) M,(q:ℝ)^(-(3/2:ℝ)))=
      ∑ i∈Ico J M,((i+1:ℕ):ℝ)^(-(3/2:ℝ)) := by
    rw [hs]
    simpa only [Nat.add_comm] using (sum_Ico_add (fun q : ℕ=>(q:ℝ)^(-(3/2:ℝ))) J M 1).symm
  have ha : AntitoneOn (fun x : ℝ=>x^(-(3/2:ℝ))) (Set.Icc (J:ℝ) M) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (hJp.trans_le hx.1) hxy (by norm_num)
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3/2:ℝ))< -1) hJp
  rw [hshift]
  apply (ha.sum_le_integral_Ico hJM).trans
  calc
    _=∫ x in Set.Ioc (J:ℝ) M,x^(-(3/2:ℝ)) := intervalIntegral.integral_of_le (by exact_mod_cast hJM)
    _≤∫ x in Set.Ioi (J:ℝ),x^(-(3/2:ℝ)) := setIntegral_mono_set hi (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact Real.rpow_nonneg (hJp.trans hx).le _) (Filter.Eventually.of_forall (fun x hx=>hx.1))
    _=_ := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-(3/2:ℝ))< -1) hJp,
        show (-(3/2:ℝ))+1= -(1/2:ℝ) by norm_num,Real.rpow_neg hJp.le,←Real.sqrt_eq_rpow]
      ring

theorem goldbach_inverse_three_halves_tail {R : ℝ} (hR : 2≤R)
    (S : Finset ℕ) (hS : ∀ q∈S,R<(q:ℝ)) :
    (∑ q∈S,(q:ℝ)^(-(3/2:ℝ)))≤4/Real.sqrt R := by
  let J := ⌊R⌋₊
  let M := max J (S.sup id)
  have hJ : 2≤J := (Nat.le_floor_iff (by linarith : 0≤R)).mpr hR
  have hJp : (0:ℝ)<J := by exact_mod_cast (show 0<J by omega)
  have hRp : 0<R := by linarith
  have hsub : S⊆Icc (J+1) M := by
    intro q hq
    exact mem_Icc.mpr ⟨by have hh := (Nat.floor_lt hRp.le).mpr (hS q hq);omega,
      (Finset.le_sup (f:=id) hq : q≤S.sup id).trans (le_max_right _ _)⟩
  have hfloor := Nat.lt_floor_add_one R
  have hRJ : R≤4*(J:ℝ) := by
    have hjR : (2:ℝ)≤J := by exact_mod_cast hJ
    dsimp only [J] at hjR ⊢
    linarith
  have hroot : Real.sqrt R≤2*Real.sqrt J := by
    calc
      _≤Real.sqrt (4*(J:ℝ)) := Real.sqrt_le_sqrt hRJ
      _=_ := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),
          show Real.sqrt (4:ℝ)=2 by rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)]]
  calc
    _≤∑ q∈Icc (J+1) M,(q:ℝ)^(-(3/2:ℝ)) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun q _ _=>Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _≤2/Real.sqrt J := goldbach_inverse_three_halves_interval J M (by omega) (le_max_left _ _)
    _≤4/Real.sqrt R := (div_le_div_iff₀ (Real.sqrt_pos.mpr hJp) (Real.sqrt_pos.mpr hRp)).mpr (by linarith)

theorem goldbach_divisor_square_tail :
    ∃ K : ℝ,0<K ∧ ∀ R : ℝ,2≤R →∀ S : Finset ℕ,(∀ q∈S,R<(q:ℝ)) →
      (∑ q∈S,(q.divisors.card:ℝ)^12/(q:ℝ)^2)≤K/Real.sqrt R := by
  obtain ⟨C,hC,hbound⟩ := divisors_card_rpow_le_rpow (by norm_num : (0:ℝ)<12) (by norm_num : (0:ℝ)<1/2)
  refine ⟨4*C,by positivity,?_⟩
  intro R hR S hS
  have hterm (q : ℕ) (hq : q∈S) : (q.divisors.card:ℝ)^12/(q:ℝ)^2≤C*(q:ℝ)^(-(3/2:ℝ)) := by
    have hqp : (0:ℝ)<q := (by linarith : (0:ℝ)<R).trans (hS q hq)
    have hqn : 0<q := by exact_mod_cast hqp
    have hτ : (q.divisors.card:ℝ)^12≤C*(q:ℝ)^(1/2:ℝ) := by
      simpa only [show (12:ℝ)=((12:ℕ):ℝ) by norm_num,Real.rpow_natCast] using hbound q hqn
    have he : (q:ℝ)^(1/2:ℝ)/(q:ℝ)^2=(q:ℝ)^(-(3/2:ℝ)) := by
      rw [←Real.rpow_natCast (q:ℝ) 2,←Real.rpow_sub hqp]
      congr 1
      norm_num
    exact (div_le_div_of_nonneg_right hτ (sq_nonneg (q:ℝ))).trans_eq (by rw [mul_div_assoc,he])
  calc
    _≤∑ q∈S,C*(q:ℝ)^(-(3/2:ℝ)) := sum_le_sum hterm
    _=C*(∑ q∈S,(q:ℝ)^(-(3/2:ℝ))) := by rw [mul_sum]
    _≤C*(4/Real.sqrt R) := mul_le_mul_of_nonneg_left (goldbach_inverse_three_halves_tail hR S hS) hC.le
    _=_ := by ring

end PrimeSquares
