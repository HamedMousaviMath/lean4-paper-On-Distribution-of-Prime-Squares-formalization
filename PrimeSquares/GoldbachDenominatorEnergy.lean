import PrimeSquares.GoldbachDivisorSquareTail

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_centers_denominator_sum (Y : ℝ) (F : ℕ→ℝ) :
    (∑ r∈sourceRationalCenters Y,F r.den)=∑ q∈Icc 1 ⌊Y⌋₊,(q.totient:ℝ)*F q := by
  rw [sourceRationalCenters_sum_units]
  apply sum_congr rfl
  intro q hq
  let : NeZero q := ⟨by have hh := (mem_Icc.mp hq).1;omega⟩
  rw [denominatorUnitSum_pos]
  simp only [unitRational_den,sum_const,card_univ,nsmul_eq_mul,ZMod.card_units_eq_totient]

theorem goldbach_centers_filtered_denominator_sum (Y : ℝ) (F : ℕ→ℝ)
    (P : ℕ→Prop) [DecidablePred P] :
    (∑ r∈(sourceRationalCenters Y).filter (fun r=>P r.den),F r.den)=
      ∑ q∈(Icc 1 ⌊Y⌋₊).filter P,(q.totient:ℝ)*F q := by
  have h := goldbach_centers_denominator_sum Y (fun q=>if P q then F q else 0)
  simpa only [sum_filter,mul_ite,mul_zero] using h

theorem goldbach_major_prefactor_count (N q : ℕ) (hq : 0<q) :
    (q.totient:ℝ)*(goldbachMajorArithmeticPrefactor N q)^2≤
      (9*Real.exp 2)^2*(Real.log N)^4*((q.divisors.card:ℝ)^12/(q:ℝ)^2) := by
  have hqp : (0:ℝ)<q := by exact_mod_cast hq
  have hφ : (q.totient:ℝ)≤q := by exact_mod_cast Nat.totient_le q
  apply (mul_le_mul_of_nonneg_right hφ (sq_nonneg _)).trans_eq
  unfold goldbachMajorArithmeticPrefactor
  simp only [mul_pow,div_pow,←pow_mul,Real.sq_sqrt (Nat.cast_nonneg q)]
  field_simp
  ring

theorem goldbach_added_denominator_energy_budget :
    ∃ K : ℝ,0<K ∧ ∀ N : ℕ,∀ R : ℝ,2≤R →∀ Y : ℝ,
      (∑ r∈(sourceRationalCenters Y).filter (fun r=>R<(r.den:ℝ)),
        (goldbachMajorArithmeticPrefactor N r.den)^2)≤K*(Real.log N)^4/Real.sqrt R := by
  classical
  obtain ⟨K,hK,hbound⟩ := goldbach_divisor_square_tail
  refine ⟨(9*Real.exp 2)^2*K,by positivity,?_⟩
  intro N R hR Y
  rw [goldbach_centers_filtered_denominator_sum Y (fun q=>goldbachMajorArithmeticPrefactor N q^2) (fun q : ℕ=>R<(q:ℝ))]
  let S := (Icc 1 ⌊Y⌋₊).filter (fun q : ℕ=>R<(q:ℝ))
  have hS : ∀ q∈S,R<(q:ℝ) := fun q hq=>(mem_filter.mp hq).2
  have hSq : ∀ q∈S,0<q := by
    intro q hq
    have hh : (0:ℝ)<q := (by linarith : (0:ℝ)<R).trans (hS q hq)
    exact_mod_cast hh
  change (∑ q∈S,(q.totient:ℝ)*(goldbachMajorArithmeticPrefactor N q)^2)≤_
  calc
    _≤∑ q∈S,(9*Real.exp 2)^2*(Real.log N)^4*((q.divisors.card:ℝ)^12/(q:ℝ)^2) :=
      sum_le_sum (fun q hq=>goldbach_major_prefactor_count N q (hSq q hq))
    _=((9*Real.exp 2)^2*(Real.log N)^4)*(∑ q∈S,(q.divisors.card:ℝ)^12/(q:ℝ)^2) := by rw [mul_sum]
    _≤((9*Real.exp 2)^2*(Real.log N)^4)*(K/Real.sqrt R) :=
      mul_le_mul_of_nonneg_left (hbound R hR S hS) (by positivity)
    _=_ := by ring

end PrimeSquares
