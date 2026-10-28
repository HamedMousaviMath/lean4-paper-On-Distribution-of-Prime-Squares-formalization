import PrimeSquares.GoldbachRankinDecay

set_option autoImplicit false
open Finset Filter
namespace PrimeSquares

theorem goldbach_source_rankin_tail {C t : ℝ} (hC : 1≤C) (ht : 0<t) :
    ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →∀ D : ℕ,D≠0 →
      (∀ p∈D.primeFactors,(p:ℝ)≤(Real.log N)^C) →∀ S : Finset ℕ,
      (∀ q∈S,q∈D.divisors ∧ (N:ℝ)/(100*Real.sqrt ((Real.log N)^C))<(q:ℝ)) →
      (∑ q∈S,(q.divisors.card:ℝ)^11/(q:ℝ))≤(Real.log N)^(-t) := by
  obtain ⟨K,_,hbound⟩ := goldbach_rankin_tail_log_bound
  have he := goldbach_rankin_parameter_decay hC goldbachPrimeProductConstant_pos ht K
  have hlog : Tendsto (fun N : ℕ=>Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hn := hlog.eventually (he.and (eventually_ge_atTop (Real.exp 1)))
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp hn
  refine ⟨max N₁ 4,le_max_right _ _,?_⟩
  intro N hN D hD hDR S hS
  have hNpos : 0<N := by omega
  have hNR : (0:ℝ)<N := by exact_mod_cast hNpos
  obtain ⟨hdec,hx⟩ := hN₁ N ((le_max_left _ _).trans hN)
  let x := Real.log (N:ℝ)
  let R := x^C
  let L := Real.log (2*R)
  let Y := (N:ℝ)/(100*Real.sqrt R)
  let σ := 1/(2*L)
  have hx0 : 0<x := (Real.exp_pos 1).trans_le hx
  have hx1 : 1≤x := (Real.add_one_le_exp (1:ℝ)).trans hx |>.trans' (by norm_num)
  have hx2 : 2≤x := (by norm_num : (2:ℝ)≤1+1).trans ((Real.add_one_le_exp (1:ℝ)).trans hx)
  have hlx : 1≤Real.log x := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
  have hR : 2≤R := hx2.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 hC)
  have hRp : 0<R := by linarith
  have hlogR : Real.log R=C*Real.log x := Real.log_rpow hx0 C
  have hL : L=Real.log 2+Real.log R := Real.log_mul (by norm_num) hRp.ne'
  have hL1 : 1≤L := by
    rw [hL,hlogR]
    have hlog2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hlx)]
  have hLp : 0<L := by linarith
  have hσ : 0<σ := by dsimp [σ];positivity
  have hσ1 : σ≤1/2 := by
    dsimp [σ]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*L)).mpr
    nlinarith
  have hσR : σ*Real.log R≤1 := by
    have heq : σ*L=1/2 := by dsimp [σ];field_simp
    have hlog2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
    have hh : Real.log R≤L := by rw [hL];linarith
    have hb := mul_le_mul_of_nonneg_left hh hσ.le
    linarith
  have hY : 0<Y := by dsimp [Y];positivity
  have htail := hbound R σ Y hR hσ hσ1 hσR hY D hD hDR S hS
  apply htail.trans
  simpa only [x,R,L,Y,σ,Real.exp_log hNR] using hdec

end PrimeSquares
