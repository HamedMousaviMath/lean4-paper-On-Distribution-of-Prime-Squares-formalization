import PrimeSquares.LogPowerAbsorption
import PrimeSquares.ConductorDecay
import PrimeSquares.ConductorRatioBound
import PrimeSquares.ConductorClassPowerDecay
import PrimeSquares.InterpolationGeometry

open Filter Finset
namespace PrimeSquares

theorem shifted_log_power_uniform (m : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ L : ℝ,0<L ∧ ∀ x : ℝ,1 ≤ x → (1+Real.log x)^m ≤ L*x^ε := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp (eventually_log_rpow_le_rpow (m : ℝ) hε)
  let Y := max X (Real.exp 1)
  have hY : 0<Y := (Real.exp_pos 1).trans_le (le_max_right _ _)
  have hY1 : 1 ≤ Y := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans (le_max_right _ _)
  have hLY : 0 ≤ Real.log Y := Real.log_nonneg hY1
  refine ⟨(2 : ℝ)^m+(1+Real.log Y)^m,by positivity,?_⟩
  intro x hx
  have hxp : 0<x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hpow : (1 : ℝ) ≤ x^ε := Real.one_le_rpow hx hε.le
  by_cases hxy : x ≤ Y
  · have hl : Real.log x ≤ Real.log Y := Real.log_le_log hxp hxy
    have h : (1+Real.log x)^m ≤ (1+Real.log Y)^m := pow_le_pow_left₀ (by positivity) (by linarith) m
    exact h.trans (by nlinarith [show (0 : ℝ) ≤ (2 : ℝ)^m by positivity,
      show (0 : ℝ) ≤ (1+Real.log Y)^m by positivity])
  · have hYx : Y ≤ x := (lt_of_not_ge hxy).le
    have hLX : 1 ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1) ((le_max_right X (Real.exp 1)).trans hYx)
      simpa only [Real.log_exp] using h
    have hb : (Real.log x)^m ≤ x^ε := by
      simpa only [Real.rpow_natCast] using hX x ((le_max_left _ _).trans hYx)
    have ha : (1+Real.log x)^m ≤ (2*Real.log x)^m := pow_le_pow_left₀ (by positivity) (by linarith) m
    rw [mul_pow] at ha
    exact (ha.trans (mul_le_mul_of_nonneg_left hb (by positivity))).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ (1+Real.log Y)^m))
        (Real.rpow_nonneg (by linarith : 0 ≤ x) ε))

theorem conductor_logarithmic_decay : ∃ L : ℝ,0<L ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      conductorSigma q χ*(conductorMajorant q)^(1/2 : ℝ)*(1+Real.log q)^3 ≤
        L*(q : ℝ)^(-(1/50 : ℝ)) := by
  obtain ⟨S,hS,hdec⟩ := conductorSigma_majorant_decay
  obtain ⟨D,hD,hlog⟩ := shifted_log_power_uniform 3 (by norm_num : (0 : ℝ)<1/50)
  refine ⟨S*D,by positivity,?_⟩
  intro q inst χ
  have hq : (0 : ℝ)<q := by exact_mod_cast NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hσ : conductorSigma q χ*(conductorMajorant q)^(1/2 : ℝ) ≤ S*(q : ℝ)^(-(1/25 : ℝ)) := by
    simpa only [Real.sqrt_eq_rpow] using hdec q χ
  calc
    _ ≤ (S*(q : ℝ)^(-(1/25 : ℝ)))*(D*(q : ℝ)^(1/50 : ℝ)) :=
      mul_le_mul hσ (hlog q hq1) (by positivity) (by positivity)
    _ = (S*D)*((q : ℝ)^(-(1/25 : ℝ))*(q : ℝ)^(1/50 : ℝ)) := by ring
    _ = _ := by rw [←Real.rpow_add hq];norm_num

theorem effective_threshold_logarithmic_bound {Q W : ℝ} (hQ : 1 ≤ Q) (hW : 1 ≤ W)
    (q : ℕ) (hq : 0<q) (hupper : W ≤ Q*(q : ℝ)) :
    (1+Real.log W)^3 ≤ (1+Real.log Q)^3*(1+Real.log q)^3 := by
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQp : 0<Q := by linarith
  have hqp : (0 : ℝ)<q := by exact_mod_cast hq
  have hLW : 0 ≤ Real.log W := Real.log_nonneg hW
  have hLQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hLq : 0 ≤ Real.log q := Real.log_nonneg hqr
  have hlog := Real.log_le_log (by linarith : 0<W) hupper
  rw [Real.log_mul hQp.ne' hqp.ne'] at hlog
  rw [←mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith

theorem effective_threshold_large_uniform : ∃ T : ℝ,0<T ∧ ∀ Q : ℝ,16*T ≤ Q →
    ∀ q : ℕ,0<q → 16 ≤ Q*(q : ℝ)/conductorMajorant q := by
  obtain ⟨T,hT,hb⟩ := conductorMajorant_linear_bound
  refine ⟨T,hT,?_⟩
  intro Q hQ q hq
  have hqp : (0 : ℝ)<q := by exact_mod_cast hq
  have hB : 0<conductorMajorant q := lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le q hq)
  apply (le_div_iff₀ hB).mpr
  have h := hb q hq
  nlinarith

theorem finite_conductor_class_linear_budget {ε : ℝ} (hε : 0<ε) (q : ℕ → ℕ)
    (hclass : ∀ i,2^i ≤ q i) (S : Finset ℕ) :
    (∑ i ∈ S,(q i : ℝ)^(-ε)) ≤ (1-(2 : ℝ)^(-ε))⁻¹ := by
  obtain ⟨hr0,hr1⟩ := dyadic_decay_ratio hε
  calc
    _ ≤ ∑ i ∈ S,((2 : ℝ)^(-ε))^i := sum_le_sum (fun i _ => conductor_class_power_decay hε.le q hclass i)
    _ ≤ ∑' i : ℕ,((2 : ℝ)^(-ε))^i :=
      (summable_geometric_of_lt_one hr0.le hr1).sum_le_tsum S (fun i _ => pow_nonneg hr0.le i)
    _ = _ := tsum_geometric_of_lt_one hr0.le hr1

end PrimeSquares
