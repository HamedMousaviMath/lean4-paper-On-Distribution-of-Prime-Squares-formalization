import PrimeSquares.GoldbachCompletionErrorIdentity

set_option autoImplicit false
open Finset Filter
namespace PrimeSquares

theorem goldbach_uniform_finite_square_sum (N : ℕ) (f : ℕ→ℂ) {M : ℝ}
    (_hM : 0≤M) (hf : ∀ n∈range (N^2),‖f n‖≤M) :
    (∑ n∈range (N^2),‖f n‖^2)≤(N:ℝ)^2*M^2 := by
  calc
    _≤∑ _n∈range (N^2),M^2 := sum_le_sum (fun n hn=>pow_le_pow_left₀ (norm_nonneg _) (hf n hn) 2)
    _=_ := by simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_pow]

theorem goldbach_small_completion_square_budget (N : ℕ) (hlog : 1≤Real.log N)
    {K A C : ℝ} (hK : 0≤K) (hC0 : 0≤C) (hC : 2*A+12≤C) :
    (N:ℝ)^2*(K*(N:ℝ)*(Real.log N)^2*(1+Real.log ((Real.log N)^C))/((Real.log N)^C)^(1/4:ℝ))^2≤
      K^2*(C+1)^2*(N:ℝ)^4*(Real.log N)^(-A) := by
  have hl : 0<Real.log N := by linarith
  have hR : 0<(Real.log N)^C := Real.rpow_pos_of_pos hl _
  have hlogR : 1+Real.log ((Real.log N)^C)≤(C+1)*Real.log N := by
    rw [Real.log_rpow hl]
    have hh := Real.log_le_self hl.le
    nlinarith
  have hroot : (((Real.log N)^C)^(1/4:ℝ))^2=Real.sqrt ((Real.log N)^C) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hR.le,Real.sqrt_eq_rpow]
    norm_num
  have hb : K*(N:ℝ)*(Real.log N)^2*(1+Real.log ((Real.log N)^C))/((Real.log N)^C)^(1/4:ℝ)≤
      K*(C+1)*(N:ℝ)*(Real.log N)^3/((Real.log N)^C)^(1/4:ℝ) := by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogR (by positivity)) (Real.rpow_nonneg hR.le _)).trans_eq
    ring
  have h0 : 0≤K*(N:ℝ)*(Real.log N)^2*(1+Real.log ((Real.log N)^C))/((Real.log N)^C)^(1/4:ℝ) := by
    have hlog0 : 0≤Real.log ((Real.log N)^C) := Real.log_nonneg (Real.one_le_rpow hlog hC0)
    positivity
  calc
    _≤(N:ℝ)^2*(K*(C+1)*(N:ℝ)*(Real.log N)^3/((Real.log N)^C)^(1/4:ℝ))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hb 2) (sq_nonneg _)
    _=(K^2*(C+1)^2*(N:ℝ)^4)*((Real.log N)^6/Real.sqrt ((Real.log N)^C)) := by
      rw [div_pow,hroot]
      ring
    _≤_ := mul_le_mul_of_nonneg_left (goldbach_completion_log_power_rate N hlog 6 A C (by norm_num;linarith)) (by positivity)

theorem goldbach_far_completion_square_budget (N : ℕ) (hlog : 1≤Real.log N)
    {K A : ℝ} (_hK : 0≤K) (hA : 0<A) :
    (N:ℝ)^2*(K*(N:ℝ)*(Real.log N)^(-A))^2≤K^2*(N:ℝ)^4*(Real.log N)^(-A) := by
  have hl : 0<Real.log N := by linarith
  have he : ((Real.log N)^(-A))^2=(Real.log N)^(-2*A) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hl.le]
    congr 1
    ring
  calc
    _=K^2*(N:ℝ)^4*((Real.log N)^(-A))^2 := by ring
    _=K^2*(N:ℝ)^4*(Real.log N)^(-2*A) := by rw [he]
    _≤_ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlog (by linarith : -2*A≤ -A)) (by positivity)

theorem goldbach_completion_all_parameters_eventual {C : ℝ} (hC : 1≤C) :
    ∃ N₀ : ℕ,10000≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      2≤Real.log N ∧ 2≤(Real.log N)^C ∧
      (Real.log N)^C≤(N:ℝ)/(100*Real.sqrt ((Real.log N)^C)) ∧
      1≤(N:ℝ)/(100*Real.sqrt ((Real.log N)^C)) ∧
      (Real.log N)^C/(4*(N:ℝ)^2)<1/2 ∧
      2*((Real.log N)^C/(4*(N:ℝ)^2))<1/((N:ℝ)/(100*Real.sqrt ((Real.log N)^C)))^2 ∧
      2*((Real.log N)^C)^3<(N:ℝ)^2 ∧ (Real.log N)^C/(N:ℝ)^2<1/2 := by
  obtain ⟨N₁,hN₁,h₁⟩ := goldbach_completion_parameters_eventual hC
  obtain ⟨N₂,_hN₂,h₂⟩ := goldbach_major_radius_eventual_budget (3*C) 0
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro N hN
  obtain ⟨hl,hR,hRY,hY,hhalf,hsep⟩ := h₁ N ((le_max_left _ _).trans hN)
  have hNbig : 10000≤N := hN₁.trans ((le_max_left _ _).trans hN)
  have hn : (10000:ℝ)≤N := by exact_mod_cast hNbig
  have hcube : ((Real.log N)^C)^3≤(N:ℝ) := by
    have he : ((Real.log N)^C)^3=(Real.log N)^(3*C) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith : 0≤Real.log N)]
      congr 1
      ring
    rw [he]
    simpa only [neg_zero,Real.rpow_zero,mul_one] using (h₂ N ((le_max_right _ _).trans hN)).2
  have hRN : (Real.log N)^C≤(N:ℝ) := (show (Real.log N)^C≤((Real.log N)^C)^3 by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1≤(Real.log N)^C) (by decide : 1≤3)).trans hcube
  refine ⟨hl,hR,hRY,hY,hhalf,hsep,by nlinarith,?_⟩
  apply (div_lt_iff₀ (by positivity : (0:ℝ)<(N:ℝ)^2)).mpr
  nlinarith

end PrimeSquares
