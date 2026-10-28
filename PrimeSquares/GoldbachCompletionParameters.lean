import PrimeSquares.GoldbachAddedMajorBessel

set_option autoImplicit false
open Filter
namespace PrimeSquares

theorem goldbach_completion_geometry (N : ℕ) (hN : 10000≤N) {R : ℝ}
    (hR : 1≤R) (hCube : R^3≤(N:ℝ)) :
    R≤(N:ℝ)/(100*Real.sqrt R) ∧
      R/(4*(N:ℝ)^2)<1/2 ∧
      2*(R/(4*(N:ℝ)^2))<1/((N:ℝ)/(100*Real.sqrt R))^2 := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hnBig : (10000:ℝ)≤N := by exact_mod_cast hN
  have hr : 0<R := by linarith
  have hRN : R≤(N:ℝ) :=
    (show R≤R^3 by simpa only [pow_one] using pow_le_pow_right₀ hR (by decide : 1≤3)).trans hCube
  have hs100 : (100:ℝ)≤Real.sqrt N := by
    calc
      (100:ℝ)=Real.sqrt 10000 := by rw [show (10000:ℝ)=(100:ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)]
      _≤Real.sqrt N := Real.sqrt_le_sqrt hnBig
  have h100 : 100*Real.sqrt N≤(N:ℝ) := by
    calc
      _≤Real.sqrt N*Real.sqrt N := mul_le_mul_of_nonneg_right hs100 (Real.sqrt_nonneg _)
      _=(N:ℝ) := Real.mul_self_sqrt hn.le
  have hsR : R*Real.sqrt R≤Real.sqrt N := by
    calc
      _=Real.sqrt (R^3) := by rw [pow_succ,Real.sqrt_mul (sq_nonneg R),Real.sqrt_sq hr.le]
      _≤Real.sqrt N := Real.sqrt_le_sqrt hCube
  refine ⟨?_,?_,?_⟩
  · apply (le_div_iff₀ (by positivity : (0:ℝ)<100*Real.sqrt R)).mpr
    calc
      R*(100*Real.sqrt R)=100*(R*Real.sqrt R) := by ring
      _≤100*Real.sqrt N := mul_le_mul_of_nonneg_left hsR (by norm_num)
      _≤(N:ℝ) := h100
  · apply (div_lt_iff₀ (by positivity : (0:ℝ)<4*(N:ℝ)^2)).mpr
    nlinarith
  · have hi : 1/((N:ℝ)/(100*Real.sqrt R))^2=10000*R/(N:ℝ)^2 := by
      rw [div_pow,one_div_div]
      simp only [mul_pow,Real.sq_sqrt hr.le]
      ring
    rw [hi]
    calc
      2*(R/(4*(N:ℝ)^2))=(1/2:ℝ)*(R/(N:ℝ)^2) := by ring
      _<10000*(R/(N:ℝ)^2) := mul_lt_mul_of_pos_right (by norm_num) (by positivity)
      _=_ := by ring

theorem goldbach_completion_parameters_eventual {C : ℝ} (hC : 1≤C) :
    ∃ N₀ : ℕ,10000≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      2≤Real.log N ∧ 2≤(Real.log N)^C ∧
      (Real.log N)^C≤(N:ℝ)/(100*Real.sqrt ((Real.log N)^C)) ∧
      1≤(N:ℝ)/(100*Real.sqrt ((Real.log N)^C)) ∧
      (Real.log N)^C/(4*(N:ℝ)^2)<1/2 ∧
      2*((Real.log N)^C/(4*(N:ℝ)^2))<1/((N:ℝ)/(100*Real.sqrt ((Real.log N)^C)))^2 := by
  obtain ⟨N₁,hN₁,hRadius⟩ := goldbach_major_radius_eventual_budget (3*C) 0
  have hlog : Tendsto (fun N : ℕ=>Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp (hlog.eventually (eventually_ge_atTop (2:ℝ)))
  refine ⟨max N₁ (max N₂ 10000),by omega,?_⟩
  intro N hN
  have hl := hN₂ N ((le_max_left N₂ 10000).trans ((le_max_right _ _).trans hN))
  have hlp : 0<Real.log N := by linarith
  have hr : 2≤(Real.log N)^C := hl.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤Real.log N) hC)
  have he : ((Real.log N)^C)^3=(Real.log N)^(3*C) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hlp.le]
    congr 1
    ring
  have hcube : ((Real.log N)^C)^3≤(N:ℝ) := by
    rw [he]
    simpa only [neg_zero,Real.rpow_zero,mul_one] using (hRadius N ((le_max_left _ _).trans hN)).2
  have hgeom := goldbach_completion_geometry N (by omega) (by linarith : 1≤(Real.log N)^C) hcube
  exact ⟨hl,hr,hgeom.1,(by linarith [hgeom.1]),hgeom.2.1,hgeom.2.2⟩

theorem goldbach_completion_log_power_rate (N : ℕ) (hlog : 1≤Real.log N)
    (j : ℕ) (A C : ℝ) (hC : 2*A+2*(j:ℝ)≤C) :
    (Real.log N)^j/Real.sqrt ((Real.log N)^C)≤(Real.log N)^(-A) := by
  have hl : 0<Real.log N := by linarith
  have he : Real.sqrt ((Real.log N)^C)=(Real.log N)^(C/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hl.le]
    congr 1
    ring
  rw [he,←Real.rpow_natCast (Real.log N) j,←Real.rpow_sub hl]
  exact Real.rpow_le_rpow_of_exponent_le hlog (by linarith)

end PrimeSquares
