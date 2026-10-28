import PrimeSquares.QuadraticWeylInput

set_option autoImplicit false
namespace PrimeSquares

theorem quadratic_weyl_major_approximation {E R ξ : ℝ} (hE : 0 ≤ E)
    (HE : RawQuadraticWeylApproximationInput E) {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hR : 0 ≤ R) (hMN : (N : ℝ) ≤ 2*(M : ℝ)) (hMN' : M ≤ N)
    (hNR : 32*R ≤ (N : ℝ)) {s : ℚ} (hs : (s.den : ℝ) ≤ R)
    (harc : |ξ-(s : ℝ)| ≤ R/((s.den : ℝ)*(N : ℝ)^2)) :
    ‖weightedSquareAverageSymbol M (fun _ => 1) (ξ : PrimeCircle)-
      rationalFullSquareGauss s*initialQuadraticModel M (ξ-(s : ℝ))‖ ≤
        2*E*Real.sqrt R/(N : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  obtain ⟨r, hr, hsmall, herr⟩ := HE M hM ξ
  have hrr : (r.den : ℝ) ≤ 8*(M : ℝ) := by exact_mod_cast hr
  have hMNreal : (M : ℝ) ≤ N := by exact_mod_cast hMN'
  have heq := quadratic_weyl_center_unique hNp hMp hR hMN hMNreal hNR hrr hs hsmall harc
  subst r
  calc
    _ ≤ E*Real.sqrt (s.den : ℝ)/(M : ℝ) := herr
    _ ≤ E*Real.sqrt R/(M : ℝ) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs) hE) hMp.le
    _ ≤ _ := by
      apply (div_le_div_iff₀ hMp hNp).mpr
      have h := mul_le_mul_of_nonneg_left hMN (mul_nonneg hE (Real.sqrt_nonneg R))
      nlinarith

theorem quadratic_weyl_main_outside {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    {R ξ : ℝ} (hR : 0 < R) (hMN : (N : ℝ) ≤ 2*(M : ℝ))
    (hout : OutsideSourceMajorArcs N R ξ) (r : ℚ) :
    ‖rationalFullSquareGauss r*initialQuadraticModel M (ξ-(r : ℝ))‖ ≤
      4*quadraticIntegralConstant/Real.sqrt R := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hsd : 0 < Real.sqrt (r.den : ℝ) := Real.sqrt_pos.mpr hd
  have hC := quadraticIntegralConstant_one_le
  rw [norm_mul]
  by_cases hdr : (r.den : ℝ) ≤ R
  · have hout' := outsideSourceMajorArcs_rational hR.le hout r hdr
    have hθ0 : 0 < |ξ-(r : ℝ)| := (div_pos hR (mul_pos hd (sq_pos_of_pos hNp))).trans_le hout'
    have hθ : ξ-(r : ℝ) ≠ 0 := abs_pos.mp hθ0
    have hsθ : 0 < Real.sqrt |ξ-(r : ℝ)| := Real.sqrt_pos.mpr hθ0
    have hprod : Real.sqrt R ≤ (N : ℝ)*Real.sqrt (r.den : ℝ)*Real.sqrt |ξ-(r : ℝ)| := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [mul_pow, mul_pow, Real.sq_sqrt hR.le, Real.sq_sqrt hd.le, Real.sq_sqrt hθ0.le]
      have h := (div_le_iff₀ (mul_pos hd (sq_pos_of_pos hNp))).mp hout'
      nlinarith
    have hprod' : Real.sqrt R ≤ 2*(M : ℝ)*Real.sqrt (r.den : ℝ)*Real.sqrt |ξ-(r : ℝ)| :=
      hprod.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMN hsd.le) hsθ.le)
    calc
      _ ≤ (2*(Real.sqrt (r.den : ℝ))⁻¹)*
          (quadraticIntegralConstant/((M : ℝ)*Real.sqrt |ξ-(r : ℝ)|)) :=
        mul_le_mul (rationalFullSquareGauss_half_decay r) (initialQuadraticModel_decay hM hθ)
          (norm_nonneg _) (by positivity)
      _ = (2*quadraticIntegralConstant)/((M : ℝ)*Real.sqrt (r.den : ℝ)*Real.sqrt |ξ-(r : ℝ)|) := by ring
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by positivity : 0 < (M : ℝ)*Real.sqrt (r.den : ℝ)*Real.sqrt |ξ-(r : ℝ)|) hsR).mpr
        have h := mul_le_mul_of_nonneg_left hprod' (show 0 ≤ 2*quadraticIntegralConstant by linarith)
        nlinarith
  · have hroot : Real.sqrt R ≤ Real.sqrt (r.den : ℝ) := Real.sqrt_le_sqrt (le_of_not_ge hdr)
    calc
      _ ≤ (2*(Real.sqrt (r.den : ℝ))⁻¹)*1 := mul_le_mul
        (rationalFullSquareGauss_half_decay r) (initialQuadraticModel_norm_one hM _) (norm_nonneg _) (by positivity)
      _ ≤ 2*(Real.sqrt R)⁻¹ := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [one_div] using one_div_le_one_div_of_le hsR hroot) (by norm_num)
      _ ≤ _ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by linarith) (inv_pos.mpr hsR).le

theorem quadratic_weyl_error_scale {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    {E : ℝ} (hE : 0 ≤ E) (hMN : (N : ℝ) ≤ 2*(M : ℝ)) (r : ℚ)
    (hr : r.den ≤ 8*M) :
    E*Real.sqrt (r.den : ℝ)/(M : ℝ) ≤ 8*E/Real.sqrt (N : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNp
  have hsM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMp
  have hd : (r.den : ℝ) ≤ 8*(M : ℝ) := by exact_mod_cast hr
  have hsd := Real.sq_sqrt (show (0 : ℝ) ≤ r.den by positivity)
  have hsM2 := Real.sq_sqrt hMp.le
  have hsN2 := Real.sq_sqrt hNp.le
  have hbound : Real.sqrt (r.den : ℝ) ≤ 4*Real.sqrt (M : ℝ) := by
    nlinarith [Real.sqrt_nonneg (r.den : ℝ)]
  have hbound' : Real.sqrt (N : ℝ) ≤ 2*Real.sqrt (M : ℝ) := by nlinarith
  calc
    _ ≤ E*(4*Real.sqrt (M : ℝ))/(M : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbound hE) hMp.le
    _ = 4*E/Real.sqrt (M : ℝ) := by field_simp; nlinarith
    _ ≤ _ := by
      apply (div_le_div_iff₀ hsM hsN).mpr
      have h := mul_le_mul_of_nonneg_left hbound' (show 0 ≤ 4*E by positivity)
      nlinarith

theorem quadratic_weyl_initial_outside {E R ξ : ℝ} (hE : 0 ≤ E)
    (HE : RawQuadraticWeylApproximationInput E) {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hR : 0 < R) (hMN : (N : ℝ) ≤ 2*(M : ℝ)) (hout : OutsideSourceMajorArcs N R ξ) :
    ‖weightedSquareAverageSymbol M (fun _ => 1) (ξ : PrimeCircle)‖ ≤
      4*quadraticIntegralConstant/Real.sqrt R+8*E/Real.sqrt (N : ℝ) := by
  obtain ⟨r, hr, _hsmall, herr⟩ := HE M hM ξ
  have hmain := quadratic_weyl_main_outside hN hM hR hMN hout r
  have herror := herr.trans (quadratic_weyl_error_scale hN hM hE hMN r hr)
  calc
    _ ≤ ‖weightedSquareAverageSymbol M (fun _ => 1) (ξ : PrimeCircle)-
        rationalFullSquareGauss r*initialQuadraticModel M (ξ-(r : ℝ))‖+
        ‖rationalFullSquareGauss r*initialQuadraticModel M (ξ-(r : ℝ))‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (weightedSquareAverageSymbol M (fun _ => 1) (ξ : PrimeCircle)-
          rationalFullSquareGauss r*initialQuadraticModel M (ξ-(r : ℝ)))
        (rationalFullSquareGauss r*initialQuadraticModel M (ξ-(r : ℝ)))
    _ ≤ _ := by linarith

end PrimeSquares
