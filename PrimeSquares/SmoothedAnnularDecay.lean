import PrimeSquares.SmoothedAnnularKernel

namespace PrimeSquares

theorem smoothedAnnularKernel_decay {N : ℕ} (hN : 2 ≤ N) {β a : ℝ}
    (hβ : β ≤ 1) (ha : 0 < a) (haN : a ≤ (N : ℝ)^2) (K : ℕ) (x : ℝ) :
    ‖smoothedAnnularKernel N β a x‖ ≤
      (2^K*cutoffDecayConstant K/(2*a))*decayProfile ((N : ℝ)^2) K x := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 1 ≤ N)
  have hH : 0 < (N : ℝ)^2 := sq_pos_of_pos hNp
  let B : ℝ := (cutoffDecayConstant K/a)*2^K*decayProfile ((N : ℝ)^2) K x
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (N : ℝ)/2) (b := (N : ℝ))
    (f := fun t => Complex.ofReal (t^(β-1))*scaledCutoffKernel a (x-t^2)) (C := B) (by
      intro t ht
      rw [Set.uIoc_of_le (by linarith : (N : ℝ)/2 ≤ N)] at ht
      have htc : t ∈ Set.Icc ((N : ℝ)/2) N := ⟨ht.1.le,ht.2⟩
      have ht0 : 0 ≤ t := by linarith [ht.1]
      have hp : 0 ≤ t^(β-1) := Real.rpow_nonneg ht0 _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
      have hs := scaledCutoffKernel_larger_profile ha haN K (x-t^2)
      have hd : decayProfile ((N : ℝ)^2) K (x-t^2) ≤
          2^K*decayProfile ((N : ℝ)^2) K x := by
        simpa only [one_add_one_eq_two] using
          (decayProfile_shift_bound (H := (N : ℝ)^2) (C := 1) (x := x) (y := t^2) hH
            (by norm_num) (by simpa only [one_mul] using annular_square_support (by omega : 1 ≤ N) htc) K)
      have hh : ‖scaledCutoffKernel a (x-t^2)‖ ≤ B := hs.trans (by
        dsimp [B];simpa only [add_self_div_two,one_add_one_eq_two,mul_assoc] using
          mul_le_mul_of_nonneg_left hd (div_nonneg (cutoffDecayConstant_nonneg K) ha.le))
      exact (mul_le_mul_of_nonneg_right (annular_density_le_one hN hβ htc) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hh))
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ)-(N : ℝ)/2)] at hi
  rw [smoothedAnnularKernel,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hNp.le)]
  calc
    _ ≤ (N : ℝ)⁻¹*(B*((N : ℝ)-(N : ℝ)/2)) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hNp.le)
    _ = _ := by dsimp [B];field_simp;ring

end PrimeSquares
