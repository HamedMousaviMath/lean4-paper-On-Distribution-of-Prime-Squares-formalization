import PrimeSquares.AnnularModelSize

open MeasureTheory

namespace PrimeSquares

theorem quadraticOscillation_joint_continuous :
    Continuous (fun z : ℝ × ℝ => quadraticOscillation z.1 z.2) := by
  unfold quadraticOscillation
  fun_prop

theorem annularOscillatoryModel_continuous {N : ℕ} (hN : 1 ≤ N) (β : ℝ) :
    Continuous (annularOscillatoryModel N β) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  let f : ℝ → ℝ → ℂ := fun θ t =>
    Complex.ofReal ((max t ((N : ℝ)/2))^(β-1))*quadraticOscillation θ t
  have hf : Continuous f.uncurry := by
    apply Continuous.mul
    · apply Complex.continuous_ofReal.comp
      apply Continuous.rpow_const
      · exact continuous_snd.max continuous_const
      · intro z
        exact Or.inl (ne_of_gt ((by positivity : (0 : ℝ) < (N : ℝ)/2).trans_le (le_max_right _ _)))
    · exact quadraticOscillation_joint_continuous
  have hi := continuous_parametric_integral_of_continuous (μ := volume) hf
    (s := Set.Icc ((N : ℝ)/2) (N : ℝ)) isCompact_Icc
  have he : annularOscillatoryModel N β = fun θ =>
      Complex.ofReal ((N : ℝ)⁻¹) * ∫ t in Set.Icc ((N : ℝ)/2) N, f θ t := by
    funext θ
    rw [annularOscillatoryModel, integral_Icc_eq_integral_Ioc]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp only [f, max_eq_left ht.1.le]
  rw [he]
  exact continuous_const.mul hi

end PrimeSquares
