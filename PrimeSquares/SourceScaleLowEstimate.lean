import PrimeSquares.NaturalSourceLowFamilies
import PrimeSquares.SourceScaleFourthPower

namespace PrimeSquares

theorem sourceMajorArcScale_cutoff_le {Q : ℝ} (hQ : 1 ≤ Q) (N : ℝ) : Q ≤ sourceMajorArcScale N Q := by
  calc
    Q = Q^1 := (pow_one _).symm
    _ ≤ Q^8 := pow_le_pow_right₀ hQ (by norm_num)
    _ ≤ _ := le_max_right _ _

theorem sourceFullLow_uniform_source_range {c : ℝ} (hc : 0 < c) :
    ∃ N₀ : ℕ,4 ≤ N₀ ∧ ∀ N : ℕ,N₀ ≤ N → ∀ Q : ℝ,2 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log N) →
    ∀ (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀),χ₀.IsQuadratic →
    ∀ active : Bool,∀ β : ℝ,β ≤ 1 → ∀ hN : 1 ≤ N,
      ‖fourierL1Operator (circleLowModel (sourceRationalCenters (sourceMajorArcScale N Q)) N hN q₀ Q
        (conductorMajorant q₀) (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β)‖ ≤
        2*realLowAmplitude N Q ∧
      ∀ (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ),
        ‖integerMultiplier (circleLowModel (sourceRationalCenters (sourceMajorArcScale N Q)) N hN q₀ Q
          (conductorMajorant q₀) (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β) (finiteInputLp F f 2) x‖ ≤
          (8*lowSpatialConstant*Q*Real.log (2*Q))*dyadicLocalMass ((N : ℝ)^2) F (fun y => ‖f y‖) x := by
  obtain ⟨N₀,hN₀,h⟩ := sourceMajorArcScale_uniform_fourth_power hc
  refine ⟨N₀,hN₀,?_⟩
  intro N hn Q hQ hQl q₀ inst χ₀ hχ active β hβ hN
  have hb := source_fourth_budget_to_eighth (h N hn Q (by linarith) hQl)
  have hn2 : 2 ≤ N := by omega
  have hQR := sourceMajorArcScale_cutoff_le (by linarith : 1 ≤ Q) (N : ℝ)
  exact ⟨sourceFullLow_L1_norm hn2 q₀ χ₀ hχ active hβ hQ hQR hb,
    fun F f x => sourceFullLow_local hn2 q₀ χ₀ hχ active hβ hQ hQR hb F f x⟩

end PrimeSquares
