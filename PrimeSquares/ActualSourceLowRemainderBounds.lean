import PrimeSquares.SourceErrorAbsorption
import PrimeSquares.SourceScaleLowEstimate

namespace PrimeSquares

theorem actualSource_low_remainder_uniform {η P C B d c A : ℝ} (hη0 : 0 < η) (hηhalf : η < 1/2)
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ d) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ H : ℝ,0 < H ∧ ∃ N₀ : ℕ,4 ≤ N₀ ∧ ∀ N : ℕ,N₀ ≤ N → ∀ Q : ℝ,2 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log N) →
    ∀ (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀),χ₀.IsQuadratic →
    ∀ (active : Bool) (β : ℝ),
      CircleAnalyticInputs N Q (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β P C B d c →
    ∀ hN : 1 ≤ N,
      ‖circleLowOperator (sourceRationalCenters (sourceMajorArcScale N Q)) N hN q₀ Q
        (conductorMajorant q₀) (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β‖ ≤
        2*realLowAmplitude N Q ∧
      ‖sourceRemainderOperator (sourceRationalCenters (sourceMajorArcScale N Q)) N hN q₀ Q
        (conductorMajorant q₀) (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β‖ ≤ H*Q^(-η) := by
  obtain ⟨H,hH,N₁,hN₁,hh⟩ := sourceRemainder_uniform_absorbed hη0 hηhalf hP hC hB hd hc hA
  obtain ⟨N₂,hN₂,hl⟩ := sourceFullLow_uniform_source_range hc
  refine ⟨H,hH,max N₁ N₂,le_trans hN₁ (le_max_left _ _),?_⟩
  intro N hn Q hQ hQl q₀ inst χ₀ hχ active β hi hN
  have hn1 : N₁ ≤ N := le_trans (le_max_left _ _) hn
  have hn2 : N₂ ≤ N := le_trans (le_max_right _ _) hn
  exact ⟨(hl N hn2 Q hQ hQl q₀ χ₀ hχ active β hi.beta_le_one hN).1,
    hh N hn1 Q (by linarith) hQl q₀ _ _ β hi hN⟩

end PrimeSquares
