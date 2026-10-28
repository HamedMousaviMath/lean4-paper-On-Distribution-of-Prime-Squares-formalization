import PrimeSquares.SourceRemainderOperator

namespace PrimeSquares

theorem sourceRemainder_uniform {η P C B d c A : ℝ} (hη0 : 0 < η) (hηhalf : η < 1/2)
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ d) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ H : ℝ,0 < H ∧ ∃ N₀ : ℕ,4 ≤ N₀ ∧ ∀ (N : ℕ),N₀ ≤ N → ∀ Q : ℝ,1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log N) →
    ∀ (q₀ : ℕ) [NeZero q₀] (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ),
      CircleAnalyticInputs N Q χ κ β P C B d c → ∀ hN : 1 ≤ N,
      ‖sourceRemainderOperator (sourceRationalCenters (sourceMajorArcScale N Q)) N hN q₀ Q
        (conductorMajorant q₀) χ κ β‖ ≤
        H*Q^(-η)+2*((2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A)) := by
  obtain ⟨H,hH,hh⟩ := sourceHigh_power_uniform hη0 hηhalf
  obtain ⟨N₀,hN₀,he⟩ := globalCircleApproximation_l2_operator hP hC hB hd hc hA
  refine ⟨H,hH,N₀,hN₀,?_⟩
  intro N hn Q hQ hQl q₀ inst χ κ β hi hN
  have hn2 : 2 ≤ N := by omega
  have hΓ : ∀ r ∈ sourceRationalCenters (sourceMajorArcScale N Q),
      r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ ⌊sourceMajorArcScale N Q⌋₊ := by
    intro r hr
    exact (mem_canonicalRationalCenters _ r).mp hr
  exact sourceRemainderOperator_norm _ N hN q₀ Q _ χ κ β
    (hh N hn2 Q (by linarith) q₀ _ _ hΓ χ κ β hi.beta_pos.le hi.beta_le_one hi.coefficient_bound).2
    (he N hn Q hQ hQl χ κ β hi hN)

end PrimeSquares
