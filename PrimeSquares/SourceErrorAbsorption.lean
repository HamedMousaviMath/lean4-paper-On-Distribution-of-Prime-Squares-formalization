import PrimeSquares.SourceRemainderPower

namespace PrimeSquares

theorem sourceError_power_absorb {N : ℕ} (hN : 1 ≤ N) {Q A η : ℝ} (hQ : 1 ≤ Q)
    (hA : 0 ≤ A) (hη : η ≤ 1/2) :
    2*((2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A)) ≤ (2*(2 : ℝ)^A)*Q^(-η) := by
  have hl : 1 ≤ 1+Real.log N := by have hh := Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ N);linarith
  have hw : (1+Real.log N)^(-A) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1) hl (neg_nonpos.mpr hA)
  have hq : Q^(-(1/2 : ℝ)) ≤ Q^(-η) := Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  calc
    _ ≤ 2*((2 : ℝ)^A*Q^(-(1/2 : ℝ))*1) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (by positivity)) (by norm_num)
    _ ≤ 2*((2 : ℝ)^A*Q^(-η)) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ (2 : ℝ)^A)) (by norm_num : (0 : ℝ) ≤ 2)
    _ = _ := by ring

theorem sourceRemainder_uniform_absorbed {η P C B d c A : ℝ} (hη0 : 0 < η) (hηhalf : η < 1/2)
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ d) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ H : ℝ,0 < H ∧ ∃ N₀ : ℕ,4 ≤ N₀ ∧ ∀ N : ℕ,N₀ ≤ N → ∀ Q : ℝ,1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log N) →
    ∀ (q₀ : ℕ) [NeZero q₀] (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ),
      CircleAnalyticInputs N Q χ κ β P C B d c → ∀ hN : 1 ≤ N,
      ‖sourceRemainderOperator (sourceRationalCenters (sourceMajorArcScale N Q)) N hN q₀ Q
        (conductorMajorant q₀) χ κ β‖ ≤ H*Q^(-η) := by
  obtain ⟨H,hH,N₀,hN₀,h⟩ := sourceRemainder_uniform hη0 hηhalf hP hC hB hd hc hA
  refine ⟨H+2*(2 : ℝ)^A,by positivity,N₀,hN₀,?_⟩
  intro N hn Q hQ hQl q₀ inst χ κ β hi hN
  have he := sourceError_power_absorb hN hQ hA hηhalf.le
  have hh := h N hn Q hQ hQl q₀ χ κ β hi hN
  nlinarith

end PrimeSquares
