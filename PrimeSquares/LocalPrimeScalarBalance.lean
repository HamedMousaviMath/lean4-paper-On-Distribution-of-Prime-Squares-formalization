import PrimeSquares.PrimeSquareAnnularEndpoint

/-!
# Uniform scalar balance for the stopping estimate

The chosen dyadic Q has log Q bounded by a fixed multiple of paperLog(delta).
The conclusion controls the actual low, high and maximal-error terms,
including all bounded densities.
-/

open Filter Topology
namespace PrimeSquares

noncomputable def localPrimeScalar (c₁ δ Q : ℝ) : ℝ :=
  δ*Q*Real.log Q + δ^(1/2 : ℝ)*Q^(-(1/2 : ℝ))*orliczHighFactor c₁ (1/2) Q +
    δ^(1/2 : ℝ)*Q^(-(1/2 : ℝ))

theorem localPrimeScalar_eq (c₁ δ Q : ℝ) : localPrimeScalar c₁ δ Q =
    orliczScalarSum 1 (1/2) 1 c₁ (1/2) 0 0 1 δ Q := by
  simp only [localPrimeScalar, orliczScalarSum, Real.rpow_one, Real.rpow_zero,
    Real.log_one, add_zero, neg_zero, mul_one]

theorem exists_localPrime_balance {c₁ cstar : ℝ} (hc₁ : 0 < c₁)
    (hstar : orliczLeadingCoefficient 1 (1/2) c₁ (1/2) < cstar) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ j : ℕ, 2 ≤ (2 : ℝ)^j ∧ Real.log ((2 : ℝ)^j) ≤ B*paperLog δ ∧
        localPrimeScalar c₁ δ ((2 : ℝ)^j) ≤ C*δ^(2/3 : ℝ)*paperPhi cstar (1/2) δ := by
  have hcstar : 0 < cstar := (orliczLeadingCoefficient_pos (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1/2) hc₁ (1/2)).trans hstar
  obtain ⟨n, hn, hraw⟩ := exists_admissible_dyadic_orlicz_bound
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1/2) hc₁
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1) hstar 1 (1/2)
  obtain ⟨T, hT⟩ := (hraw 1 0).exists_forall_of_atTop
  let CC := orliczCompactConstant 1 (1/2) 1 c₁ (1/2) 0 T
  have hCC : 0 < CC := orliczCompactConstant_pos _ _ _ _ _ _ _
  let B : ℝ := 4/3 + Real.log 4
  have hl4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hB : 0 < B := by dsimp [B]; linarith
  refine ⟨B, 3+CC, hB, by linarith, ?_⟩
  intro δ hδ hδ1
  have hL := paperLog_two_le δ
  have htarget : 0 ≤ δ^(2/3 : ℝ)*paperPhi cstar (1/2) δ :=
    mul_nonneg (Real.rpow_nonneg hδ.le _) (paperPhi_pos _ _ _).le
  by_cases hlarge : T ≤ paperLog δ
  · let L := paperLog δ
    let N := Real.exp (((4/3 : ℝ)*L)^2)
    have hN : 1 ≤ N := Real.one_le_exp_iff.mpr (sq_nonneg _)
    have hroot : (Real.log N)^(1/2 : ℝ) = (4/3 : ℝ)*L := by
      rw [show Real.log N = ((4/3 : ℝ)*L)^2 by exact Real.log_exp _,
        ← Real.sqrt_eq_rpow, Real.sqrt_sq (by dsimp [L]; linarith)]
    have hcut : L ≤ 1 / (1 / (2*((1 : ℝ)+1/2))+1) * (Real.log N)^(1/2 : ℝ) := by
      rw [hroot]
      convert le_refl L using 1; ring
    have hb := hT L hlarge N 0 hN (by norm_num) hcut
    dsimp only at hb
    rw [exp_two_sub_paperLog hδ hδ1] at hb
    refine ⟨n L, hn L, ?_, ?_⟩
    · have hlog : Real.log ((2 : ℝ)^n L) ≤ (4/3 : ℝ)*L := by
        simpa only [one_mul, hroot] using hb.1
      exact hlog.trans (mul_le_mul_of_nonneg_right
        (show (4/3 : ℝ) ≤ B by dsimp [B]; linarith) (by dsimp [L]; linarith))
    · rw [localPrimeScalar_eq]
      have hh : orliczScalarSum 1 (1/2) 1 c₁ (1/2) 0 0 1 δ ((2 : ℝ)^n L) ≤
          3*δ^(2/3 : ℝ)*paperPhi cstar (1/2) δ := by
        simpa only [orliczScalarSum, orliczHighFactor, neg_zero, Real.rpow_zero, mul_one, highLowDensityExponent,
          show (1 : ℝ)-1/(2*(1+1/2)) = 2/3 by norm_num] using hb.2
      exact hh.trans (by nlinarith)
  · refine ⟨2, by norm_num, ?_, ?_⟩
    · norm_num only [show (2 : ℝ)^(2 : ℕ)=4 by norm_num]
      dsimp [B]
      nlinarith
    · rw [show (2 : ℝ)^(2 : ℕ)=4 by norm_num, localPrimeScalar_eq]
      have hc := orliczScalarSum_compact (by norm_num : (1 : ℝ) ≤ 1) hδ hδ1
        (by norm_num : (2/3 : ℝ) ≤ 1) (le_of_not_ge hlarge) (by norm_num : (0 : ℝ) ≤ 0)
        1 (1/2) 1 c₁ (1/2) 0
      have hPhi := paperPhi_one_le hcstar.le (1/2) δ
      change _ ≤ CC*δ^(2/3 : ℝ) at hc
      have ht : 0 ≤ δ^(2/3 : ℝ) := Real.rpow_nonneg hδ.le _
      nlinarith [mul_le_mul_of_nonneg_left hPhi (mul_nonneg hCC.le ht)]

end PrimeSquares
