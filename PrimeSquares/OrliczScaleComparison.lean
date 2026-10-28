import PrimeSquares.PrimeSquareDyadicAnnularEndpoint

namespace PrimeSquares

theorem orliczWeight_half_add_le {L a : ℝ} (hL : 2 ≤ L) (ha : 0 ≤ a) :
    orliczWeight (1/2) (L+a) ≤ orliczWeight (1/2) L+Real.sqrt a/2 := by
  have hL0 : 0 ≤ L := by linarith
  have hden : 2 ≤ 2+Real.log L := by linarith [Real.log_nonneg (by linarith : 1 ≤ L)]
  have hden' : 0 < 2+Real.log (L+a) := by
    have := Real.log_nonneg (by linarith : 1 ≤ L+a)
    linarith
  have hl : 2+Real.log L ≤ 2+Real.log (L+a) := by
    linarith [Real.log_le_log (by linarith : 0 < L) (by linarith : L ≤ L+a)]
  have hs : Real.sqrt (L+a) ≤ Real.sqrt L+Real.sqrt a := by
    have hs0 := Real.sqrt_nonneg (L+a)
    have hs1 := Real.sqrt_nonneg L
    have hs2 := Real.sqrt_nonneg a
    have hsq0 := Real.sq_sqrt (by linarith : 0 ≤ L+a)
    have hsq1 := Real.sq_sqrt hL0
    have hsq2 := Real.sq_sqrt ha
    nlinarith [mul_nonneg hs1 hs2]
  dsimp [orliczWeight]
  rw [←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow]
  calc
    _ ≤ (Real.sqrt L+Real.sqrt a)/(2+Real.log L) :=
      (div_le_div_of_nonneg_right hs hden'.le).trans
        (div_le_div_of_nonneg_left (by positivity) (by linarith) hl)
    _ = Real.sqrt L/(2+Real.log L)+Real.sqrt a/(2+Real.log L) := add_div _ _ _
    _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_left (Real.sqrt_nonneg a) (by norm_num) hden)

theorem paperPhi_half_fixed_rescale {c a b K : ℝ} (hc : 0 ≤ c) (ha : 0 < a)
    (hb : b ≤ 1) (hK : 1 ≤ K) (hab : a ≤ b) (hba : b ≤ K*a) :
    paperPhi c (1/2) a ≤ Real.exp (c*Real.sqrt (Real.log K)/2)*paperPhi c (1/2) b := by
  have hbp : 0 < b := ha.trans_le hab
  have hKp : 0 < K := by linarith
  have hla : paperLog a ≤ paperLog b+Real.log K := by
    rw [paperLog_of_le_one ha (hab.trans hb),paperLog_of_le_one hbp hb]
    have hlog := Real.log_le_log hbp hba
    rw [Real.log_mul hKp.ne' ha.ne'] at hlog
    linarith
  have hW := (orliczWeight_half_mono (paperLog_two_le a) hla).trans
    (orliczWeight_half_add_le (paperLog_two_le b) (Real.log_nonneg hK))
  rw [paperPhi_eq_exp_weight,paperPhi_eq_exp_weight,←Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hW hc])

end PrimeSquares
