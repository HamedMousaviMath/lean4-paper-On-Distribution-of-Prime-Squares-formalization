import PrimeSquares.OrliczGrowth

/-! # Exact geometric interpolation of two restricted pair bounds -/

namespace PrimeSquares

theorem complementary_count_normalization {L f g α : ℝ}
    (hL : 0 < L) (hf : 0 ≤ f) (hg : 0 ≤ g) :
    f^α*g^(1-α)/L = (f/L)^α*(g/L)^(1-α) := by
  rw [Real.div_rpow hf hL.le, Real.div_rpow hg hL.le, div_mul_div_comm,
    ← Real.rpow_add hL, show α+(1-α)=1 by ring, Real.rpow_one]

theorem restricted_geometric_interpolation {R A B f g q t α a b : ℝ}
    (hR0 : 0 ≤ R) (hA : 0 < A) (hB : 0 < B) (hf : 0 < f) (hg : 0 < g)
    (ht : 0 < t) (ht1 : t < 1)
    (ha : a=t*q+(1-t)*α) (hb : b=t*q+(1-t)*(1-α))
    (hE : R ≤ A*f^q*g^q) (hP : R ≤ B*f^α*g^(1-α)) :
    R ≤ (A^t*B^(1-t))*f^a*g^b := by
  by_cases hR : R = 0
  · subst R
    positivity
  have hRp : 0 < R := lt_of_le_of_ne hR0 (Ne.symm hR)
  have hlogE : Real.log R ≤ Real.log A+q*Real.log f+q*Real.log g := by
    have h := Real.log_le_log hRp hE
    rw [Real.log_mul (mul_pos hA (Real.rpow_pos_of_pos hf q)).ne'
        (Real.rpow_pos_of_pos hg q).ne',
      Real.log_mul hA.ne' (Real.rpow_pos_of_pos hf q).ne',
      Real.log_rpow hf, Real.log_rpow hg] at h
    exact h
  have hlogP : Real.log R ≤ Real.log B+α*Real.log f+(1-α)*Real.log g := by
    have h := Real.log_le_log hRp hP
    rw [Real.log_mul (mul_pos hB (Real.rpow_pos_of_pos hf α)).ne'
        (Real.rpow_pos_of_pos hg (1-α)).ne',
      Real.log_mul hB.ne' (Real.rpow_pos_of_pos hf α).ne',
      Real.log_rpow hf, Real.log_rpow hg] at h
    exact h
  have hlog : Real.log R ≤ t*Real.log A+(1-t)*Real.log B+a*Real.log f+b*Real.log g := by
    calc
      _ = t*Real.log R+(1-t)*Real.log R := by ring
      _ ≤ t*(Real.log A+q*Real.log f+q*Real.log g) +
          (1-t)*(Real.log B+α*Real.log f+(1-α)*Real.log g) := add_le_add
        (mul_le_mul_of_nonneg_left hlogE ht.le)
        (mul_le_mul_of_nonneg_left hlogP (by linarith))
      _ = _ := by rw [ha, hb]; ring
  calc
    _ = Real.exp (Real.log R) := (Real.exp_log hRp).symm
    _ ≤ Real.exp (t*Real.log A+(1-t)*Real.log B+a*Real.log f+b*Real.log g) :=
      Real.exp_le_exp.mpr hlog
    _ = _ := by
      rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB,
        Real.rpow_def_of_pos hf, Real.rpow_def_of_pos hg]
      simp only [← Real.exp_add]
      congr 1
      ring

end PrimeSquares
