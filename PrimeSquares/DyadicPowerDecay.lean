import PrimeSquares.DyadicDenominatorPartition

namespace PrimeSquares

theorem dyadic_inverse_rpow {q s : ℕ} (hq : 0 < q) (hlog : Nat.log2 q=s) {ε : ℝ} (hε : 0 ≤ ε) :
    (q : ℝ)^(-ε) ≤ ((2 : ℝ)^(-ε))^s := by
  have hn : (2 : ℕ)^s ≤ q := by simpa only [hlog] using Nat.log2_self_le hq.ne'
  have hscale : (2 : ℝ)^s ≤ q := by exact_mod_cast hn
  have hh := Real.rpow_le_rpow_of_nonpos (pow_pos (by norm_num : (0 : ℝ) < 2) s) hscale (neg_nonpos.mpr hε)
  have he : ((2 : ℝ)^s)^(-ε)=((2 : ℝ)^(-ε))^s := by
    calc
      _ = (2 : ℝ)^((s : ℝ)*(-ε)) := (Real.rpow_natCast_mul (by norm_num) s (-ε)).symm
      _ = (2 : ℝ)^((-ε)*(s : ℝ)) := congrArg (fun z : ℝ => (2 : ℝ)^z) (mul_comm (s : ℝ) (-ε))
      _ = _ := Real.rpow_mul_natCast (by norm_num) (-ε) s
  exact hh.trans_eq he

end PrimeSquares
