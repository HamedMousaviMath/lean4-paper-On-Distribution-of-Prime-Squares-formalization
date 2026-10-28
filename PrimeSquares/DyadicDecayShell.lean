import PrimeSquares.DecayProfile

namespace PrimeSquares

theorem decayProfile_dyadic_shell {H x : ℝ} (hH : 0 < H) (j k : ℕ)
    (hx : (2 : ℝ)^j*H ≤ |x|) :
    decayProfile H k x ≤ ((2 : ℝ)^(j*k))⁻¹ := by
  have hdiv : (2 : ℝ)^j ≤ |x|/H := (le_div_iff₀ hH).mpr hx
  have hp : ((2 : ℝ)^j)^k ≤ (1+|x|/H)^k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  rw [←pow_mul] at hp
  unfold decayProfile
  exact inv_anti₀ (by positivity) hp

theorem dyadic_shell_normalization (j k : ℕ) (hk : 1 ≤ k) :
    ((2 : ℝ)^(j*k))⁻¹*(2 : ℝ)^j = ((2 : ℝ)^((k-1)*j))⁻¹ := by
  have he : j*k = j+(k-1)*j := by
    calc
      j*k = j*((k-1)+1) := congrArg (fun n : ℕ => j*n) (Nat.sub_add_cancel hk).symm
      _ = _ := by ring
  rw [he,pow_add,mul_inv_rev]
  have h : (2 : ℝ)^j ≠ 0 := by positivity
  field_simp

end PrimeSquares
