import PrimeSquares.DyadicAnnularFrequencyDecay
import Mathlib.Analysis.SpecificLimits.Normed

namespace PrimeSquares

theorem dyadic_annular_square_summable {M : ℕ} (hM : 2 ≤ M) {β q Q θ : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hq : 0 < q) (hQ : 0 < Q)
    (hθ : Q/(2*q*(M : ℝ)^2) ≤ |θ|) :
    Summable (fun j : ℕ => ‖annularOscillatoryModel ((2 : ℕ)^j*M) β θ‖^2) := by
  have hg := hasSum_geometric_of_norm_lt_one (ξ := (1/16 : ℝ)) (by norm_num)
  apply Summable.of_nonneg_of_le (fun j => sq_nonneg _) _ (hg.summable.mul_left ((4*q/(Real.pi*Q))^2))
  intro j
  have h := pow_le_pow_left₀ (norm_nonneg _) (dyadic_annular_frequency_decay hM hβ0 hβ1 hq hQ hθ j) 2
  have he : ((1/4 : ℝ)^j)^2=(1/16 : ℝ)^j := by
    rw [←pow_mul,Nat.mul_comm j 2,pow_mul]
    norm_num
  simpa only [mul_pow,he] using h

theorem dyadic_annular_square_total {M : ℕ} (hM : 2 ≤ M) {β q Q θ : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hq : 0 < q) (hQ : 0 < Q)
    (hθ : Q/(2*q*(M : ℝ)^2) ≤ |θ|) :
    (∑' j : ℕ,‖annularOscillatoryModel ((2 : ℕ)^j*M) β θ‖^2) ≤
      (16/15 : ℝ)*(4*q/(Real.pi*Q))^2 := by
  have hg := hasSum_geometric_of_norm_lt_one (ξ := (1/16 : ℝ)) (by norm_num)
  have hs := dyadic_annular_square_summable hM hβ0 hβ1 hq hQ hθ
  calc
    _ ≤ ∑' j : ℕ,(4*q/(Real.pi*Q))^2*(1/16 : ℝ)^j := by
      apply hs.tsum_le_tsum _ (hg.summable.mul_left _)
      intro j
      have h := pow_le_pow_left₀ (norm_nonneg _) (dyadic_annular_frequency_decay hM hβ0 hβ1 hq hQ hθ j) 2
      have he : ((1/4 : ℝ)^j)^2=(1/16 : ℝ)^j := by
        rw [←pow_mul,Nat.mul_comm j 2,pow_mul]
        norm_num
      simpa only [mul_pow,he] using h
    _ = _ := by rw [tsum_mul_left,hg.tsum_eq];norm_num;ring

end PrimeSquares
