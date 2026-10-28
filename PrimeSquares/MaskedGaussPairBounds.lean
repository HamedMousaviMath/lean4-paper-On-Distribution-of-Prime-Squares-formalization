import PrimeSquares.CenteredHighMaskFormula

namespace PrimeSquares

theorem norm_masked_gauss_pair {p t κ f g : ℂ} {B L : ℝ} (hB : 0 ≤ B)
    (hp : ‖p‖ ≤ B) (ht : ‖t‖ ≤ B) (hκ : ‖κ‖ ≤ 1) (hf : ‖f‖ ≤ L) (hg : ‖g‖ ≤ L) :
    ‖p*f-t*(κ*g)‖ ≤ 2*B*L := by
  have hkg : ‖κ*g‖ ≤ L := by
    rw [norm_mul]
    exact (mul_le_mul hκ hg (norm_nonneg _) (by norm_num)).trans (by simp)
  calc
    _ ≤ ‖p*f‖+‖t*(κ*g)‖ := norm_sub_le _ _
    _ ≤ B*L+B*L := add_le_add
      (by rw [norm_mul];exact mul_le_mul hp hf (norm_nonneg _) hB)
      (by rw [norm_mul];exact mul_le_mul ht hkg (norm_nonneg _) hB)
    _ = _ := by ring

theorem maskedGaussPair_two_bounds {N : ℕ} (hN : 2 ≤ N) {β q q₀ Q B C T δ : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hq : 0 < q) (hq₀ : 0 < q₀) (hQ : 0 < Q) (hB : 0 < B)
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hratio : B/q₀ ≤ T) (p t κ : ℂ)
    (hp : ‖p‖ ≤ C*q^(-δ)) (ht : ‖t‖ ≤ C*q^(-δ)) (hk : ‖κ‖ ≤ 1) (θ : ℝ) :
    ‖p*annularHighFactor N 1 q Q θ-t*(κ*annularHighFactor N β q (Q*q₀/B) θ)‖ ≤
        (2*C*highMaskConstant*(1+T))*q^(-δ) ∧
    ‖p*annularHighFactor N 1 q Q θ-t*(κ*annularHighFactor N β q (Q*q₀/B) θ)‖ ≤
        (2*C*highMaskConstant*(1+T))*q^(-δ)*q/Q := by
  have hK := highMaskConstant_one_le
  have hK0 : 0 ≤ highMaskConstant := by linarith
  have hW : 0 < Q*q₀/B := by positivity
  have hD1 : 1 ≤ highMaskConstant*(1+T) := one_le_mul_of_one_le_of_one_le hK (by linarith)
  have hcq : 0 ≤ C*q^(-δ) := mul_nonneg hC (Real.rpow_pos_of_pos hq _).le
  have hs := norm_masked_gauss_pair hcq hp ht hk
    ((annularHighFactor_half hN (by norm_num : (1 : ℝ) ≤ 1) q Q θ).trans (by norm_num : (1/2 : ℝ) ≤ 1))
    ((annularHighFactor_half hN hβ1 q (Q*q₀/B) θ).trans (by norm_num : (1/2 : ℝ) ≤ 1))
  have hO : ‖annularHighFactor N 1 q Q θ‖ ≤ (highMaskConstant*(1+T))*(q/Q) := by
    calc
      _ ≤ highMaskConstant*q/Q := annularHighFactor_linear hN (by norm_num) (by norm_num) hq hQ θ
      _ = (highMaskConstant*(q/Q))*1 := by ring
      _ ≤ (highMaskConstant*(q/Q))*(1+T) := mul_le_mul_of_nonneg_left
        (show (1 : ℝ) ≤ 1+T by linarith) (mul_nonneg hK0 (div_nonneg hq.le hQ.le))
      _ = _ := by ring
  have hE : ‖annularHighFactor N β q (Q*q₀/B) θ‖ ≤ (highMaskConstant*(1+T))*(q/Q) := by
    calc
      _ ≤ highMaskConstant*q/(Q*q₀/B) := annularHighFactor_linear hN hβ0 hβ1 hq hW θ
      _ = highMaskConstant*(B/q₀)*(q/Q) := by rw [mul_div_assoc,exceptional_effective_ratio hq₀ hQ hB];ring
      _ ≤ highMaskConstant*T*(q/Q) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio hK0) (div_nonneg hq.le hQ.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)) hK0) (div_nonneg hq.le hQ.le)
  constructor
  · calc
      _ ≤ 2*(C*q^(-δ))*1 := hs
      _ ≤ (2*(C*q^(-δ)))*(highMaskConstant*(1+T)) :=
        mul_le_mul_of_nonneg_left hD1 (mul_nonneg (by norm_num) hcq)
      _ = _ := by ring
  · have hh := norm_masked_gauss_pair hcq hp ht hk hO hE
    calc
      _ ≤ 2*(C*q^(-δ))*((highMaskConstant*(1+T))*(q/Q)) := hh
      _ = _ := by ring

end PrimeSquares
