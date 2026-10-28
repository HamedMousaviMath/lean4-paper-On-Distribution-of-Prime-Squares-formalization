import PrimeSquares.OrdinaryFourPieceConvolution
namespace PrimeSquares
noncomputable def effectiveCollarCutoff (Q : ℝ) (q₀ : ℕ) : ℝ := Q*(q₀ : ℝ)/conductorMajorant q₀
theorem effectiveCollarCutoff_pos {Q : ℝ} (hQ : 0 < Q) {q₀ : ℕ} (hq₀ : 0 < q₀) :
    0 < effectiveCollarCutoff Q q₀ := by
  have hB : 0 < conductorMajorant q₀ := lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le q₀ hq₀)
  unfold effectiveCollarCutoff
  positivity
theorem effectiveCollarCutoff_condition {Q : ℝ} {q₀ : ℕ} (hq₀ : 0 < q₀) (r : ℚ) :
    (r.den : ℝ)/(q₀ : ℝ) ≤ Q/conductorMajorant q₀ ↔ (r.den : ℝ) ≤ effectiveCollarCutoff Q q₀ :=
  exceptional_effective_cutoff (by exact_mod_cast hq₀)
end PrimeSquares
