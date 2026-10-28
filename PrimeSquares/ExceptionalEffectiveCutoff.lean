import PrimeSquares.HighFactorInterpolation
import PrimeSquares.ConductorRatioBound

namespace PrimeSquares

theorem exceptional_effective_cutoff {q q₀ Q B : ℝ} (hq₀ : 0 < q₀) :
    q/q₀ ≤ Q/B ↔ q ≤ Q*q₀/B := by
  have he : (Q/B)*q₀=Q*q₀/B := by ring
  rw [div_le_iff₀ hq₀,he]

theorem exceptional_effective_width {N q q₀ Q B : ℝ} (hq₀ : 0 < q₀) (hQ : 0 < Q) (hB : 0 < B) :
    B*(q/q₀)*N^2/Q=q*N^2/(Q*q₀/B) := by
  field_simp

theorem exceptional_effective_ratio {q q₀ Q B : ℝ} (hq₀ : 0 < q₀) (hQ : 0 < Q) (hB : 0 < B) :
    q/(Q*q₀/B)=(B/q₀)*(q/Q) := by
  field_simp

end PrimeSquares
