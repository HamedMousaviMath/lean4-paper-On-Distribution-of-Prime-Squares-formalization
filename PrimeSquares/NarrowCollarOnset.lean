import PrimeSquares.SourceArcCutoff

namespace PrimeSquares

theorem narrow_collar_onset {a θ b : ℝ} (ha : 0 < a)
    (hcontain : sourceArcCutoff (a*θ)*b=sourceArcCutoff (a*θ))
    (hne : b-sourceArcCutoff (a*θ) ≠ 0) : 1/(2*a) < |θ| := by
  by_contra h
  have hθ : |θ| ≤ 1/(2*a) := le_of_not_gt h
  have hc : sourceArcCutoff (a*θ)=1 := by
    apply sourceArcCutoff_core
    rw [abs_mul,abs_of_pos ha]
    have ht := (le_div_iff₀ (by positivity : (0 : ℝ) < 2*a)).mp hθ
    nlinarith
  rw [hc,one_mul] at hcontain
  exact hne (by rw [hc,hcontain,sub_self])

theorem ordinary_collar_frequency_lower {N Q q θ b : ℝ} (hQ : 0 < Q) (hq : 0 < q) (hN : 0 < N)
    (hc : sourceArcCutoff ((q*N^2/Q)*θ)*b=sourceArcCutoff ((q*N^2/Q)*θ))
    (hne : b-sourceArcCutoff ((q*N^2/Q)*θ) ≠ 0) : Q/(2*q*N^2) < |θ| := by
  have h := narrow_collar_onset (by positivity : (0 : ℝ) < q*N^2/Q) hc hne
  have he : 1/(2*(q*N^2/Q))=Q/(2*q*N^2) := by field_simp
  rw [he] at h
  exact h

end PrimeSquares
