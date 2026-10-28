import PrimeSquares.OrdinaryCollarMaximalPairing
import PrimeSquares.RealCutoffCanonicalFilter

namespace PrimeSquares

theorem ordinaryHigh_filtered_source (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (hq₀ : 0 < q₀)
    {Q R B : ℝ} (hQ : 0 < Q) (hQR : Q ≤ R) (hB : 0 < B)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    circleHighModel ((sourceRationalCenters R).filter (fun r => (r.den : ℝ) ≤ Q)) N hN q₀ Q B χ (fun _ => 0) β=
      rationalCollarBlock (canonicalRationalCenters ⌊Q⌋₊) N hN Q (fun _ => 1) rationalPrincipalGauss := by
  rw [sourceCenters_real_filter hQ.le hQR]
  apply circleHighModel_ordinary_collar _ N hN q₀ hq₀ hQ hB χ β
  intro r hr
  have hd := (mem_canonicalRationalCenters ⌊Q⌋₊ r).mp hr
  exact (by exact_mod_cast hd.2 : (r.den : ℝ) ≤ ⌊Q⌋₊).trans (Nat.floor_le hQ.le)

end PrimeSquares
