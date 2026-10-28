import PrimeSquares.CombinedSourceCollarPairing
namespace PrimeSquares
theorem sourceCollarDifference_inactive (N : ℕ) (hN : 1 ≤ N) {Q R : ℝ} {q₀ : ℕ}
    (hQ : 0 < Q) (hq₀ : 0 < q₀) (hR : 0 ≤ R) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    sourceCollarDifference N hN Q R q₀ false χ β=
      rationalCollarBlock (canonicalRationalCenters ⌊Q⌋₊) N hN Q (fun _ => 1) rationalPrincipalGauss := by
  rw [sourceCollarDifference,clipped_source_collar_identity N hN hQ hq₀ hR]
  ext θ
  simp [rationalCollarBlock,sourceExceptionalSelector_inactive]
end PrimeSquares
