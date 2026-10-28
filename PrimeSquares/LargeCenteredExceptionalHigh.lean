import PrimeSquares.FiniteExceptionalCollar
namespace PrimeSquares
theorem centeredExceptionalHigh_large (N : ℕ) (hN : 1 ≤ N) {q₀ : ℕ} (hq₀ : 0 < q₀)
    {Q B : ℝ} (hQ : 0 < Q) (hB : 0 < B) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (hr : Q*(q₀ : ℝ)/B < (r.den : ℝ)) :
    centeredExceptionalHigh N hN q₀ Q B χ κ β r=
      centeredRationalSymbol N hN χ (fun _ => 0) β r-centeredRationalSymbol N hN χ κ β r := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  ext θ
  rw [centeredExceptionalHigh_formula N hN hq₀ hQ hB χ κ β r θ]
  simp only [annularHighFactor,annularHighMask,ite_eq_right (not_le.mpr hr),sub_zero,Complex.ofReal_one,mul_one]
  change _=localizedAnnularGaussModel N r.den (χ r) 0 β (r.num : ZMod r.den) (Nat.log2 r.den) θ-
    localizedAnnularGaussModel N r.den (χ r) (κ r) β (r.num : ZMod r.den) (Nat.log2 r.den) θ
  unfold localizedAnnularGaussModel annularGaussModel rationalTwistedGauss
  ring
end PrimeSquares
