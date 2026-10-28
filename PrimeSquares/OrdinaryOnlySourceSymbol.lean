import PrimeSquares.OrdinaryCenteredLowSource

namespace PrimeSquares

theorem rationalLowModelTerm_no_exception (N q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) (r : ℚ) (ξ : ℝ) :
    rationalLowModelTerm N q₀ Q B₀ χ (fun _ => 0) β r ξ=
      if (r.den : ℝ) ≤ Q then rationalOrdinaryModelTerm N r ξ*ordinaryNarrowCutoff N Q r ξ else 0 := by
  simp only [rationalLowModelTerm,rationalExceptionalModelTerm,zero_mul,mul_zero,neg_zero,ite_self,add_zero]

theorem centeredLowSymbol_no_exception {N : ℕ} (hN : 1 ≤ N) (r : ℚ)
    {Q R : ℝ} (hQ : 0 < Q) (hQR : Q ≤ R) (hr : (r.den : ℝ) ≤ R)
    (hb : 2*R^4 ≤ (N : ℝ)^2) (q₀ : ℕ) (B₀ : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    centeredLowSymbol N hN q₀ Q B₀ χ (fun _ => 0) β r=
      if (r.den : ℝ) ≤ Q then ordinaryCenteredLow N hN Q r else 0 := by
  ext θ
  change rationalLowModelTerm N q₀ Q B₀ χ (fun _ => 0) β r (θ+(r : ℝ))*
    Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) θ)=_
  rw [rationalLowModelTerm_no_exception]
  by_cases hd : (r.den : ℝ) ≤ Q
  · simp only [ite_eq_left hd]
    have ho := ordinaryNarrowCutoff_mul_broad hN r (ξ := θ+(r : ℝ)) hQ hQR hr hb
    simp only [add_sub_cancel_right] at ho
    rw [mul_assoc,ho]
    exact (ordinaryCenteredLow_source N hN Q r θ).symm
  · simp only [ite_eq_right hd,zero_mul,ContinuousMap.zero_apply]

end PrimeSquares
