import PrimeSquares.CircleHighDenominatorSplit
import PrimeSquares.OrdinaryOnlySourceSymbol

namespace PrimeSquares

theorem centeredLowSymbol_large_ordinary_zero (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) (r : ℚ) (hr : Q < (r.den : ℝ)) :
    centeredLowSymbol N hN q₀ Q B χ (fun _ => 0) β r=0 := by
  ext θ
  change rationalLowModelTerm N q₀ Q B χ (fun _ => 0) β r (θ+(r : ℝ))*
    Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) θ)=0
  rw [rationalLowModelTerm_no_exception,ite_eq_right (not_le.mpr hr),zero_mul]

theorem centeredHighSymbol_large_ordinary (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) (r : ℚ) (hr : Q < (r.den : ℝ)) :
    centeredHighSymbol N hN q₀ Q B χ (fun _ => 0) β r=centeredRationalSymbol N hN χ (fun _ => 0) β r := by
  rw [centeredHighSymbol,centeredLowSymbol_large_ordinary_zero N hN q₀ Q B χ β r hr,sub_zero]

end PrimeSquares
