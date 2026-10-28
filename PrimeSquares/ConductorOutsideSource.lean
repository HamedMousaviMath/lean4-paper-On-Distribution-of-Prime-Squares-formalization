import PrimeSquares.SourceLowSquaredRange

open Finset
namespace PrimeSquares

theorem centeredLowSymbol_coefficient_zero (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (hk : κ r=0) :
    centeredLowSymbol N hN q₀ Q B₀ χ κ β r=centeredLowSymbol N hN q₀ Q B₀ χ (fun _ => 0) β r := by
  ext θ
  simp [centeredLowSymbol,rationalLowModelTerm,rationalExceptionalModelTerm,hk]

theorem circleLowTerm_coefficient_zero (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (hk : κ r=0) :
    circleLowTerm N hN q₀ Q B₀ χ κ β r=circleLowTerm N hN q₀ Q B₀ χ (fun _ => 0) β r := by
  exact congrArg (fun m : C(PrimeCircle, ℂ) => circleFrequencyShift m (((r : ℝ) : PrimeCircle)))
    (compactCircleLift_congr _ _ (centeredLowSymbol_support N hN q₀ Q B₀ χ κ β r)
      (centeredLowSymbol_support N hN q₀ Q B₀ χ (fun _ => 0) β r)
      (centeredLowSymbol_coefficient_zero N hN q₀ Q B₀ χ κ β r hk))

theorem sourceLowModel_conductor_outside (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (Q R β : ℝ) (active : Bool)
    (hR : 0 ≤ R) (hqR : R < (q₀ : ℝ)) :
    circleLowModel (sourceRationalCenters R) N hN q₀ Q (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (sourceExceptionalSelector q₀ active) β=
    circleLowModel (sourceRationalCenters R) N hN q₀ Q (conductorMajorant q₀)
      (sourceInducedCharacter q₀ χ₀) (fun _ => 0) β := by
  classical
  unfold circleLowModel
  apply sum_congr rfl
  intro r hr
  have hd : ¬q₀ ∣ r.den := by
    intro hd
    have hq : (q₀ : ℝ) ≤ r.den := by exact_mod_cast Nat.le_of_dvd r.den_pos hd
    exact not_le_of_gt hqR (hq.trans ((mem_sourceRationalCenters hR r).mp hr).2)
  apply circleLowTerm_coefficient_zero
  simp only [sourceExceptionalSelector,hd,and_false,ite_false]

theorem realExceptionalDenominators_empty {q₀ M : ℕ} (hM : M < q₀) (Q : ℝ) :
    realExceptionalDenominators q₀ M Q=∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hp : 0 < q₀ := by omega
  obtain ⟨hd1,_,hqd⟩ := (mem_realExceptionalDenominators hp Q).mp hd
  have hh : q₀ ≤ q₀*d := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left q₀ hd1
  omega

theorem realExceptionalLowModel_empty (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (Q : ℝ) (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) {M : ℕ} (hM : M < q₀) : realExceptionalLowModel N hN q₀ χ₀ Q hQ hb β M=0 := by
  rw [realExceptionalLowModel,realExceptionalDenominators_empty hM Q,sum_empty]

end PrimeSquares
