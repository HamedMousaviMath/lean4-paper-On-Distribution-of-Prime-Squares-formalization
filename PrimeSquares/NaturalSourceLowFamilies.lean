import PrimeSquares.SourceLowPairing

open scoped lp
namespace PrimeSquares

structure NaturalSourceLowData (N : ℕ) (Q : ℝ) where
  scale_lower : 2 ≤ N
  cutoff_lower : 2 ≤ Q
  radius : ℝ
  cutoff_le : Q ≤ radius
  scale_budget : radius^4 ≤ (N : ℝ)/2
  conductor : ℕ
  conductor_pos : 0 < conductor
  character : DirichletCharacter ℂ conductor
  quadratic : character.IsQuadratic
  active : Bool
  beta : ℝ
  beta_le_one : beta ≤ 1

noncomputable def NaturalSourceLowData.symbol {N : ℕ} {Q : ℝ} (D : NaturalSourceLowData N Q) : C(PrimeCircle, ℂ) := by
  letI : NeZero D.conductor := ⟨D.conductor_pos.ne'⟩
  exact circleLowModel (sourceRationalCenters D.radius) N (by have h := D.scale_lower;omega) D.conductor Q
    (conductorMajorant D.conductor) (sourceInducedCharacter D.conductor D.character)
    (sourceExceptionalSelector D.conductor D.active) D.beta

theorem naturalSourceLowData_L1_norm {N : ℕ} {Q : ℝ} (D : NaturalSourceLowData N Q) :
    ‖fourierL1Operator D.symbol‖ ≤ 2*realLowAmplitude N Q := by
  have : NeZero D.conductor := ⟨D.conductor_pos.ne'⟩
  exact sourceFullLow_L1_norm D.scale_lower D.conductor D.character D.quadratic D.active D.beta_le_one
    D.cutoff_lower D.cutoff_le (source_fourth_budget_to_eighth D.scale_budget)

theorem naturalSourceLow_countable_maximal {N₀ : ℕ} (hN₀ : 2 ≤ N₀) {Q : ℝ}
    (N : ℕ → ℕ) (D : ∀ j,NaturalSourceLowData (N j) Q) (hN : ∀ j,N₀ ≤ N j) (f : ℓ¹(ℤ, ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) ⊤,
      (∀ x : ℤ,g x=⨆ j : ℕ,‖integerMultiplier (D j).symbol
        (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x‖) ∧
      ‖g‖ ≤ 2*realLowAmplitude N₀ Q*‖f‖ := by
  let T (j : ℕ) := fourierL1Operator (D j).symbol
  have hT : ∀ j,‖T j‖ ≤ 2*realLowAmplitude N₀ Q := fun j =>
    (naturalSourceLowData_L1_norm (D j)).trans (mul_le_mul_of_nonneg_left
      (realLowAmplitude_scale_mono (by omega) (hN j) (by have h := (D j).cutoff_lower;linarith)) (by norm_num))
  refine ⟨operatorL1Maximum T hT f,?_,operatorL1Maximum_norm T hT f⟩
  intro x
  change (⨆ j : ℕ,‖fourierL1Operator (D j).symbol f x‖)=_
  exact iSup_congr (fun j => congrArg norm (fourierL1Operator_all_l2_agreement (D j).symbol f x))

end PrimeSquares
