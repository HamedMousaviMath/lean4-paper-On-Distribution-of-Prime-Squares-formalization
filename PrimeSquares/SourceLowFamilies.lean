import PrimeSquares.SourceFullLowIdentity
import PrimeSquares.RealCombinedLowLocal
import PrimeSquares.AllInputFourierConvolution
import PrimeSquares.UniformL1Maximum

open scoped lp
namespace PrimeSquares

structure SourceLowData (N : ℕ) (Q : ℝ) where
  scale_lower : 2 ≤ N
  cutoff_lower : 2 ≤ Q
  working_radius : ℝ
  cutoff_le : Q ≤ working_radius
  index_limit : ℕ
  index_le : (index_limit : ℝ) ≤ working_radius
  cutoff_complete : ⌊Q⌋₊ ≤ index_limit
  conductor : ℕ
  conductor_pos : 0 < conductor
  character : DirichletCharacter ℂ conductor
  quadratic : character.IsQuadratic
  active : Bool
  beta : ℝ
  beta_le_one : beta ≤ 1
  exceptional_range : Q*(conductor : ℝ)/conductorMajorant conductor ≤ working_radius
  geometry : 2*working_radius^4 ≤ (N : ℝ)^2

noncomputable def SourceLowData.symbol {N : ℕ} {Q : ℝ} (D : SourceLowData N Q) : C(PrimeCircle, ℂ) := by
  letI : NeZero D.conductor := ⟨D.conductor_pos.ne'⟩
  exact circleLowModel (canonicalRationalCenters D.index_limit) N (by have h := D.scale_lower;omega)
    D.conductor Q (conductorMajorant D.conductor) (sourceInducedCharacter D.conductor D.character)
    (sourceExceptionalSelector D.conductor D.active) D.beta

theorem sourceLowData_symbol_eq {N : ℕ} {Q : ℝ} (D : SourceLowData N Q) :
    letI : NeZero D.conductor := ⟨D.conductor_pos.ne'⟩
    D.symbol=realCombinedLowModel N (by have h := D.scale_lower;omega) D.conductor D.character Q
      (by have h := D.cutoff_lower;linarith)
      (source_low_width_budget (by have h := D.cutoff_lower;linarith) D.cutoff_le D.geometry)
      D.beta D.index_limit D.active := by
  have : NeZero D.conductor := ⟨D.conductor_pos.ne'⟩
  exact truncatedSourceLow_identity (by have h := D.scale_lower;omega) D.conductor D.character D.active D.beta
    D.index_limit (by have h := D.cutoff_lower;linarith) D.cutoff_le D.exceptional_range D.index_le D.cutoff_complete D.geometry

theorem sourceLowData_L1_norm {N : ℕ} {Q : ℝ} (D : SourceLowData N Q) :
    ‖fourierL1Operator D.symbol‖ ≤ 2*realLowAmplitude N Q := by
  have : NeZero D.conductor := ⟨D.conductor_pos.ne'⟩
  rw [sourceLowData_symbol_eq]
  exact realCombinedLowModel_L1_norm D.scale_lower D.cutoff_lower _ D.conductor D.character
    D.quadratic D.beta_le_one D.index_limit D.active

theorem sourceLowFamily_countable_maximal {N₀ : ℕ} (hN₀ : 2 ≤ N₀) {Q : ℝ}
    (N : ℕ → ℕ) (D : ∀ j,SourceLowData (N j) Q) (hN : ∀ j,N₀ ≤ N j) (f : ℓ¹(ℤ, ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) ⊤,
      (∀ x : ℤ,g x=⨆ j : ℕ,‖integerMultiplier (D j).symbol
        (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x‖) ∧
      ‖g‖ ≤ 2*realLowAmplitude N₀ Q*‖f‖ := by
  let T (j : ℕ) := fourierL1Operator (D j).symbol
  have hT : ∀ j,‖T j‖ ≤ 2*realLowAmplitude N₀ Q := fun j =>
    (sourceLowData_L1_norm (D j)).trans (mul_le_mul_of_nonneg_left
      (realLowAmplitude_scale_mono (by omega) (hN j) (by have h := (D j).cutoff_lower;linarith)) (by norm_num))
  refine ⟨operatorL1Maximum T hT f,?_,operatorL1Maximum_norm T hT f⟩
  intro x
  change (⨆ j : ℕ,‖fourierL1Operator (D j).symbol f x‖)=_
  exact iSup_congr (fun j => congrArg norm (fourierL1Operator_all_l2_agreement (D j).symbol f x))

end PrimeSquares
