import PrimeSquares.DenominatorLowL1Bound
import PrimeSquares.AllInputFourierConvolution
import PrimeSquares.UniformL1Maximum

open scoped lp
namespace PrimeSquares

structure LowSymbolData (N Q : ℕ) where
  scale_lower : 2 ≤ N
  cutoff_lower : 2 ≤ Q
  budget : 2*(Q : ℝ) ≤ (N : ℝ)^2
  conductor : ℕ
  conductor_pos : 0 < conductor
  character : DirichletCharacter ℂ conductor
  quadratic : character.IsQuadratic
  beta : ℝ
  beta_le_one : beta ≤ 1
  denominators : Finset ℕ
  denominators_subset : denominators ⊆ Finset.Icc 1 Q
  width : ∀ d ∈ denominators,conductorMajorant conductor*(d : ℝ) ≤ Q

noncomputable def LowSymbolData.symbol {N Q : ℕ} (D : LowSymbolData N Q) : C(PrimeCircle, ℂ) := by
  letI : NeZero D.conductor := ⟨D.conductor_pos.ne'⟩
  exact denominatorCircleLow N Q (by have h := D.scale_lower;omega) (by have h := D.cutoff_lower;omega)
    D.budget D.conductor D.character D.beta D.denominators

theorem lowSymbolData_L1_norm {N Q : ℕ} (D : LowSymbolData N Q) :
    ‖fourierL1Operator D.symbol‖ ≤ physicalLowAmplitude N Q := by
  have : NeZero D.conductor := ⟨D.conductor_pos.ne'⟩
  exact denominatorCircleLow_L1_norm D.scale_lower D.cutoff_lower D.budget D.conductor D.character
    D.quadratic D.beta_le_one D.denominators D.denominators_subset D.width

theorem lowSymbolFamily_countable_maximal {N₀ Q : ℕ} (hN₀ : 2 ≤ N₀)
    (N : ℕ → ℕ) (D : ∀ j,LowSymbolData (N j) Q) (hN : ∀ j,N₀ ≤ N j) (f : ℓ¹(ℤ, ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) ⊤,
      (∀ x : ℤ,g x=⨆ j : ℕ,‖integerMultiplier (D j).symbol
        (lpInclusion (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num) f) x‖) ∧
      ‖g‖ ≤ physicalLowAmplitude N₀ Q*‖f‖ := by
  let T (j : ℕ) := fourierL1Operator (D j).symbol
  have hT : ∀ j,‖T j‖ ≤ physicalLowAmplitude N₀ Q := fun j =>
    (lowSymbolData_L1_norm (D j)).trans (physicalLowAmplitude_mono (by omega) (hN j) (by have h := (D j).cutoff_lower;omega))
  refine ⟨operatorL1Maximum T hT f,?_,operatorL1Maximum_norm T hT f⟩
  intro x
  change (⨆ j : ℕ,‖fourierL1Operator (D j).symbol f x‖)=_
  exact iSup_congr (fun j => congrArg norm (fourierL1Operator_all_l2_agreement (D j).symbol f x))

end PrimeSquares
