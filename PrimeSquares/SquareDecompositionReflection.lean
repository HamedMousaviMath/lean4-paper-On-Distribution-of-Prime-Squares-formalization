import PrimeSquares.SquareAverageReflection
import PrimeSquares.MaximalReflection
import PrimeSquares.TheoremOneOne

/-!
# Sign-independent interface to the external ordinary-square decomposition

The global analytic estimate remains a hypothesis. Its positive-sign version
implies the already used negative-sign version, and conversely, with exactly
the same constant. This removes reflection, but not globalization, from the
unformalized boundary. Theorem 1.1 can consume the positive-sign interface.
-/

open scoped lp

namespace PrimeSquares

def PositiveFullSquareDecompositionInput (C : ℝ) : Prop :=
  ∀ N : ℕ, 0 < N → ∀ j : ℕ, 2 ≤ (2 : ℝ)^j →
    OperatorHighLowBound (plusSquareAverageKernel N (fun _ => 1))
      ((N : ℝ)^2) ((2 : ℝ)^j) 1 (1/2) 2 1 C

theorem fullSquareDecompositionInput_sign_iff (C : ℝ) :
    PositiveFullSquareDecompositionInput C ↔ FullSquareDecompositionInput C := by
  constructor
  · intro H N hN j hj
    have h := H N hN j hj
    rw [← weightedSquareAverageKernel_reflection] at h
    exact (operatorHighLowBound_reflect_iff _ _ _ _ _ _ _ _).1 h
  · intro H N hN j hj
    rw [← weightedSquareAverageKernel_reflection]
    exact operatorHighLowBound_reflect (H N hN j hj)

theorem fullSquare_decomposition_from_plus {C : ℝ}
    (H : PositiveFullSquareDecompositionInput C) : FullSquareDecompositionInput C :=
  (fullSquareDecompositionInput_sign_iff C).1 H

theorem plusSquare_decomposition_from_minus {C : ℝ}
    (H : FullSquareDecompositionInput C) : PositiveFullSquareDecompositionInput C :=
  (fullSquareDecompositionInput_sign_iff C).2 H

theorem positiveFullSquare_decomposition_annular {C : ℝ} (hC : 0 ≤ C)
    (H : PositiveFullSquareDecompositionInput C) (M : ℕ) (hM : 0 < M) (j : ℕ)
    (hj : 2 ≤ (2 : ℝ)^j) :
    OperatorHighLowBound (annularWeightedSquareAverageKernel (2*M) (fun _ => 1))
      (((2*M : ℕ) : ℝ)^2) ((2 : ℝ)^j) 1 (1/2) 2 1 (3*C) :=
  fullSquare_decomposition_annular_two_mul hC (fullSquare_decomposition_from_plus H) M hM j hj

theorem positiveFullSquare_decomposition_annular_plus {C : ℝ} (hC : 0 ≤ C)
    (H : PositiveFullSquareDecompositionInput C) (M : ℕ) (hM : 0 < M) (j : ℕ)
    (hj : 2 ≤ (2 : ℝ)^j) :
    OperatorHighLowBound (annularPlusSquareAverageKernel (2*M) (fun _ => 1))
      (((2*M : ℕ) : ℝ)^2) ((2 : ℝ)^j) 1 (1/2) 2 1 (3*C) := by
  rw [← annularWeightedSquareAverageKernel_reflection]
  exact operatorHighLowBound_reflect (positiveFullSquare_decomposition_annular hC H M hM j hj)

theorem primeSquareSourceInterval_reflection (N : ℕ) :
    reflectedFinset (primeSquareSourceInterval N) =
      Finset.Icc (-2*(N : ℤ)^2) ((N : ℤ)^2) := by
  simp [primeSquareSourceInterval, neg_mul]

theorem primeSquareAverageValue_reflection (N : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    reflectSequence (primeSquareAverageValue N (reflectSequence f)) x =
      Complex.ofReal ((N : ℝ)⁻¹) * ∑ n ∈ Finset.Ioc 0 N,
        (ArithmeticFunction.vonMangoldt n : ℂ) * f (x + (n : ℤ)^2) := by
  simp only [reflectSequence_apply, primeSquareAverageValue]
  simp only [neg_sub, sub_neg_eq_add, add_comm]

/-- Both already proved conclusions of Theorem 1.1, accepting the global
ordinary-square hypothesis in its literal plus-square convention. -/
theorem theorem_1_1_from_positive_square_input (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {CS : ℝ} (hCS : 1 ≤ CS)
    (HS : PositiveFullSquareDecompositionInput CS) :
    (∀ cstar : ℝ, 4*Real.sqrt 3/9 < cstar → ∃ A : ℝ, 0 < A ∧
      ∀ N : ℕ, 0 < N → ∀ F G : Finset ℤ,
        F ⊆ primeSquareSourceInterval N → G ⊆ primeSquareSourceInterval N →
        ‖restrictedKernelPairing (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F G‖/
          ((primeSquareSourceInterval N).card : ℝ) ≤
        A*(finiteSetDensity ((primeSquareSourceInterval N).card : ℝ) F G)^(2/3 : ℝ)*
          paperPhi cstar (1/2) (finiteSetDensity ((primeSquareSourceInterval N).card : ℝ) F G)) ∧
    (∀ (P Q : ENNReal), ∀ [Fact (1 ≤ P)] [Fact (1 ≤ Q)],
      ∀ (hP2 : P ≤ 2) (h2Q : 2 ≤ Q) (hQ : Q ≠ ⊤),
        Q.toReal = holderConjugate P.toReal → ∀ hp : 3/2 < P.toReal,
        ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 0 < N → ∀ f : lp (fun _ : ℤ => ℂ) P,
          ‖primeSquareImprovingOperator (by linarith : 0 < P.toReal) (hP2.trans h2Q) hQ N f‖/
            ((primeSquareSourceInterval N).card : ℝ)^(1/Q.toReal) ≤
          A*‖f‖/((primeSquareSourceInterval N).card : ℝ)^(1/P.toReal)) :=
  theorem_1_1 HP D hCS (fullSquare_decomposition_from_plus HS)

end PrimeSquares
