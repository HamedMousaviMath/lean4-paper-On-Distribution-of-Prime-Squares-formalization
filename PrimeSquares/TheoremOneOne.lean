import PrimeSquares.PrimeSquareActualStrongOperator

open scoped lp
namespace PrimeSquares

theorem normalized_lp_norm_as_sum {P : ENNReal} [Fact (1 ≤ P)]
    (hp : 0 < P.toReal) {S : ℝ} (hS : 0 < S) (f : lp (fun _ : ℤ => ℂ) P) :
    (S⁻¹*∑' x : ℤ,‖f x‖^P.toReal)^(1/P.toReal)=‖f‖/S^(1/P.toReal) := by
  rw [Real.mul_rpow (inv_nonneg.mpr hS.le) (tsum_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)),
    Real.inv_rpow hS.le,←lp.norm_eq_tsum_rpow hp]
  ring

/-- The exact sum-of-powers form of the second conclusion of Theorem 1.1.
The genuine prime-square operator is identified pointwise by
primeSquareImprovingOperator_apply. No support restriction is required. -/
theorem theorem_1_1_strong_sum (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {CS : ℝ} (hCS : 1 ≤ CS)
    (HS : FullSquareDecompositionInput CS)
    {P Q : ENNReal} [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    (hP2 : P ≤ 2) (h2Q : 2 ≤ Q) (hQ : Q ≠ ⊤)
    (hconj : Q.toReal=holderConjugate P.toReal) (hp : 3/2 < P.toReal) :
    ∃ A : ℝ,0 < A ∧ ∀ N : ℕ,0 < N → ∀ f : lp (fun _ : ℤ => ℂ) P,
      (((primeSquareSourceInterval N).card : ℝ)⁻¹*∑' x : ℤ,
        ‖primeSquareImprovingOperator (by linarith : 0 < P.toReal) (hP2.trans h2Q) hQ N f x‖^Q.toReal)^(1/Q.toReal) ≤
      A*(((primeSquareSourceInterval N).card : ℝ)⁻¹*∑' x : ℤ,‖f x‖^P.toReal)^(1/P.toReal) := by
  obtain ⟨A,hA,h⟩ := theorem_1_1_strong HP D hCS HS hP2 h2Q hQ hconj hp
  refine ⟨A,hA,?_⟩
  intro N hN f
  have hI : (0 : ℝ) < (primeSquareSourceInterval N).card :=
    (by positivity : (0 : ℝ) < (N : ℝ)^2).trans_le (primeSquareSourceInterval_card_bounds hN).1
  have hp0 : 0 < P.toReal := by linarith
  have hq0 : 0 < Q.toReal := by rw [hconj];exact holderConjugate_pos (by linarith)
  rw [normalized_lp_norm_as_sum hq0 hI,normalized_lp_norm_as_sum hp0 hI]
  simpa only [mul_div_assoc] using h N hN f


noncomputable def primeSquareAverageValue (N : ℕ) (f : ℤ → ℂ) (x : ℤ) : ℂ :=
  Complex.ofReal ((N : ℝ)⁻¹)*∑ n ∈ Finset.Ioc 0 N,
    (ArithmeticFunction.vonMangoldt n : ℂ)*f (x-(n : ℤ)^2)

/-- Real-exponent form matching the manuscript literally, including actual
membership of the output in l^{p'}; hence no conclusion rests on a totalized
infinite sum outside its summability domain. This is stronger than the source
support-restricted assertion. -/
theorem theorem_1_1_strong_real (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {CS : ℝ} (hCS : 1 ≤ CS)
    (HS : FullSquareDecompositionInput CS) (p : ℝ) (hp : 3/2 < p) (hp2 : p ≤ 2) :
    ∃ A : ℝ,0 < A ∧ ∀ N : ℕ,0 < N → ∀ f : ℤ → ℂ,Memℓp f (ENNReal.ofReal p) →
      Memℓp (primeSquareAverageValue N f) (ENNReal.ofReal (holderConjugate p)) ∧
      (((primeSquareSourceInterval N).card : ℝ)⁻¹*∑' x : ℤ,
        ‖primeSquareAverageValue N f x‖^(holderConjugate p))^(1/holderConjugate p) ≤
      A*(((primeSquareSourceInterval N).card : ℝ)⁻¹*∑' x : ℤ,‖f x‖^p)^(1/p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  have hq0 := holderConjugate_pos hp1
  have h2q : 2 ≤ holderConjugate p := by
    dsimp [holderConjugate]
    exact (le_div_iff₀ (by linarith : 0 < p-1)).mpr (by linarith)
  let P := ENNReal.ofReal p
  let Q := ENNReal.ofReal (holderConjugate p)
  have hP1 : 1 ≤ P := by
    simpa only [P,ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  have hQ1 : 1 ≤ Q := by
    simpa only [Q,ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ holderConjugate p)
  have : Fact (1 ≤ P) := ⟨hP1⟩
  have : Fact (1 ≤ Q) := ⟨hQ1⟩
  have hP2 : P ≤ 2 := by simpa only [P,ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp2
  have h2Q : 2 ≤ Q := by simpa only [Q,ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal h2q
  have hQ : Q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hPreal : P.toReal=p := ENNReal.toReal_ofReal hp0.le
  have hQreal : Q.toReal=holderConjugate p := ENNReal.toReal_ofReal hq0.le
  have hconj : Q.toReal=holderConjugate P.toReal := by rw [hPreal,hQreal]
  have hpp : 3/2 < P.toReal := by rw [hPreal];exact hp
  obtain ⟨A,hA,h⟩ := theorem_1_1_strong_sum HP D hCS HS hP2 h2Q hQ hconj hpp
  refine ⟨A,hA,?_⟩
  intro N hN f hf
  let u : lp (fun _ : ℤ => ℂ) P := ⟨f,hf⟩
  let v := primeSquareImprovingOperator (by linarith : 0 < P.toReal) (hP2.trans h2Q) hQ N u
  have he : (v : ℤ → ℂ)=primeSquareAverageValue N f := by
    funext x
    exact primeSquareImprovingOperator_apply _ _ _ N u x
  refine ⟨?_,?_⟩
  · rw [←he]
    exact v.property
  · have hb := h N hN u
    simpa only [hPreal,hQreal,←he] using hb

/-- Both source conclusions, with constants uniform before the arithmetic
cutoff and the input functions/sets. PNT, the raw compatible prime estimates,
and the independent ordinary-square theorem remain explicit hypotheses.
There is no axiom or assumed prime-square decomposition in this statement. -/
theorem theorem_1_1 (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {CS : ℝ} (hCS : 1 ≤ CS)
    (HS : FullSquareDecompositionInput CS) :
    (∀ cstar : ℝ,4*Real.sqrt 3/9 < cstar → ∃ A : ℝ,0 < A ∧
      ∀ N : ℕ,0 < N → ∀ F G : Finset ℤ,
        F ⊆ primeSquareSourceInterval N → G ⊆ primeSquareSourceInterval N →
        ‖restrictedKernelPairing (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F G‖/
          ((primeSquareSourceInterval N).card : ℝ) ≤
        A*(finiteSetDensity ((primeSquareSourceInterval N).card : ℝ) F G)^(2/3 : ℝ)*
          paperPhi cstar (1/2) (finiteSetDensity ((primeSquareSourceInterval N).card : ℝ) F G)) ∧
    (∀ (P Q : ENNReal),∀ [Fact (1 ≤ P)] [Fact (1 ≤ Q)],
      ∀ (hP2 : P ≤ 2) (h2Q : 2 ≤ Q) (hQ : Q ≠ ⊤),
        Q.toReal=holderConjugate P.toReal → ∀ hp : 3/2 < P.toReal,
        ∃ A : ℝ,0 < A ∧ ∀ N : ℕ,0 < N → ∀ f : lp (fun _ : ℤ => ℂ) P,
          ‖primeSquareImprovingOperator (by linarith : 0 < P.toReal) (hP2.trans h2Q) hQ N f‖/
            ((primeSquareSourceInterval N).card : ℝ)^(1/Q.toReal) ≤
          A*‖f‖/((primeSquareSourceInterval N).card : ℝ)^(1/P.toReal)) := by
  constructor
  · intro cstar hstar
    exact theorem_1_1_restricted HP D hCS HS hstar
  · intro P Q instP instQ hP2 h2Q hQ hconj hp
    exact theorem_1_1_strong HP D hCS HS hP2 h2Q hQ hconj hp

end PrimeSquares
