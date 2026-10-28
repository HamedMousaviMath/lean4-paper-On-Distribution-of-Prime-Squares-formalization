import PrimeSquares.GoldbachMajorCompletionComplete

set_option autoImplicit false
open Finset MeasureTheory
open scoped SchwartzMap ENNReal
namespace PrimeSquares

noncomputable def goldbachCutoffRemainder (ψ : 𝓢(ℝ,ℝ)) (N ℓ k a : ℕ)
    (R U W : ℝ) (n : ℕ) : ℂ :=
  ((goldbachCutoffPrimePairs N ℓ k a n U W).card:ℂ)-
    goldbachArithmeticFactor R k (ℓ:ℤ) (a:ℤ) n/((ℓ:ℂ)*(k.totient:ℂ))*
      goldbachSingularIntegral ψ N ℓ R (n:ℝ) U W

noncomputable def goldbachFullRemainder (ψ : 𝓢(ℝ,ℝ)) (N ℓ k a : ℕ)
    (R : ℝ) (n : ℕ) : ℂ :=
  ((goldbachProgressionPairs ℓ k a n).card:ℂ)-
    goldbachArithmeticFactor R k (ℓ:ℤ) (a:ℤ) n/((ℓ:ℂ)*(k.totient:ℂ))*
      goldbachSingularIntegral ψ N ℓ R (n:ℝ) (N:ℝ) ((N:ℝ)^2)

theorem goldbach_circle_method_cutoff_complete
    (HSW : RawPrimeSiegelWalfiszInput) (HBV : RawPrimeBombieriVinogradovInput)
    (D : UniformRenGhoshInputs) (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x| →ψ x=0) {A δ : ℝ} (hA : 0<A) (hδ : 0<δ) :
    ∃ B₀ C K : ℝ,0≤B₀ ∧ 0<C ∧ 0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      ∀ B L : ℝ,B₀≤B →L<(N:ℝ)^(2-δ) →∀ V : ℕ→ℝ,
      (∀ ℓ : ℕ,0<ℓ →(ℓ:ℝ)<L →V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) →
      ∀ a : ℕ×ℕ→ℕ,(∀ i∈goldbachCoefficientIndices L V,(a i).Coprime i.2) →
      ∀ d : ℕ×ℕ→ℂ,(∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1) →
      ∀ U W : ℝ,2≤U →U≤N →2≤W →
      (∑ n∈range (N^2),‖∑ i∈goldbachCoefficientIndices L V,d i*
        goldbachCutoffRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) U W n‖^2)≤
        K*(N:ℝ)^4*(Real.log N)^(-A) := by
  classical
  obtain ⟨CC,hCC,hCompletion⟩ := goldbach_major_completion_complete ψ hψ hsψ hA hδ
  obtain ⟨CM,hCM,hMinor⟩ := goldbach_hybrid_minor_complete D hA
  let C := max CC CM
  have hC : 0<C := lt_of_lt_of_le hCC (le_max_left _ _)
  obtain ⟨KC,hKC,NC,hNC,hComplete⟩ := hCompletion C (le_max_left _ _)
  obtain ⟨NM,hNM,hMinorBound⟩ := hMinor C (le_max_right _ _)
  obtain ⟨B₀,KR,hB₀,hKR,NR,hNR,hReplacement⟩ := goldbach_major_approximation_complete HSW HBV hA hC.le hδ
  obtain ⟨NX,hNX,hRanges⟩ := goldbach_source_ranges_eventual hδ
  let K := 3*(goldbachHybridMinorConstant D+KR+KC)
  have hK : 0<K := by
    have := goldbachHybridMinorConstant_pos D
    dsimp [K]
    positivity
  refine ⟨B₀,C,K,hB₀,hC,hK,max NC (max NM (max NR NX)),hNC.trans (le_max_left _ _),?_⟩
  intro N hN B L hB hL V hV a ha d hd U W hU hUN hW
  have hNNc := (le_max_left NC (max NM (max NR NX))).trans hN
  have hNNm := (le_max_left NM (max NR NX)).trans ((le_max_right NC _).trans hN)
  have hNNr := (le_max_left NR NX).trans ((le_max_right NM _).trans ((le_max_right NC _).trans hN))
  have hNNx := (le_max_right NR NX).trans ((le_max_right NM _).trans ((le_max_right NC _).trans hN))
  have hBpos : 0≤B := hB₀.trans hB
  let I := goldbachCoefficientIndices L V
  let R := (Real.log N)^C
  let P : PrimeCircle→ℂ := goldbachPrimeSquarePolynomial U
  let F : PrimeCircle→ℂ := goldbachWeightedProgressionPolynomial N I a d W
  let Q := goldbachSquareMajorModel N R U
  let G := goldbachWeightedProgressionMajorModel N I a d R W
  let E₁ := fun n : ℕ=>∫ θ : PrimeCircle in GoldbachMinorArcs N R,
    P θ*F θ*fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle
  let E₂ := fun n : ℕ=>∑ i∈I,d i*(∫ θ : PrimeCircle in GoldbachMajorArcs N R,
    (goldbachPrimeSquarePolynomial U θ*goldbachProgressionPolynomial N i.1 i.2 (a i) W θ-
      Q θ*goldbachProgressionMajorModel N i.1 i.2 (a i) R W θ)*fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle)
  let E₃ := fun n : ℕ=>∑ i∈I,d i*((∫ θ : PrimeCircle in GoldbachMajorArcs N R,
      Q θ*goldbachProgressionMajorModel N i.1 i.2 (a i) R W θ*fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle)-
    goldbachArithmeticFactor R i.2 (i.1:ℤ) (a i:ℤ) n/((i.1:ℂ)*(i.2.totient:ℂ))*
      goldbachSingularIntegral ψ N i.1 R (n:ℝ) U W)
  have hI : ∀ i∈I,0 < i.1 := fun i hi=>((mem_goldbachCoefficientIndices L V i.1 i.2).mp hi).1
  have hX : ∀ i∈I,2≤(N:ℝ)^2/i.1 := (hRanges N hNNx L hL).2 V
  have hE₁ : (∑ n∈range (N^2),‖E₁ n‖^2)≤goldbachHybridMinorConstant D*(N:ℝ)^4*(Real.log N)^(-A) :=
    hMinorBound N hNNm L B δ V hBpos hδ hL hV a d U W hd (by linarith) hUN
  have hE₂ : (∑ n∈range (N^2),‖E₂ n‖^2)≤KR*(N:ℝ)^4*(Real.log N)^(-A) :=
    hReplacement N hNNr B L hB hL V hV a ha d hd U W hU hUN hW
  have hE₃ : (∑ n∈range (N^2),‖E₃ n‖^2)≤KC*(N:ℝ)^4*(Real.log N)^(-A) :=
    hComplete N hNNc L B V hBpos hL hV a ha d hd U W hU hUN hW
  have he (n : ℕ) : (∑ i∈I,d i*goldbachCutoffRemainder ψ N i.1 i.2 (a i) R U W n)=E₁ n+E₂ n+E₃ n := by
    have hP : MemLp P ∞ AddCircle.haarAddCircle := ContinuousMap.memLp AddCircle.haarAddCircle ℂ _
    have hF : MemLp F 1 AddCircle.haarAddCircle := ContinuousMap.memLp AddCircle.haarAddCircle ℂ _
    have hQ : MemLp Q ∞ AddCircle.haarAddCircle := goldbachSquareMajorModel_memLp N R hU ∞
    have hG : MemLp G 1 AddCircle.haarAddCircle := goldbachWeightedProgressionMajorModel_memLp N I a d R hW hI hX 1
    have hφ : MemLp ((fourier (-(n:ℤ))) : PrimeCircle→ℂ) ∞ AddCircle.haarAddCircle :=
      ContinuousMap.memLp AddCircle.haarAddCircle ℂ _
    have hPF : MemLp (fun θ : PrimeCircle=>P θ*F θ*fourier (-(n:ℤ)) θ) 1 AddCircle.haarAddCircle := (hP.mul (r:=1) hF).mul hφ
    have hQG : MemLp (fun θ : PrimeCircle=>Q θ*G θ*fourier (-(n:ℤ)) θ) 1 AddCircle.haarAddCircle := (hQ.mul (r:=1) hG).mul hφ
    have hiPF := hPF.integrable (by norm_num : (1:ℝ≥0∞)≤1)
    have hiQG := hQG.integrable (by norm_num : (1:ℝ≥0∞)≤1)
    have hSplit := integral_add_compl (goldbachMinorArcs_measurable N R) hiPF
    change E₁ n+(∫ θ : PrimeCircle in GoldbachMajorArcs N R,P θ*F θ*fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle)=
      (∫ θ : PrimeCircle,P θ*F θ*fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle) at hSplit
    have hSecond : E₂ n=(∫ θ : PrimeCircle in GoldbachMajorArcs N R,P θ*F θ*fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle)-
        goldbachMajorModelCoefficient N I a d R U W n := by
      change (∑ i∈I,d i*(∫ θ : PrimeCircle in GoldbachMajorArcs N R,
        (goldbachPrimeSquarePolynomial U θ*goldbachProgressionPolynomial N i.1 i.2 (a i) W θ-
          goldbachSquareMajorModel N R U θ*goldbachProgressionMajorModel N i.1 i.2 (a i) R W θ)*fourier (-(n:ℤ)) θ
            ∂AddCircle.haarAddCircle))=_
      rw [goldbach_major_weighted_coefficient_identity N n I a d R hU hW hI hX]
      change (∫ θ : PrimeCircle in GoldbachMajorArcs N R,(P θ*F θ-Q θ*G θ)*fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle)=_
      simp only [sub_mul]
      rw [integral_sub hiPF.restrict hiQG.restrict]
      rfl
    have hThird : E₃ n=goldbachMajorModelCoefficient N I a d R U W n-goldbachCompletedMainTerm ψ N I a d R U W n := by
      dsimp only [E₃,Q]
      simp only [mul_sub,sum_sub_distrib]
      rw [goldbach_model_weighted_coefficient N n I a d R hU hW hI hX]
      congr 1
      unfold goldbachCompletedMainTerm
      apply sum_congr rfl
      intro i _
      rw [Int.cast_natCast]
      ring
    have hCount : (∑ i∈I,d i*goldbachCutoffRemainder ψ N i.1 i.2 (a i) R U W n)=
        (∫ θ : PrimeCircle,P θ*F θ*fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle)-goldbachCompletedMainTerm ψ N I a d R U W n := by
      dsimp only [goldbachCutoffRemainder]
      simp only [mul_sub,sum_sub_distrib]
      rw [goldbach_weighted_fourier_inversion]
      congr 1
      unfold goldbachCompletedMainTerm
      apply sum_congr rfl
      intro i _
      rw [Int.cast_natCast]
      ring
    rw [hCount,hSecond,hThird,←hSplit]
    ring
  calc
    _≤∑ n∈range (N^2),3*(‖E₁ n‖^2+‖E₂ n‖^2+‖E₃ n‖^2) :=
      sum_le_sum (fun n _=>by rw [he];exact norm_three_sum_square _ _ _)
    _=3*((∑ n∈range (N^2),‖E₁ n‖^2)+(∑ n∈range (N^2),‖E₂ n‖^2)+(∑ n∈range (N^2),‖E₃ n‖^2)) := by
      rw [←mul_sum,sum_add_distrib,sum_add_distrib]
    _≤3*(goldbachHybridMinorConstant D*(N:ℝ)^4*(Real.log N)^(-A)+KR*(N:ℝ)^4*(Real.log N)^(-A)+
        KC*(N:ℝ)^4*(Real.log N)^(-A)) := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hE₁ hE₂) hE₃) (by norm_num)
    _=_ := by dsimp [K];ring

theorem goldbach_circle_method_complete
    (HSW : RawPrimeSiegelWalfiszInput) (HBV : RawPrimeBombieriVinogradovInput)
    (D : UniformRenGhoshInputs) (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x| →ψ x=0) {A δ : ℝ} (hA : 0<A) (hδ : 0<δ) :
    ∃ B₀ C K : ℝ,0≤B₀ ∧ 0<C ∧ 0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      ∀ B L : ℝ,B₀≤B →L<(N:ℝ)^(2-δ) →∀ V : ℕ→ℝ,
      (∀ ℓ : ℕ,0<ℓ →(ℓ:ℝ)<L →V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) →
      ∀ a : ℕ×ℕ→ℕ,(∀ i∈goldbachCoefficientIndices L V,(a i).Coprime i.2) →
      ∀ d : ℕ×ℕ→ℂ,(∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1) →
      (∑ n∈range (N^2),‖∑ i∈goldbachCoefficientIndices L V,d i*
        goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n‖^2)≤
        K*(N:ℝ)^4*(Real.log N)^(-A) := by
  obtain ⟨B₀,C,K,hB₀,hC,hK,N₀,hN₀,hCutoff⟩ := goldbach_circle_method_cutoff_complete HSW HBV D ψ hψ hsψ hA hδ
  refine ⟨B₀,C,K,hB₀,hC,hK,N₀,hN₀,?_⟩
  intro N hN B L hB hL V hV a ha d hd
  have hN2 : (2:ℝ)≤N := by exact_mod_cast (show 2≤N by omega)
  have hNpow : (2:ℝ)≤(N:ℝ)^2 := by nlinarith
  have h := hCutoff N hN B L hB hL V hV a ha d hd N ((N:ℝ)^2) hN2 le_rfl hNpow
  have he (n : ℕ) (hn : n∈range (N^2)) : (∑ i∈goldbachCoefficientIndices L V,d i*
      goldbachCutoffRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) (N:ℝ) ((N:ℝ)^2) n)=
      ∑ i∈goldbachCoefficientIndices L V,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n := by
    apply sum_congr rfl
    intro i hi
    have hℓ := ((mem_goldbachCoefficientIndices L V i.1 i.2).mp hi).1
    unfold goldbachCutoffRemainder goldbachFullRemainder
    rw [goldbach_full_cutoffs_redundant hℓ (mem_range.mp hn)]
  calc
    _=(∑ n∈range (N^2),‖∑ i∈goldbachCoefficientIndices L V,d i*
        goldbachCutoffRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) (N:ℝ) ((N:ℝ)^2) n‖^2) := by
      apply sum_congr rfl
      intro n hn
      rw [he n hn]
    _≤_ := h

end PrimeSquares
