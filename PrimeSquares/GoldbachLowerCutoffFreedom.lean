import PrimeSquares.GoldbachLowerSieveApplication

set_option autoImplicit false
open Finset Filter MeasureTheory
open scoped SchwartzMap ENNReal
namespace PrimeSquares

theorem goldbach_circle_method_cutoff_above (Cmin : ℝ)
    (HSW : RawPrimeSiegelWalfiszInput) (HBV : RawPrimeBombieriVinogradovInput)
    (D : UniformRenGhoshInputs) (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x| →ψ x=0) {A δ : ℝ} (hA : 0<A) (hδ : 0<δ) :
    ∃ B₀ C K : ℝ,Cmin≤C ∧ 0≤B₀ ∧ 0<C ∧ 0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
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
  let C := max (max CC CM) Cmin
  have hCC' : CC≤C := (le_max_left CC CM).trans (le_max_left _ _)
  have hCM' : CM≤C := (le_max_right CC CM).trans (le_max_left _ _)
  have hC : 0<C := lt_of_lt_of_le hCC hCC'
  obtain ⟨KC,hKC,NC,hNC,hComplete⟩ := hCompletion C hCC'
  obtain ⟨NM,hNM,hMinorBound⟩ := hMinor C hCM'
  obtain ⟨B₀,KR,hB₀,hKR,NR,hNR,hReplacement⟩ := goldbach_major_approximation_complete HSW HBV hA hC.le hδ
  obtain ⟨NX,hNX,hRanges⟩ := goldbach_source_ranges_eventual hδ
  let K := 3*(goldbachHybridMinorConstant D+KR+KC)
  have hK : 0<K := by
    have := goldbachHybridMinorConstant_pos D
    dsimp [K]
    positivity
  refine ⟨B₀,C,K,(le_max_right _ _),hB₀,hC,hK,max NC (max NM (max NR NX)),hNC.trans (le_max_left _ _),?_⟩
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

theorem goldbach_circle_method_above (Cmin : ℝ)
    (HSW : RawPrimeSiegelWalfiszInput) (HBV : RawPrimeBombieriVinogradovInput)
    (D : UniformRenGhoshInputs) (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x| →ψ x=0) {A δ : ℝ} (hA : 0<A) (hδ : 0<δ) :
    ∃ B₀ C K : ℝ,Cmin≤C ∧ 0≤B₀ ∧ 0<C ∧ 0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      ∀ B L : ℝ,B₀≤B →L<(N:ℝ)^(2-δ) →∀ V : ℕ→ℝ,
      (∀ ℓ : ℕ,0<ℓ →(ℓ:ℝ)<L →V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) →
      ∀ a : ℕ×ℕ→ℕ,(∀ i∈goldbachCoefficientIndices L V,(a i).Coprime i.2) →
      ∀ d : ℕ×ℕ→ℂ,(∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1) →
      (∑ n∈range (N^2),‖∑ i∈goldbachCoefficientIndices L V,d i*
        goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n‖^2)≤
        K*(N:ℝ)^4*(Real.log N)^(-A) := by
  obtain ⟨B₀,C,K,hCmin,hB₀,hC,hK,N₀,hN₀,hCutoff⟩ := goldbach_circle_method_cutoff_above Cmin HSW HBV D ψ hψ hsψ hA hδ
  refine ⟨B₀,C,K,hCmin,hB₀,hC,hK,N₀,hN₀,?_⟩
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


theorem goldbach_sieve_remainders_selected_above (Cmin : ℝ)
    (HSW : RawPrimeSiegelWalfiszInput) (HBV : RawPrimeBombieriVinogradovInput)
    (D : UniformRenGhoshInputs) (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x| →ψ x=0) {A δ : ℝ} (hA : 0<A) (hδ : 0<δ) :
    ∃ B₀ C K : ℝ,Cmin≤C ∧ 0≤B₀ ∧ 0<C ∧ 0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      ∀ B L : ℝ,B₀≤B →L<(N:ℝ)^(2-δ) →∀ V : ℕ→ℝ,
      (∀ ℓ : ℕ,0<ℓ →(ℓ:ℝ)<L →V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) →
      ∀ I : Finset (ℕ×ℕ),I⊆goldbachCoefficientIndices L V →
      ∀ a : ℕ×ℕ→ℕ,(∀ i∈I,(a i).Coprime i.2) →
      ∀ d : ℕ×ℕ→ℂ,(∀ i∈I,‖d i‖≤1) →
      (∑ n∈range (N^2),‖∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n‖^2)≤
        K*(N:ℝ)^4*(Real.log N)^(-A) ∧
      (∑ n∈range (N^2),‖∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) (n-1)‖^2)≤
        (2*K)*(N:ℝ)^4*(Real.log N)^(-A) ∧
      ∀ T : Finset ℕ,(∀ n∈T,0<n ∧ n<N^2) →
        (∑ n∈T,‖∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) (n-1)‖^2)≤
          K*(N:ℝ)^4*(Real.log N)^(-A) := by
  classical
  obtain ⟨B₀,C,K,hCmin,hB₀,hC,hK,N₀,hN₀,hCircle⟩ := goldbach_circle_method_above Cmin HSW HBV D ψ hψ hsψ hA hδ
  refine ⟨B₀,C,K,hCmin,hB₀,hC,hK,N₀,hN₀,?_⟩
  intro N hN B L hB hL V hV I hI a ha d hd
  let a' := fun i : ℕ×ℕ=>if i∈I then a i else 1
  let d' := fun i : ℕ×ℕ=>if i∈I then d i else 0
  have ha' : ∀ i∈goldbachCoefficientIndices L V,(a' i).Coprime i.2 := by
    intro i _
    by_cases hi : i∈I
    · simpa only [a',ite_eq_left hi] using ha i hi
    · simp [a',hi]
  have hd' : ∀ i∈goldbachCoefficientIndices L V,‖d' i‖≤1 := by
    intro i _
    by_cases hi : i∈I
    · simpa only [d',ite_eq_left hi] using hd i hi
    · simp only [d',ite_eq_right hi,norm_zero,zero_le_one]
  have he (n : ℕ) : (∑ i∈goldbachCoefficientIndices L V,d' i*
      goldbachFullRemainder ψ N i.1 i.2 (a' i) ((Real.log N)^C) n)=
      ∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n := by
    calc
      _=∑ i∈I,d' i*goldbachFullRemainder ψ N i.1 i.2 (a' i) ((Real.log N)^C) n := by
        symm
        apply sum_subset hI
        intro i _ hi
        simp only [d',ite_eq_right hi,zero_mul]
      _=_ := by
        apply sum_congr rfl
        intro i hi
        simp only [a',d',ite_eq_left hi]
  have hFull := hCircle N hN B L hB hL V hV a' ha' d' hd'
  have hSelected : (∑ n∈range (N^2),‖∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n‖^2)≤
      K*(N:ℝ)^4*(Real.log N)^(-A) := by simpa only [he] using hFull
  refine ⟨hSelected,?_,?_⟩
  · calc
      _≤2*(∑ n∈range (N^2),‖∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n‖^2) :=
        goldbach_pred_full_square_sum_bound N _
      _≤2*(K*(N:ℝ)^4*(Real.log N)^(-A)) := mul_le_mul_of_nonneg_left hSelected (by norm_num)
      _=_ := by ring
  intro T hT
  exact (goldbach_pred_square_sum_bound N T hT
    (fun n=>∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n)).trans hSelected


theorem goldbach_lower_remainder_mean_square_above (Cmin : ℝ)
    (HSW : RawPrimeSiegelWalfiszInput) (HBV : RawPrimeBombieriVinogradovInput)
    (Hminor : UniformRenGhoshInputs) (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x|→ψ x=0) {A : ℝ} (hA : 0<A) :
    ∃ B₀ C K : ℝ,Cmin≤C ∧ 0≤B₀ ∧ 0<C ∧ 0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧
      ∀ N : ℕ,N₀≤N→∀ B : ℝ,B₀≤B→∀ c : ℕ→ℝ,(∀ d : ℕ,|c d|≤1)→
        (∑ n∈range (N^2),(goldbachLowerRemainderSum ψ N B ((Real.log N)^C) c n)^2)≤
          K*(N:ℝ)^4*(Real.log N)^(-A) := by
  classical
  obtain ⟨B₀,C,K,hCmin,hB₀,hC,hK,N₀,hN₀,hCircle⟩ :=
    goldbach_sieve_remainders_selected_above Cmin HSW HBV Hminor ψ hψ hsψ hA (by norm_num : (0:ℝ)<1/2)
  refine ⟨B₀,C,K,hCmin,hB₀,hC,hK,N₀,hN₀,?_⟩
  intro N hN B hB c hc
  have hN4 : (4:ℝ)≤N := by exact_mod_cast hN₀.trans hN
  have hN0 : (0:ℝ)≤N := Nat.cast_nonneg _
  have hlog : 0<Real.log N := Real.log_pos (by linarith)
  have hpow := Real.rpow_pos_of_pos hlog B
  let T := (range (Nat.ceil (goldbachLowerSieveLevel B N))).filter (fun d=>0<d)
  let I := T.image (fun d : ℕ=>(1,24*d))
  let V := fun ℓ : ℕ=>Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)
  let a := fun i : ℕ×ℕ=>goldbachLowerSieveResidue (i.2/24)
  let u := fun i : ℕ×ℕ=>(c (i.2/24):ℂ)
  have hdiv (d : ℕ) : 24*d/24=d := by omega
  have hinj : Set.InjOn (fun d : ℕ=>(1,24*d)) (↑T:Set ℕ) := by
    intro d _ e _ he
    have hh := congrArg Prod.snd he
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0<24) hh
  have hI : I⊆goldbachCoefficientIndices 2 V := by
    intro i hi
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hi
    obtain ⟨hd,hpos⟩ := mem_filter.mp hd
    have hlev : (d:ℝ)<goldbachLowerSieveLevel B N := Nat.lt_ceil.mp (mem_range.mp hd)
    apply (mem_goldbachCoefficientIndices 2 V 1 (24*d)).mpr
    refine ⟨by decide,by norm_num,Nat.mul_pos (by decide) hpos,?_⟩
    dsimp only [V]
    rw [Nat.cast_one,div_one,Real.sqrt_sq hN0,Real.rpow_neg hlog.le]
    dsimp only [goldbachLowerSieveLevel] at hlev
    have h := (lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<24) hpow)).mp hlev
    push_cast
    apply (lt_div_iff₀ hpow).mpr
    simpa only [div_eq_mul_inv] using (show (24:ℝ)*(d:ℝ)*(Real.log N)^B<N by nlinarith only [h])
  have ha : ∀ i∈I,(a i).Coprime i.2 := by
    intro i hi
    obtain ⟨d,_,rfl⟩ := mem_image.mp hi
    simpa only [a,hdiv] using goldbach_lower_residue_coprime d
  have hu : ∀ i∈I,‖u i‖≤1 := by
    intro i _
    simpa only [u,Complex.norm_real,Real.norm_eq_abs] using hc (i.2/24)
  have hL : (2:ℝ)<(N:ℝ)^(2-(1/2:ℝ)) := by
    have hh : (N:ℝ)≤(N:ℝ)^(2-(1/2:ℝ)) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤N) (by norm_num : (1:ℝ)≤2-1/2)
    linarith
  have hbound := (hCircle N hN B 2 hB hL V (fun _ _ _=>le_rfl) I hI a ha u hu).1
  have he (n : ℕ) : goldbachLowerRemainderSum ψ N B ((Real.log N)^C) c n=
      (∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n).re := by
    dsimp only [I]
    rw [sum_image hinj]
    simp only [u,a,hdiv,Complex.re_sum,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rfl
  apply le_trans (sum_le_sum (fun n _=>?_)) hbound
  rw [he]
  have hh := Complex.abs_re_le_norm
    (∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n)
  nlinarith only [hh,abs_nonneg
    ((∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n).re),
    norm_nonneg (∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n),sq_abs
      ((∑ i∈I,u i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n).re)]


theorem goldbach_lower_sieve_complete_above (Cmin : ℝ)
    (HSW : RawPrimeSiegelWalfiszInput) (HBV : RawPrimeBombieriVinogradovInput)
    (Hminor : UniformRenGhoshInputs) (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x|→ψ x=0)
    (K K₀ c sstar K₁ δ : ℝ) (f F : ℝ→ℝ)
    (hK : 0≤K) (hK₀ : 0≤K₀) (hc : 0<c) (hδ : 0<δ)
    (hM : GoldbachClassicalIntervalMertens K)
    (hpre : GoldbachClassicalFundamentalInput 2 K K₀ c sstar)
    (houter : GoldbachClassicalCoefficientInput ((1:ℝ)/2) K K₁ δ f F)
    (hf : ContinuousAt f ((9:ℝ)/8)) {A : ℝ} (hA : 0<A) :
    ∃ B C M : ℝ,Cmin≤C ∧ 0≤B ∧ 0<C ∧ 0<M ∧ ∃ η : ℝ→ℝ,
      Tendsto η atTop (nhds 0) ∧ ∀ᶠ N : ℕ in atTop,
        ∃ cm : ℕ→ℝ,(∀ d : ℕ,|cm d|≤1) ∧
          (∀ n : ℕ,(n:ZMod 24)=12→
            goldbachLowerMainTerm ψ N ((Real.log N)^C) n*
              goldbachLowerTheta ((Real.log N)^C) (goldbachLowerSiftingLimit N) n*
              (f ((9:ℝ)/8)-η N)+goldbachLowerRemainderSum ψ N B ((Real.log N)^C) cm n≤
                ((goldbachSiftedValues n (goldbachLowerSiftingLimit N)).card:ℝ)) ∧
          (∑ n∈range (N^2),(goldbachLowerRemainderSum ψ N B ((Real.log N)^C) cm n)^2)≤
            M*(N:ℝ)^4*(Real.log N)^(-A) := by
  classical
  obtain ⟨B,C,M,hCmin,hB,hC,hMpos,N₀,hN₀,hRem⟩ :=
    goldbach_lower_remainder_mean_square_above Cmin HSW HBV Hminor ψ hψ hsψ hA
  let z := goldbachLowerSiftingLimit
  let D₁ := goldbachLowerOuterLevel B
  let P := fun N : ℝ=>goldbachLowerPreliminaryPrimes ((Real.log N)^C) (z N)
  let Q := fun N : ℝ=>goldbachLowerOuterPrimes ((Real.log N)^C) (z N)
  have hlarge : ∀ᶠ N : ℝ in atTop,1<N ∧ Disjoint (P N) (Q N) ∧
      Real.exp (C*Real.log (Real.log N))+1≤z N ∧ z N≤D₁ N ∧ D₁ N≤N^(2:ℝ) ∧
      (∀ p∈P N,p.Prime ∧ (p:ℝ)<Real.exp (C*Real.log (Real.log N))+1) ∧
      (∀ p∈Q N,p.Prime ∧ (p:ℝ)<z N) := by
    filter_upwards [goldbach_lower_sieve_levels_eventually B C] with N hN
    obtain ⟨hN,hR,hD,hU⟩ := hN
    have he := goldbach_presieve_source_R N C hN
    refine ⟨hN,(goldbach_lower_prime_split _ _).1,?_,hD,hU,?_,?_⟩
    · simpa only [←he] using hR
    · intro p hp
      obtain ⟨hp,hpR⟩ := mem_filter.mp hp
      refine ⟨((mem_goldbach_lower_sieve_primes (z N) p).mp hp).1.1,?_⟩
      rw [←he]
      linarith
    · intro p hp
      have hs := (mem_goldbach_lower_sieve_primes (z N) p).mp (mem_filter.mp hp).1
      exact ⟨hs.1.1,hs.2⟩
  obtain ⟨hε,hAt⟩ := goldbach_corrected_presieving.{0} C 2 2 ((1:ℝ)/2) K K₀ c sstar K₁ δ
    z D₁ P Q f F hC (by norm_num) (by norm_num) hK hK₀ hc hδ hpre houter hlarge
  let η := fun N : ℝ=>goldbachLowerSieveError B C K K₀ c K₁ δ N+
    |f (Real.log (D₁ N)/Real.log (z N))-f ((9:ℝ)/8)|
  have hflim := hf.tendsto.comp (goldbach_lower_sieve_parameter_tendsto B)
  have hη : Tendsto η atTop (nhds 0) := by
    have hh := hε.add ((hflim.sub_const (f ((9:ℝ)/8))).abs)
    simpa only [η,goldbachLowerSieveError,z,D₁,sub_self,abs_zero,add_zero,Function.comp_def] using hh
  refine ⟨B,C,M,hCmin,hB,hC,hMpos,η,hη,?_⟩
  have hRlarge : ∀ᶠ N : ℝ in atTop,3≤(Real.log N)^C :=
    ((tendsto_rpow_atTop hC).comp Real.tendsto_log_atTop).eventually_ge_atTop 3
  have hNat : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hNat.eventually hAt,hNat.eventually hRlarge,eventually_ge_atTop N₀] with N hAt hR hN
  have hN2 : 2≤N := by omega
  obtain ⟨cm,hcm,hpoint⟩ := goldbach_lower_presieve_application ψ hψ N hN2
    B C K K₀ c K₁ δ f F hR hM hAt
  refine ⟨cm,hcm,?_,hRem N hN B le_rfl cm hcm⟩
  intro n hn
  have hp := hpoint n hn
  have hnonneg := mul_nonneg (goldbach_lower_main_term_nonneg ψ hψ N hN2 _ hR n hn)
    (goldbach_lower_theta_positive ((Real.log N)^C) (z N) n).le
  have hcoef : f ((9:ℝ)/8)-η N≤
      f (Real.log (D₁ N)/Real.log (z N))-goldbachLowerSieveError B C K K₀ c K₁ δ N := by
    dsimp only [η]
    linarith only [neg_abs_le (f (Real.log (D₁ N)/Real.log (z N))-f ((9:ℝ)/8))]
  exact (add_le_add (mul_le_mul_of_nonneg_left hcoef hnonneg) le_rfl).trans hp


end PrimeSquares
