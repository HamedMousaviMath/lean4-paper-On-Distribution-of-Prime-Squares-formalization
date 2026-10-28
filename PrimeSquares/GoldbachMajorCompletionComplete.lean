import PrimeSquares.GoldbachMajorCompletionBound

set_option autoImplicit false
open Finset MeasureTheory
open scoped SchwartzMap ENNReal
namespace PrimeSquares

theorem goldbach_model_weighted_coefficient (N n : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (R : ℝ) {U W : ℝ} (hU : 2≤U) (hW : 2≤W)
    (hI : ∀ i∈I,0 < i.1) (hX : ∀ i∈I,2≤(N:ℝ)^2/i.1) :
    (∑ i∈I,d i*(∫ θ : PrimeCircle in GoldbachMajorArcs N R,
      goldbachSquareMajorModel N R U θ*goldbachProgressionMajorModel N i.1 i.2 (a i) R W θ*
        fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle))=
      goldbachMajorModelCoefficient N I a d R U W n := by
  have hQ := goldbachSquareMajorModel_memLp N R hU ∞
  have hφ : MemLp ((fourier (-(n:ℤ))) : PrimeCircle→ℂ) ∞ AddCircle.haarAddCircle :=
    ContinuousMap.memLp AddCircle.haarAddCircle ℂ _
  have hi (i : ℕ×ℕ) (hi : i∈I) : Integrable (fun θ : PrimeCircle=>
      goldbachSquareMajorModel N R U θ*goldbachProgressionMajorModel N i.1 i.2 (a i) R W θ*
        fourier (-(n:ℤ)) θ) (AddCircle.haarAddCircle.restrict (GoldbachMajorArcs N R)) := by
    have hG := goldbachProgressionMajorModel_memLp N i.1 i.2 (a i) (hI i hi) R hW (hX i hi) 1
    have hm : MemLp (fun θ : PrimeCircle=>goldbachSquareMajorModel N R U θ*
        goldbachProgressionMajorModel N i.1 i.2 (a i) R W θ*fourier (-(n:ℤ)) θ) 1 AddCircle.haarAddCircle :=
      (hQ.mul (r:=1) hG).mul hφ
    exact (hm.integrable (by norm_num)).restrict
  simp_rw [←integral_const_mul]
  rw [←integral_finsetSum I (fun i h=>(hi i h).const_mul (d i))]
  unfold goldbachMajorModelCoefficient
  apply integral_congr_ae
  filter_upwards with θ
  simp only [goldbachWeightedProgressionMajorModel,mul_sum,sum_mul]
  apply sum_congr rfl
  intro i _
  ring

theorem goldbach_source_ranges_eventual {δ : ℝ} (hδ : 0<δ) :
    ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →∀ L : ℝ,L<(N:ℝ)^(2-δ) →
      L≤(N:ℝ)^2 ∧ ∀ V : ℕ→ℝ,∀ i∈goldbachCoefficientIndices L V,2≤(N:ℝ)^2/i.1 := by
  obtain ⟨N₀,hN₀,hScale⟩ := goldbach_bv_source_eventual_threshold (L:=0) hδ (by norm_num : (4:ℝ)≤4)
  refine ⟨N₀,hN₀,?_⟩
  intro N hN L hL
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hp : (N:ℝ)^(2-δ)≤(N:ℝ)^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  refine ⟨hL.le.trans hp,?_⟩
  intro V i hi
  obtain ⟨hℓ,hℓL,_,_⟩ := (mem_goldbachCoefficientIndices L V i.1 i.2).mp hi
  have hx := (goldbach_progression_scale_logs N i.1 (by omega) hℓ δ (hℓL.trans hL)).1
  have hs := (hScale N hN).2.2
  linarith

theorem goldbach_major_completion_complete (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x| →ψ x=0) {A δ : ℝ} (hA : 0<A) (hδ : 0<δ) :
    ∃ C₀ : ℝ,0<C₀ ∧ ∀ C : ℝ,C₀≤C →∃ K : ℝ,0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧
      ∀ N : ℕ,N₀≤N →∀ L B : ℝ,∀ V : ℕ→ℝ,0≤B →L<(N:ℝ)^(2-δ) →
      (∀ ℓ : ℕ,0<ℓ →(ℓ:ℝ)<L →V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) →
      ∀ a : ℕ×ℕ→ℕ,(∀ i∈goldbachCoefficientIndices L V,(a i).Coprime i.2) →
      ∀ d : ℕ×ℕ→ℂ,(∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1) →
      ∀ U W : ℝ,2≤U →U≤N →2≤W →
      (∑ n∈range (N^2),‖∑ i∈goldbachCoefficientIndices L V,d i*
        ((∫ θ : PrimeCircle in GoldbachMajorArcs N ((Real.log N)^C),
          goldbachSquareMajorModel N ((Real.log N)^C) U θ*
            goldbachProgressionMajorModel N i.1 i.2 (a i) ((Real.log N)^C) W θ*
              fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle)-
          goldbachArithmeticFactor ((Real.log N)^C) i.2 (i.1:ℤ) (a i:ℤ) n/
            ((i.1:ℂ)*(i.2.totient:ℂ))*goldbachSingularIntegral ψ N i.1 ((Real.log N)^C) (n:ℝ) U W)‖^2)≤
        K*(N:ℝ)^4*(Real.log N)^(-A) := by
  obtain ⟨C₀,hC₀,hCompletion⟩ := goldbach_major_completion_coefficient_complete ψ hψ hsψ hA
  obtain ⟨NX,hNX,hRanges⟩ := goldbach_source_ranges_eventual hδ
  refine ⟨C₀,hC₀,?_⟩
  intro C hC
  obtain ⟨K,hK,NC,hNC,hBound⟩ := hCompletion C hC
  refine ⟨K,hK,max NC NX,hNC.trans (le_max_left _ _),?_⟩
  intro N hN L B V hB hL hV a ha d hd U W hU hUN hW
  obtain ⟨hL2,hX⟩ := hRanges N ((le_max_right _ _).trans hN) L hL
  have hI : ∀ i∈goldbachCoefficientIndices L V,0 < i.1 :=
    fun i hi=>((mem_goldbachCoefficientIndices L V i.1 i.2).mp hi).1
  have h := hBound N ((le_max_left _ _).trans hN) L B V hB hL2 hV a ha d hd U W hU hUN hW
  have he (n : ℕ) : (∑ i∈goldbachCoefficientIndices L V,d i*
      ((∫ θ : PrimeCircle in GoldbachMajorArcs N ((Real.log N)^C),
        goldbachSquareMajorModel N ((Real.log N)^C) U θ*
          goldbachProgressionMajorModel N i.1 i.2 (a i) ((Real.log N)^C) W θ*
            fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle)-
        goldbachArithmeticFactor ((Real.log N)^C) i.2 (i.1:ℤ) (a i:ℤ) n/
          ((i.1:ℂ)*(i.2.totient:ℂ))*goldbachSingularIntegral ψ N i.1 ((Real.log N)^C) (n:ℝ) U W))=
      goldbachMajorModelCoefficient N (goldbachCoefficientIndices L V) a d ((Real.log N)^C) U W n-
        goldbachCompletedMainTerm ψ N (goldbachCoefficientIndices L V) a d ((Real.log N)^C) U W n := by
    simp only [mul_sub,sum_sub_distrib]
    rw [goldbach_model_weighted_coefficient N n _ a d _ hU hW hI (hX V)]
    congr 1
    unfold goldbachCompletedMainTerm
    apply sum_congr rfl
    intro i _
    rw [Int.cast_natCast]
    ring
  simpa only [he] using h

end PrimeSquares
