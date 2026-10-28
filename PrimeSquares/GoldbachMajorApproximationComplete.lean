import PrimeSquares.GoldbachMajorWeightedAssembly

set_option autoImplicit false
open Finset MeasureTheory
open scoped ENNReal
namespace PrimeSquares

theorem goldbach_major_approximation_complete
    (HSW : RawPrimeSiegelWalfiszInput) (HBV : RawPrimeBombieriVinogradovInput)
    {A C δ : ℝ} (hA : 0<A) (hC : 0≤C) (hδ : 0<δ) :
    ∃ B₀ K : ℝ,0≤B₀ ∧ 0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      ∀ B L₀ : ℝ,B₀≤B → L₀<(N:ℝ)^(2-δ) →
      ∀ V : ℕ→ℝ,(∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L₀ →
        V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) →
      ∀ a : ℕ×ℕ→ℕ,(∀ i∈goldbachCoefficientIndices L₀ V,(a i).Coprime i.2) →
      ∀ d : ℕ×ℕ→ℂ,(∀ i∈goldbachCoefficientIndices L₀ V,‖d i‖≤1) →
      ∀ U W : ℝ,2≤U → U≤N → 2≤W →
      (∑ n∈range (N^2),‖∑ i∈goldbachCoefficientIndices L₀ V,d i*
        (∫ θ : PrimeCircle in GoldbachMajorArcs N ((Real.log N)^C),
          (goldbachPrimeSquarePolynomial U θ*goldbachProgressionPolynomial N i.1 i.2 (a i) W θ-
            goldbachSquareMajorModel N ((Real.log N)^C) U θ*
              goldbachProgressionMajorModel N i.1 i.2 (a i) ((Real.log N)^C) W θ)*
            fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle)‖^2)≤
        K*(N:ℝ)^4*(Real.log N)^(-A) := by
  classical
  have htP : 0<(A+6)/2 := by linarith
  have htE : 0<(A+3*C)/2 := by linarith
  obtain ⟨KP,hKP,NP,hNP,hSW⟩ := goldbach_square_circle_major_sw HSW htP hC
  obtain ⟨B₀,KE,hB₀,hKE,NE,hNE,hBV⟩ := goldbach_linear_circle_major_bv HBV htE hC hδ
  let K := 2*(8*KE^2/(Real.log 2)^2+KP^2*(256/Real.log 2))
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0<K := by dsimp only [K]; positivity
  refine ⟨B₀,K,hB₀,hK,max NP NE,hNP.trans (le_max_left _ _),?_⟩
  intro N hN B L₀ hB hL V hV a ha d hd U W hU hUN hW
  obtain ⟨hl,hR,hsep,hSWN⟩ := hSW N ((le_max_left _ _).trans hN)
  obtain ⟨_,_,_,hBVN⟩ := hBV N ((le_max_right _ _).trans hN)
  obtain ⟨hX,hBVN⟩ := hBVN B L₀ hB hL V hV
  have hNnat : 1≤N := by omega
  have hlpos : 0<Real.log N := by linarith
  let I := goldbachCoefficientIndices L₀ V
  let R := (Real.log N)^C
  let s := GoldbachMajorArcs N R
  let P : PrimeCircle→ℂ := goldbachPrimeSquarePolynomial U
  let F : PrimeCircle→ℂ := goldbachWeightedProgressionPolynomial N I a d W
  let Q := goldbachSquareMajorModel N R U
  let G := goldbachWeightedProgressionMajorModel N I a d R W
  have hI : ∀ i∈I,0 < i.1 := by
    intro i hi
    exact ((mem_goldbachCoefficientIndices L₀ V i.1 i.2).mp hi).1
  have hs : MeasurableSet s := goldbachMajorArcs_measurable N R
  have hP : MemLp P ∞ AddCircle.haarAddCircle := ContinuousMap.memLp AddCircle.haarAddCircle ℂ _
  have hF : MemLp F 2 AddCircle.haarAddCircle := ContinuousMap.memLp AddCircle.haarAddCircle ℂ _
  have hQ : MemLp Q ∞ AddCircle.haarAddCircle := goldbachSquareMajorModel_memLp N R hU ∞
  have hG : MemLp G 2 AddCircle.haarAddCircle :=
    goldbachWeightedProgressionMajorModel_memLp N I a d R hW hI hX 2
  have hQbound : ∀ θ∈s,‖Q θ‖≤(N:ℝ)/Real.log 2 :=
    goldbachSquareMajorModel_norm_on_major N hNnat hR hsep hU hUN
  have hPbound : ∀ θ∈s,‖P θ-Q θ‖≤KP*(N:ℝ)*(Real.log N)^(-((A+6)/2)) :=
    hSWN U hU hUN
  have hFbound : ∀ θ∈s,‖F θ-G θ‖≤KE*(N:ℝ)^2*(Real.log N)^(-((A+3*C)/2)) := by
    intro θ hθ
    apply (goldbach_weighted_major_error_le_sum N I a d R W hd θ).trans
    exact hBVN a ha (fun _ => W) (fun _ _ => hW) θ hθ
  have henergy : (∫ θ : PrimeCircle,‖F θ‖^2 ∂AddCircle.haarAddCircle)≤
      (256/Real.log 2)*(N:ℝ)^2*(Real.log N)^6 :=
    goldbach_source_progression_energy_printed_range N hNnat hl L₀ B δ V (hB₀.trans hB)
      hδ hL hV a d W hd
  let e : ℕ↪ℤ := ⟨fun n => n,fun _ _ h => Int.ofNat_inj.mp h⟩
  let S := (range (N^2)).map e
  have hb := goldbach_two_model_major_bessel S s hs P F Q G hP hF hQ hG
    (by positivity : 0≤(N:ℝ)/Real.log 2) hQbound hPbound hFbound henergy
  have hmeasure := goldbach_major_arcs_measure N hNnat hR
  have hb' : (∑ n∈S,‖∫ θ : PrimeCircle in s,(P θ*F θ-Q θ*G θ)*fourier (-n) θ
      ∂AddCircle.haarAddCircle‖^2)≤
      2*(((N:ℝ)/Real.log 2)^2*(KE*(N:ℝ)^2*(Real.log N)^(-((A+3*C)/2)))^2*
        (8*R^3/(N:ℝ)^2)+
      (KP*(N:ℝ)*(Real.log N)^(-((A+6)/2)))^2*((256/Real.log 2)*(N:ℝ)^2*(Real.log N)^6)) := by
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
    exact add_le_add (mul_le_mul_of_nonneg_left hmeasure
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))) le_rfl
  have hid (n : ℕ) := goldbach_major_weighted_coefficient_identity N n I a d R hU hW hI hX s
  calc
    _=(∑ n∈S,‖∫ θ : PrimeCircle in s,(P θ*F θ-Q θ*G θ)*fourier (-n) θ
      ∂AddCircle.haarAddCircle‖^2) := by
      rw [Finset.sum_map]
      apply sum_congr rfl
      intro n _
      rw [hid]
      rfl
    _≤_ := hb'
    _=K*(N:ℝ)^4*(Real.log N)^(-A) :=
      goldbach_major_mean_square_budget N hNnat hlpos A C KP KE

end PrimeSquares
