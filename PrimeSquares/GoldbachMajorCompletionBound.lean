import PrimeSquares.GoldbachCompletionBudgets
import PrimeSquares.ThreeTermSquareBound

set_option autoImplicit false
open Finset MeasureTheory
open scoped SchwartzMap
namespace PrimeSquares

theorem goldbach_major_completion_coefficient_complete (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x| →ψ x=0) {A : ℝ} (hA : 0<A) :
    ∃ C₀ : ℝ,0<C₀ ∧ ∀ C : ℝ,C₀≤C →∃ K : ℝ,0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧
      ∀ N : ℕ,N₀≤N →∀ L B : ℝ,∀ V : ℕ→ℝ,0≤B →L≤(N:ℝ)^2 →
      (∀ ℓ : ℕ,0<ℓ →(ℓ:ℝ)<L →V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) →
      ∀ a : ℕ×ℕ→ℕ,(∀ i∈goldbachCoefficientIndices L V,(a i).Coprime i.2) →
      ∀ d : ℕ×ℕ→ℂ,(∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1) →
      ∀ U W : ℝ,2≤U →U≤N →2≤W →
      (∑ n∈range (N^2),‖goldbachMajorModelCoefficient N (goldbachCoefficientIndices L V) a d ((Real.log N)^C) U W n-
        goldbachCompletedMainTerm ψ N (goldbachCoefficientIndices L V) a d ((Real.log N)^C) U W n‖^2)≤
        K*(N:ℝ)^4*(Real.log N)^(-A) := by
  classical
  obtain ⟨KS,hKS,hSmall⟩ := goldbach_small_smoothing_uniform ψ hψ
  obtain ⟨KE,hKE,hAdded⟩ := goldbach_smooth_added_major_bessel ψ hψ hsψ
  refine ⟨2*A+16,by linarith,?_⟩
  intro C hC
  have hC1 : 1≤C := by linarith
  obtain ⟨NG,hNG,hGeom⟩ := goldbach_completion_all_parameters_eventual hC1
  obtain ⟨NT,hNT,hTail⟩ := goldbach_source_rankin_arithmetic_tail ψ hψ hC1 hA
  let K := 3*(KS^2*(C+1)^2+KE+goldbachArithmeticTailConstant^2)
  have hK : 0<K := by dsimp [K];positivity
  refine ⟨K,hK,max NG NT,by omega,?_⟩
  intro N hN L B V hB hL hV a ha d hd U W hU hUN hW
  obtain ⟨hlog,hR,hRY,hY,hhalf,hsep,hSepHard,hHalfHard⟩ := hGeom N ((le_max_left _ _).trans hN)
  obtain ⟨_,_,hTailN⟩ := hTail N ((le_max_right _ _).trans hN)
  have hN1 : 1≤N := by omega
  have hlog1 : 1≤Real.log N := by linarith
  let I := goldbachCoefficientIndices L V
  let R := (Real.log N)^C
  let Y := (N:ℝ)/(100*Real.sqrt R)
  let S := goldbachSmallCompletionError ψ N I a d R U W
  let E := goldbachAddedCompletionError ψ N I a d R Y U W
  let F := goldbachFarCompletionError ψ N I a d R Y U W
  have haI : ∀ i∈I,IsCoprime (i.2:ℤ) (a i:ℤ) := by
    intro i hi
    exact Nat.isCoprime_iff_coprime.mpr (ha i hi).symm
  have hSpoint (n : ℕ) : ‖S n‖≤KS*(N:ℝ)*(Real.log N)^2*(1+Real.log R)/R^(1/4:ℝ) :=
    hSmall N hN1 hlog1 L B V hB hL hV (fun i=>(a i:ℤ)) haI d hd R U W hR hU hUN hW n
  have hS0 : 0≤KS*(N:ℝ)*(Real.log N)^2*(1+Real.log R)/R^(1/4:ℝ) := by
    have := Real.log_nonneg (show 1≤R by linarith)
    positivity
  have hSmean : (∑ n∈range (N^2),‖S n‖^2)≤KS^2*(C+1)^2*(N:ℝ)^4*(Real.log N)^(-A) :=
    (goldbach_uniform_finite_square_sum N (fun n=>S n) hS0 (fun n _=>hSpoint n)).trans
      (goldbach_small_completion_square_budget N hlog1 hKS.le (by linarith) (by linarith))
  let e : ℕ↪ℤ := ⟨fun n=>n,fun _ _ h=>Int.ofNat_inj.mp h⟩
  have hBessel := hAdded N hN1 hlog1 L B V hB hL hV (fun i=>(a i:ℤ)) haI d hd
    U W R Y hU hUN hW hR hY hhalf hsep (goldbachAddedCompletionCenters R Y)
    (goldbach_added_completion_centers_subset R Y) ((range (N^2)).map e)
  have hEmean : (∑ n∈range (N^2),‖E n‖^2)≤KE*(N:ℝ)^4*(Real.log N)^(-A) := by
    have hh : (∑ n∈range (N^2),‖E n‖^2)≤KE*(N:ℝ)^4*(Real.log N)^4/Real.sqrt R := by
      rw [sum_map] at hBessel
      apply le_trans _ hBessel
      apply le_of_eq
      apply sum_congr rfl
      intro n _
      rfl
    apply hh.trans
    calc
      _=(KE*(N:ℝ)^4)*((Real.log N)^4/Real.sqrt R) := by ring
      _≤_ := mul_le_mul_of_nonneg_left (goldbach_completion_log_power_rate N hlog1 4 A C (by norm_num;linarith)) (by positivity)
  have hFpoint (n : ℕ) : ‖F n‖≤goldbachArithmeticTailConstant*(N:ℝ)*(Real.log N)^(-A) := by
    apply hTailN L B V hB hL hV (fun i=>(a i:ℤ)) haI d hd U W hU hUN hW
      (smoothEulerBound (⌊R⌋₊+1)) (goldbach_completion_bound_nezero R) (goldbach_completion_bound_primes hR)
      ((goldbachCompletionDivisors R).filter (fun q : ℕ=>Y<(q:ℝ))) _ (n:ℤ)
    intro q hq
    exact mem_filter.mp hq
  have hF0 : 0≤goldbachArithmeticTailConstant*(N:ℝ)*(Real.log N)^(-A) := by
    have := goldbachArithmeticTailConstant_pos
    positivity
  have hFmean : (∑ n∈range (N^2),‖F n‖^2)≤goldbachArithmeticTailConstant^2*(N:ℝ)^4*(Real.log N)^(-A) :=
    (goldbach_uniform_finite_square_sum N (fun n=>F n) hF0 (fun n _=>hFpoint n)).trans
      (goldbach_far_completion_square_budget N hlog1 goldbachArithmeticTailConstant_pos.le hA)
  have he (n : ℕ) : goldbachMajorModelCoefficient N I a d R U W n-goldbachCompletedMainTerm ψ N I a d R U W n=
      S n-E n-F n :=
    goldbach_completion_error_identity ψ hψ N hN1 hlog1 L B V hB hL hV a haI d hd
      hR hRY hSepHard hHalfHard hU hUN hW n
  calc
    _≤∑ n∈range (N^2),3*(‖S n‖^2+‖E n‖^2+‖F n‖^2) := by
      apply sum_le_sum
      intro n _
      rw [he]
      have hh := norm_three_sum_square (S n) (-(E n)) (-(F n))
      simpa only [sub_eq_add_neg,norm_neg] using hh
    _=3*((∑ n∈range (N^2),‖S n‖^2)+(∑ n∈range (N^2),‖E n‖^2)+(∑ n∈range (N^2),‖F n‖^2)) := by
      rw [←mul_sum,sum_add_distrib,sum_add_distrib]
    _≤3*(KS^2*(C+1)^2*(N:ℝ)^4*(Real.log N)^(-A)+KE*(N:ℝ)^4*(Real.log N)^(-A)+
        goldbachArithmeticTailConstant^2*(N:ℝ)^4*(Real.log N)^(-A)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hSmean hEmean) hFmean) (by norm_num)
    _=_ := by dsimp [K];ring

end PrimeSquares
