import PrimeSquares.GeneralParentPrimeEndpoint
import PrimeSquares.QuadraticLocalRadiusBridge
import PrimeSquares.PhysicalDyadicPrimeStopping

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem source_prime_local_endpoint {c δ CS cstar C A : ℝ}
    (D : PagePrimeSquareDistributionInputs c) (H419 : Proposition419Bounds D δ) (hδ : 0 < δ)
    (hCS : 1 ≤ CS) (HS : OrdinarySquareStoppingInput CS) (hstar : 4*Real.sqrt 3/9 < cstar)
    (m : ℕ) (hm : 1 ≤ m) (hC : 0 < C) (hA : 0 ≤ A) :
    ∃ K : ℝ,0 < K ∧ ∀ (I : SparseIntegerInterval) (F G : Finset ℤ) (τ : ℤ → ℕ),
      (∀ y ∈ F,|y-I.left| ≤ (m:ℤ)*I.length) → G ⊆ I.points →
      (∀ x ∈ G,∃ j : ℕ,τ x=2^j) → (∀ x ∈ G,(τ x)^2 ≤ I.length) →
      (∀ x ∈ G,∀ M : ℝ,(τ x:ℝ) ≤ M →
        (linearWindowCount C (M^2) F x:ℝ)/M^2 ≤ A*((F.card:ℝ)/I.length)) →
      ‖∑ x ∈ G,physicalAnnularPrimeValue (τ x) F x‖/(I.length:ℝ) ≤
        K*(finiteSetDensity I.length F G)^(2/3:ℝ)*paperPhi cstar (1/2) (finiteSetDensity I.length F G) := by
  let R : ℝ := max 1 (1/C)
  have hR : 0 ≤ R := by have h:=le_max_left (1:ℝ) (1/C); linarith
  obtain ⟨K,hK,hbound⟩ := primeStopping_general_parent_endpoint D H419 hδ hCS HS hstar m hm
    (mul_nonneg hR hA)
  refine ⟨K,hK,?_⟩
  intro I F G τ hF hG hτ hscale hadm
  by_cases hF0 : F=∅
  · subst F
    simp [physicalAnnularPrimeValue_empty,finiteSetDensity,Real.zero_rpow (by norm_num : (2/3:ℝ)≠0)]
  by_cases hG0 : G=∅
  · subst G
    simp [finiteSetDensity,Real.zero_rpow (by norm_num : (2/3:ℝ)≠0)]
  let G₂ := G.filter (fun x => 2 ≤ τ x)
  let t := fun x : ℤ => Nat.log2 (τ x)-1
  have hG₂ : G₂ ⊆ G := Finset.filter_subset _ _
  have ht (x : ℤ) (hx : x ∈ G₂) : (2:ℕ)^(t x)*2=τ x :=
    physicalDyadic_above_one (Finset.mem_filter.mp hx).2 (hτ x (hG₂ hx))
  have hscale' (x : ℤ) (hx : x ∈ G₂) : ((2:ℕ)^(t x)*2)^2 ≤ I.length := by
    rw [ht x hx]
    exact hscale x (hG₂ hx)
  have hadm' (x : ℤ) (hx : x ∈ G₂) :
      sourceLocalMass ((2:ℕ)^(t x)*2) (finiteIndicatorLp F 1) x ≤ (R*A)*((F.card:ℝ)/I.length) := by
    rw [ht x hx]
    have hN : 1 ≤ τ x := by have h:=(Finset.mem_filter.mp hx).2; omega
    have h := sourceLocalMass_from_quadratic_radius hN hC F x (hadm x (hG₂ hx))
    exact h.trans_eq (by dsimp [R]; ring)
  have h := hbound I F G₂ G t hF hG hG₂
    (Finset.nonempty_iff_ne_empty.mpr hF0) (Finset.nonempty_iff_ne_empty.mpr hG0) hscale' hadm'
  rw [physicalDyadic_prime_pairing F G τ hτ]
  exact h

theorem source_prime_local_endpoint_real_dilation {c δ CS cstar C A dilation : ℝ}
    (D : PagePrimeSquareDistributionInputs c) (H419 : Proposition419Bounds D δ) (hδ : 0 < δ)
    (hCS : 1 ≤ CS) (HS : OrdinarySquareStoppingInput CS) (hstar : 4*Real.sqrt 3/9 < cstar)
    (hdilation : 1 ≤ dilation) (hC : 0 < C) (hA : 0 ≤ A) :
    ∃ K : ℝ,0 < K ∧ ∀ (I : SparseIntegerInterval) (F G : Finset ℤ) (τ : ℤ → ℕ),
      (∀ y ∈ F,(I.left:ℝ)-((dilation-1)/2)*(I.length:ℝ) ≤ (y:ℝ) ∧
        (y:ℝ)<(I.left:ℝ)+((dilation+1)/2)*(I.length:ℝ)) → G ⊆ I.points →
      (∀ x ∈ G,∃ j : ℕ,τ x=2^j) → (∀ x ∈ G,(τ x)^2 ≤ I.length) →
      (∀ x ∈ G,∀ M : ℝ,(τ x:ℝ) ≤ M →
        (linearWindowCount C (M^2) F x:ℝ)/M^2 ≤ A*((F.card:ℝ)/I.length)) →
      ‖∑ x ∈ G,physicalAnnularPrimeValue (τ x) F x‖/(I.length:ℝ) ≤
        K*(finiteSetDensity I.length F G)^(2/3:ℝ)*paperPhi cstar (1/2) (finiteSetDensity I.length F G) := by
  let m : ℕ := ⌈dilation⌉₊+1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmd : dilation ≤ (m:ℝ) := by
    have hh : dilation ≤ (⌈dilation⌉₊:ℝ) := Nat.le_ceil _
    dsimp [m]
    push_cast
    linarith
  obtain ⟨K,hK,hbound⟩ := source_prime_local_endpoint D H419 hδ hCS HS hstar m hm hC hA
  refine ⟨K,hK,?_⟩
  intro I F G τ hF hG hτ hscale hadm
  apply hbound I F G τ _ hG hτ hscale hadm
  intro y hy
  have hL : (0:ℝ)≤I.length := Nat.cast_nonneg _
  have hminus := mul_le_mul_of_nonneg_right (by linarith : (dilation-1)/2 ≤ (m:ℝ)) hL
  have hplus := mul_le_mul_of_nonneg_right (by linarith : (dilation+1)/2 ≤ (m:ℝ)) hL
  have hFy := hF y hy
  have hh : |((y-I.left:ℤ):ℝ)| ≤ (m:ℝ)*I.length := by
    rw [abs_le]
    push_cast
    constructor <;> linarith
  exact_mod_cast hh

theorem source_prime_local_endpoint_from_independent_inputs {c BC CS cstar C A dilation : ℝ}
    (HP : PrimeAsymptoticInputs) (D : PagePrimeSquareDistributionInputs c) (hc : 0 < c)
    (hBC : 0 ≤ BC) (HB : SmoothCircleBourgainInput BC) (HPage : RawPageUniquenessInput c)
    (hCS : 1 ≤ CS) (HS : OrdinarySquareStoppingInput CS) (hstar : 4*Real.sqrt 3/9 < cstar)
    (hdilation : 1 ≤ dilation) (hC : 0 < C) (hA : 0 ≤ A) :
    ∃ K : ℝ,0 < K ∧ ∀ (I : SparseIntegerInterval) (F G : Finset ℤ) (τ : ℤ → ℕ),
      (∀ y ∈ F,(I.left:ℝ)-((dilation-1)/2)*(I.length:ℝ) ≤ (y:ℝ) ∧
        (y:ℝ)<(I.left:ℝ)+((dilation+1)/2)*(I.length:ℝ)) → G ⊆ I.points →
      (∀ x ∈ G,∃ j : ℕ,τ x=2^j) → (∀ x ∈ G,(τ x)^2 ≤ I.length) →
      (∀ x ∈ G,∀ M : ℝ,(τ x:ℝ) ≤ M →
        (linearWindowCount C (M^2) F x:ℝ)/M^2 ≤ A*((F.card:ℝ)/I.length)) →
      ‖∑ x ∈ G,physicalAnnularPrimeValue (τ x) F x‖/(I.length:ℝ) ≤
        K*(finiteSetDensity I.length F G)^(2/3:ℝ)*paperPhi cstar (1/2) (finiteSetDensity I.length F G) := by
  obtain ⟨δ,hδ,H419⟩ := proposition419 HP D hc hBC HB HPage
  exact source_prime_local_endpoint_real_dilation D H419 hδ hCS HS hstar hdilation hC hA

end PrimeSquares
