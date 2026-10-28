import PrimeSquares.VariableAdmissibilityPrimeEndpoint
import PrimeSquares.ParentEndpointRescaling

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem primeStopping_general_parent_endpoint {c δ CS cstar A : ℝ}
    (D : PagePrimeSquareDistributionInputs c) (H419 : Proposition419Bounds D δ) (hδ : 0 < δ)
    (hCS : 1 ≤ CS) (HS : OrdinarySquareStoppingInput CS) (hstar : 4*Real.sqrt 3/9 < cstar)
    (m : ℕ) (hm : 1 ≤ m) (hA : 0 ≤ A) :
    ∃ Kout : ℝ,0 < Kout ∧ ∀ (I : SparseIntegerInterval) (F G H : Finset ℤ) (τ : ℤ → ℕ),
      (∀ y ∈ F,|y-I.left| ≤ (m:ℤ)*I.length) → H ⊆ I.points → G ⊆ H →
      F.Nonempty → H.Nonempty →
      (∀ x ∈ G,((2:ℕ)^(τ x)*2)^2 ≤ I.length) →
      (∀ x ∈ G,sourceLocalMass ((2:ℕ)^(τ x)*2) (finiteIndicatorLp F 1) x ≤ A*((F.card:ℝ)/I.length)) →
      ‖∑ x ∈ G,annularDyadicValue (τ x) F x‖/(I.length:ℝ) ≤
        Kout*(finiteSetDensity I.length F H)^(2/3:ℝ)*paperPhi cstar (1/2) (finiteSetDensity I.length F H) := by
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have hmp : (0:ℝ)<m := by linarith
  have hcstar : 0 < cstar := (by positivity : (0:ℝ)<4*Real.sqrt 3/9).trans hstar
  let B₀ : ℝ := 1+A*m
  have hB₀ : 1 ≤ B₀ := by dsimp [B₀]; nlinarith [mul_nonneg hA hmp.le]
  obtain ⟨K,hK,hbound⟩ := primeStopping_local_endpoint_with_constant D H419 hδ hCS hB₀ HS hstar
  let R : ℝ := (5*(m:ℝ))^2
  have hR : 1 ≤ R := by dsimp [R]; nlinarith
  let Kout : ℝ := (5*(m:ℝ))*K*Real.exp (cstar*Real.sqrt (Real.log R)/2)
  have hKout : 0 < Kout := by dsimp [Kout]; positivity
  refine ⟨Kout,hKout,?_⟩
  intro I F G H τ hF hH hGH hFn hHn hscale hadm
  let J := enlargedStoppingParent I m hm
  have hI : (0:ℝ)<I.length := by exact_mod_cast I.length_pos
  have hJ : (0:ℝ)<J.length := by exact_mod_cast J.length_pos
  have hHJ : H ⊆ J.points := hH.trans (enlargedStoppingParent_contains I m hm)
  have hGJ : G ⊆ J.points := hGH.trans hHJ
  have hFJ : F ⊆ J.five.points := enlargedStoppingParent_support I m hm F hF
  have hHJ5 : H ⊆ J.five.points := hHJ.trans (integerInterval_points_subset_five J)
  have hlen : I.length ≤ J.length := by
    dsimp [J,enlargedStoppingParent]
    nlinarith [I.length_pos]
  have hadm' (x : ℤ) (hx : x ∈ G) :
      sourceLocalMass ((2:ℕ)^(τ x)*2) (finiteIndicatorLp F 1) x ≤ B₀*((F.card:ℝ)/J.length) := by
    apply (hadm x hx).trans
    have he : A*((F.card:ℝ)/I.length)=(A*(m:ℝ))*((F.card:ℝ)/J.length) := by
      dsimp [J,enlargedStoppingParent]
      push_cast
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_right (by dsimp [B₀]; linarith) (by positivity)
  have hb := hbound J F G H τ hFJ hHJ5 hGJ hGH hFn hHn
    (fun x hx => (hscale x hx).trans hlen) hadm'
  let a := finiteSetDensity (5*(J.length:ℝ)) F H
  let b := finiteSetDensity I.length F H
  obtain ⟨ha,ha1⟩ := finiteSetDensity_five_bounds J F H hFJ hHJ5 hFn hHn
  have hba : b=R*a := enlargedStoppingParent_density I m hm F H
  have hab : a ≤ b := by
    have hmul := mul_le_mul_of_nonneg_right hR ha.le
    simp only [one_mul] at hmul
    exact hmul.trans_eq hba.symm
  have hf := primeEndpoint_fixed_density_rescale hcstar.le ha ha1 hR hab hba.le
  have hn : ‖∑ x ∈ G,annularDyadicValue (τ x) F x‖/(I.length:ℝ)=
      (5*(m:ℝ))*(‖∑ x ∈ G,annularDyadicValue (τ x) F x‖/(5*(J.length:ℝ))) := by
    dsimp [J,enlargedStoppingParent]
    push_cast
    field_simp
  rw [hn]
  calc
    _ ≤ (5*(m:ℝ))*(K*a^(2/3:ℝ)*paperPhi cstar (1/2) a) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ((5*(m:ℝ))*K)*(a^(2/3:ℝ)*paperPhi cstar (1/2) a) := by ring
    _ ≤ ((5*(m:ℝ))*K)*(Real.exp (cstar*Real.sqrt (Real.log R)/2)*b^(2/3:ℝ)*paperPhi cstar (1/2) b) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ = _ := by dsimp [Kout]; ring

end PrimeSquares
