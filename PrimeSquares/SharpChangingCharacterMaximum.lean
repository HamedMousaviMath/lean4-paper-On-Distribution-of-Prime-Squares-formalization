import PrimeSquares.SharpConductorMaximalRate
import PrimeSquares.CircleHighLowOperators

open Finset
open scoped lp
namespace PrimeSquares

theorem sharpChangingCharacter_maximum {C : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C) :
    ∃ Q₀ D : ℝ,16 ≤ Q₀ ∧ 0<D ∧ ∀ Q : ℝ,Q₀ ≤ Q → 2 ≤ Real.log Q →
    gaussThresholdSlope (Real.log Q) ≤ 1/4 → ∀ (M : ℕ) (hM : 2 ≤ M)
      (q : ℕ → ℕ),(∀ i,2^i ≤ q i) → ∀ (χ : ∀ i,DirichletCharacter ℂ (q i)),
      (∀ i,(χ i).IsQuadratic) → ∀ (β : ℕ → ℝ),(∀ j,0 ≤ β j) → (∀ j,β j ≤ 1) →
    ∀ (R : ℕ → ℝ),(∀ j,0 ≤ R j) → ∀ (σ : ℕ → ℕ) (active : ℕ → Bool) (f : ℓ²(ℤ,ℂ)),
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖circleHighOperator (sourceRationalCenters (R j)) ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) (q (σ j)) Q (conductorMajorant (q (σ j)))
        (sourceInducedCharacter (q (σ j)) (χ (σ j))) (sourceExceptionalSelector (q (σ j)) (active j))
        (β j) f x‖ ≤ g x) ∧ ‖g‖ ≤ (D*sharpHighMaximalRate Q)*‖f‖ := by
  classical
  obtain ⟨Q₀,H,hQ₀,hH,hExc⟩ := sharpExceptional_conductor_rate hC hBourgain
  have hK := sharpThresholdMaximalConstant_nonneg hC
  have hratio := (dyadic_decay_ratio (by norm_num : (0 : ℝ)<1/50)).2
  have hinv : 0<(1-(2 : ℝ)^(-(1/50 : ℝ)))⁻¹ := inv_pos.mpr (by linarith)
  let D := 1+4*sharpThresholdMaximalConstant C+H*(1-(2 : ℝ)^(-(1/50 : ℝ)))⁻¹
  refine ⟨Q₀,D,hQ₀,by dsimp [D];positivity,?_⟩
  intro Q hQ hL hSlope M hM q hclass χ hχ β hβ0 hβ1 R hR σ active f
  have hQ16 : 16 ≤ Q := hQ₀.trans hQ
  have hQ1 : 1 ≤ Q := by linarith
  have hQp : 0<Q := by linarith
  have hRate := sharpHighMaximalRate_nonneg hQ1
  have inst : ∀ i,NeZero (q i) := fun i => ⟨(conductor_class_positive q hclass i).ne'⟩
  obtain ⟨gO,hgO,htO,hnO⟩ := sharpOrdinary_rate_maximum hC hBourgain hM hQ16 hL hSlope R hR f
  have hex (i : ℕ) := hExc Q hQ hL hSlope M hM (q i) (χ i) (hχ i) β hβ0 hβ1 R hR f
  choose G hG0 hGt hGn using hex
  let T := fun j => circleHighOperator (sourceRationalCenters (R j)) ((2 : ℕ)^j*M)
    (by have h := dyadic_annular_scale_lower hM j;omega) (q (σ j)) Q (conductorMajorant (q (σ j)))
    (sourceInducedCharacter (q (σ j)) (χ (σ j))) (sourceExceptionalSelector (q (σ j)) (active j)) (β j)
  have hpoint (j : ℕ) (x : ℤ) : ‖T j f x‖ ≤ gO x+G (σ j) x := by
    change ‖integerMultiplier (circleHighModel _ _ _ _ _ _ _ _ _) f x‖ ≤ _
    rw [circleHighModel_threshold_decomposition _ _ _ (conductor_class_positive q hclass (σ j)) hQp
      (lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le _ (conductor_class_positive q hclass (σ j)))),
      thresholdAnnularBlock_mask]
    cases ha : active j
    · simp only [Bool.false_eq_true,ite_false,sub_zero]
      exact (htO j x).trans (le_add_of_nonneg_right (hG0 (σ j) x))
    · simp only [ite_true]
      rw [integerMultiplier_sub,_root_.sub_apply,lp.coeFn_sub,Pi.sub_apply]
      exact (norm_sub_le _ _).trans (add_le_add (htO j x) (hGt (σ j) j x))
  have hD0 : 0 ≤ D := by dsimp [D];positivity
  apply finite_family_countable_maximum (fun j => T j f) (by positivity)
  intro J
  let S := J.image σ
  let g := gO+∑ i ∈ S,G i
  have hnSum : (∑ i ∈ S,‖G i‖) ≤
      (H*sharpHighMaximalRate Q*‖f‖)*(1-(2 : ℝ)^(-(1/50 : ℝ)))⁻¹ := by
    calc
      _ ≤ ∑ i ∈ S,(H*(q i : ℝ)^(-(1/50 : ℝ))*sharpHighMaximalRate Q)*‖f‖ := sum_le_sum (fun i _ => hGn i)
      _ = (H*sharpHighMaximalRate Q*‖f‖)*∑ i ∈ S,(q i : ℝ)^(-(1/50 : ℝ)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (finite_conductor_class_linear_budget (by norm_num : (0 : ℝ)<1/50) q hclass S) (by positivity)
  refine ⟨g,?_,?_,?_⟩
  · intro x
    change 0 ≤ (gO+∑ i ∈ S,G i) x
    simpa only [lp.coeFn_add,Pi.add_apply,lp.coeFn_sum,Finset.sum_apply] using
      add_nonneg (hgO x) (sum_nonneg (fun i _ => hG0 i x))
  · intro j hj x
    have hs : σ j ∈ S := mem_image.mpr ⟨j,hj,rfl⟩
    have hh := single_le_sum (fun i _ => hG0 i x) hs
    have hn := (hpoint j x).trans (add_le_add (le_refl (gO x)) hh)
    simpa only [g,lp.coeFn_add,Pi.add_apply,lp.coeFn_sum,Finset.sum_apply] using hn
  · have hb : (4*sharpThresholdMaximalConstant C+H*(1-(2 : ℝ)^(-(1/50 : ℝ)))⁻¹) ≤ D := by dsimp [D];linarith
    calc
      _ ≤ ‖gO‖+‖∑ i ∈ S,G i‖ := norm_add_le _ _
      _ ≤ (4*sharpThresholdMaximalConstant C*sharpHighMaximalRate Q)*‖f‖+∑ i ∈ S,‖G i‖ :=
        add_le_add hnO (norm_sum_le _ _)
      _ ≤ (4*sharpThresholdMaximalConstant C*sharpHighMaximalRate Q)*‖f‖+
          (H*sharpHighMaximalRate Q*‖f‖)*(1-(2 : ℝ)^(-(1/50 : ℝ)))⁻¹ := add_le_add (le_refl _) hnSum
      _ = ((4*sharpThresholdMaximalConstant C+H*(1-(2 : ℝ)^(-(1/50 : ℝ)))⁻¹)*sharpHighMaximalRate Q)*‖f‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hRate) (norm_nonneg f)

end PrimeSquares
