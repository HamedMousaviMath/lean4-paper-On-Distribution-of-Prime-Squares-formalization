import PrimeSquares.PositiveAverageMaximum
import PrimeSquares.DyadicLayerGaugeCost

open Finset
namespace PrimeSquares

/-- A reusable hypothesis for the general layer-cake implication. It is
not an independent analytic input for the actual prime-square theorem. -/
def PositiveRestrictedGauge (A : PositiveAverageFamily) (C R : ℝ) : Prop :=
  ∀ F : Finset ℤ,∀ t : ℝ,1≤t →
    TestedDistributionBound (positiveMaximal A (finiteIndicator F)) (1/t)
      (R*(F.card : ℝ)*nearOnePsi C t)

theorem finiteDistribution_positive_mul (D : Finset ℤ) (g : ℤ → ℝ)
    {c a : ℝ} (hc : 0<c) :
    finiteDistribution D (fun x => c*g x) (c*a)=finiteDistribution D g a := by
  classical
  unfold finiteDistribution
  congr 2
  ext x
  simp only [mem_filter,mul_lt_mul_iff_right₀ hc]

theorem positiveRestricted_to_truncated_modular (A : PositiveAverageFamily) {C R : ℝ}
    (hC : 0≤C) (hR : 0≤R) (H : PositiveRestrictedGauge A C R)
    (F : Finset ℤ) (f : ℤ → ℂ) (hf : ∀ x,x∉F → f x=0)
    {level : ℝ} (hl : 0<level) :
    TestedDistributionBound (positiveMaximal A f) level
      ((R*layerGaugeConstant C (2*A.mass))*
        ∑ x∈F.filter (fun x => level/(2*A.mass)<‖f x‖),nearOnePsi (9*C+4) (‖f x‖/level)) := by
  classical
  let K := 2*A.mass
  let u := fun x => K*‖f x‖/level
  let I := functionLayerIndices F u
  let E := functionLayer F u
  let c := fun j : ℕ => (2 : ℝ)^(j+1)*level/K
  let b := fun j : ℕ => 1/(4*(2 : ℝ)^j*((j : ℝ)+1)^2)
  have hK : 2≤K := by dsimp [K];linarith [A.mass_one_le]
  have hK0 : 0<K := by linarith
  have hc : ∀ j,0<c j := fun j => by dsimp [c];positivity
  have hb : ∀ j,0<b j := fun j => by dsimp [b];positivity
  have hbudget : (∑ j∈I,c j*b j)≤level/2 := by
    have he (j : ℕ) : c j*b j=(level/(2*K))*(1/((j : ℝ)+1)^2) := by
      dsimp [c,b]
      rw [pow_succ]
      field_simp
      ring
    simp_rw [he]
    rw [←mul_sum]
    calc
      _ ≤ (level/(2*K))*2 := mul_le_mul_of_nonneg_left (finite_inverse_square_sum I) (by positivity)
      _ = level/K := by ring
      _ ≤ level/2 := div_le_div_of_nonneg_left hl.le (by norm_num) hK
  have hmajor (x : ℤ) : positiveMaximal A f x≤level/2+
      ∑ j∈I,c j*positiveMaximal A (finiteIndicator (E j)) x := by
    have h := positiveMaximal_layer_majorization A I E c (fun j _ => (hc j).le)
      (show 0≤level/K by positivity) f (functionLayer_majorization F f hf hK0 hl) x
    have he : A.mass*(level/K)=level/2 := by
      dsimp [K]
      field_simp [ne_of_gt (show 0<A.mass by linarith [A.mass_one_le])]
    simpa only [he] using h
  intro D
  have hdist : finiteDistribution D (positiveMaximal A f) level≤
      finiteDistribution D (fun x => ∑ j∈I,c j*positiveMaximal A (finiteIndicator (E j)) x)
        (∑ j∈I,c j*b j) := by
    apply Nat.cast_le.mpr
    apply card_le_card
    intro x hx
    obtain ⟨hx,ht⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hx,by have := hmajor x;nlinarith⟩
  have hsum := finiteDistribution_finite_sum D I
    (fun j x => c j*positiveMaximal A (finiteIndicator (E j)) x) (fun j => c j*b j)
  calc
    _ ≤ ∑ j∈I,finiteDistribution D (fun x => c j*positiveMaximal A (finiteIndicator (E j)) x) (c j*b j) :=
      hdist.trans hsum
    _ = ∑ j∈I,finiteDistribution D (positiveMaximal A (finiteIndicator (E j))) (b j) :=
      sum_congr rfl (fun j _ => finiteDistribution_positive_mul _ _ (hc j))
    _ ≤ ∑ j∈I,R*(E j).card*nearOnePsi C (4*(2 : ℝ)^j*((j : ℝ)+1)^2) := by
      apply sum_le_sum
      intro j hj
      exact H (E j) _ (by
        have h2 : (1 : ℝ)≤(2 : ℝ)^j := one_le_pow₀ (by norm_num)
        have hj0 : 0≤(j : ℝ) := Nat.cast_nonneg j
        nlinarith [sq_nonneg (j : ℝ)]) D
    _ = R*∑ j∈I,(E j).card*nearOnePsi C (4*(2 : ℝ)^j*((j : ℝ)+1)^2) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      ring
    _ ≤ R*(layerGaugeConstant C K*∑ x∈F.filter (fun x => level/K<‖f x‖),
        nearOnePsi (9*C+4) (‖f x‖/level)) :=
      mul_le_mul_of_nonneg_left (functionLayer_gauge_sum F f hC hK hl) hR
    _ = _ := by ring

end PrimeSquares
