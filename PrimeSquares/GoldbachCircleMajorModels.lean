import PrimeSquares.GoldbachMajorModelRegularity

set_option autoImplicit false
open Finset MeasureTheory Metric
open scoped ENNReal
namespace PrimeSquares

instance goldbachRatDenNeZero (r : ℚ) : NeZero r.den := ⟨r.den_pos.ne'⟩

noncomputable def goldbachArcModel (N : ℕ) (R : ℝ) (f : ℚ→ℝ→ℂ) (θ : PrimeCircle) : ℂ :=
  ∑ r∈sourceRationalCenters R,(closedBall ((r:ℝ):PrimeCircle) (R/(N:ℝ)^2)).indicator
    (fun η => f r (goldbachArcCoordinate r η)) θ

theorem goldbachArcModel_stronglyMeasurable (N : ℕ) (R : ℝ) (f : ℚ→ℝ→ℂ)
    (hf : ∀ r∈sourceRationalCenters R,StronglyMeasurable (f r)) :
    StronglyMeasurable (goldbachArcModel N R f) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro r hr
  exact ((hf r hr).comp_measurable (goldbachArcCoordinate_measurable r)).indicator measurableSet_closedBall

theorem goldbachArcModel_norm_bound (N : ℕ) (R : ℝ) (f : ℚ→ℝ→ℂ) (B : ℚ→ℝ)
    (hf : ∀ r∈sourceRationalCenters R,∀ γ,‖f r γ‖≤B r) (θ : PrimeCircle) :
    ‖goldbachArcModel N R f θ‖≤∑ r∈sourceRationalCenters R,B r := by
  classical
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro r hr
  by_cases hθ : θ∈closedBall ((r:ℝ):PrimeCircle) (R/(N:ℝ)^2)
  · rw [Set.indicator_of_mem hθ]
    exact hf r hr _
  · rw [Set.indicator_of_notMem hθ,norm_zero]
    exact (norm_nonneg (f r 0)).trans (hf r hr 0)

theorem goldbachArcModel_memLp (N : ℕ) (R : ℝ) (f : ℚ→ℝ→ℂ) (B : ℚ→ℝ)
    (hf : ∀ r∈sourceRationalCenters R,StronglyMeasurable (f r))
    (hbound : ∀ r∈sourceRationalCenters R,∀ γ,‖f r γ‖≤B r) (p : ℝ≥0∞) :
    MemLp (goldbachArcModel N R f) p AddCircle.haarAddCircle :=
  MemLp.of_bound (goldbachArcModel_stronglyMeasurable N R f hf).aestronglyMeasurable
    (∑ r∈sourceRationalCenters R,B r) (Filter.Eventually.of_forall (goldbachArcModel_norm_bound N R f B hbound))

theorem goldbachArcModel_on_arc (N : ℕ) (hN : 1≤N) {R : ℝ} (hR : 1≤R)
    (hsep : 2*R^3<(N:ℝ)^2) (f : ℚ→ℝ→ℂ) (r : ℚ)
    (hr : r∈sourceRationalCenters R) (θ : PrimeCircle)
    (hθ : θ∈closedBall ((r:ℝ):PrimeCircle) (R/(N:ℝ)^2)) :
    goldbachArcModel N R f θ=f r (goldbachArcCoordinate r θ) := by
  classical
  unfold goldbachArcModel
  rw [sum_eq_single r]
  · exact Set.indicator_of_mem hθ _
  · intro s hs hne
    apply Set.indicator_of_notMem
    intro hθs
    have hd := goldbach_major_balls_disjoint N hN hR hsep hs hr hne
    exact Set.disjoint_left.mp hd hθs hθ
  · intro hn
    exact (hn hr).elim

noncomputable def goldbachSquareMajorModel (N : ℕ) (R U : ℝ) : PrimeCircle→ℂ :=
  goldbachArcModel N R (fun r γ => principalSquareSum r.den (-(r.num:ZMod r.den))*goldbachSquareIntegral U γ)

noncomputable def goldbachProgressionMajorModel (N ℓ k a : ℕ) (R W : ℝ) : PrimeCircle→ℂ :=
  goldbachArcModel N R (fun r γ => goldbachLinearMajorModel N ℓ k r.den a r.num W γ)

theorem goldbach_square_model_norm_euclidean {U : ℝ} (hU : 2≤U) (r : ℚ) (γ : ℝ) :
    ‖principalSquareSum r.den (-(r.num:ZMod r.den))*goldbachSquareIntegral U γ‖≤U/Real.log 2 := by
  rw [norm_mul]
  exact (mul_le_mul (norm_principalSquareSum_le_one r.den _) (goldbachSquareIntegral_norm hU γ)
    (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem goldbachSquareMajorModel_memLp (N : ℕ) (R : ℝ) {U : ℝ} (hU : 2≤U) (p : ℝ≥0∞) :
    MemLp (goldbachSquareMajorModel N R U) p AddCircle.haarAddCircle :=
  goldbachArcModel_memLp N R _ (fun _ => U/Real.log 2)
    (fun _ _ => stronglyMeasurable_const.mul (goldbachSquareIntegral_stronglyMeasurable U))
    (fun r _ γ => goldbach_square_model_norm_euclidean hU r γ) p

theorem goldbachProgressionMajorModel_memLp (N ℓ k a : ℕ) (hℓ : 0<ℓ) (R : ℝ)
    {W : ℝ} (hW : 2≤W) (hX : 2≤(N:ℝ)^2/ℓ) (p : ℝ≥0∞) :
    MemLp (goldbachProgressionMajorModel N ℓ k a R W) p AddCircle.haarAddCircle := by
  apply goldbachArcModel_memLp N R _
    (fun r => ‖upsilon r.den k (a:ℤ) (-((r.num:ZMod r.den)*(ℓ:ZMod r.den)))/(k.totient:ℂ)‖*
      (W/Real.log 2)) _ _ p
  · intro r _
    exact stronglyMeasurable_const.mul (goldbachLinearSourceIntegral_stronglyMeasurable N ℓ hℓ W)
  · intro r _ γ
    change ‖(upsilon r.den k (a:ℤ) (-((r.num:ZMod r.den)*(ℓ:ZMod r.den)))/(k.totient:ℂ))*
      goldbachLinearSourceIntegral N ℓ W γ‖≤_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (goldbachLinearSourceIntegral_norm N ℓ hℓ hW hX γ) (norm_nonneg _)

theorem goldbachSquareMajorModel_norm_on_major (N : ℕ) (hN : 1≤N) {R U : ℝ}
    (hR : 1≤R) (hsep : 2*R^3<(N:ℝ)^2) (hU : 2≤U) (hUN : U≤N)
    (θ : PrimeCircle) (hθ : θ∈GoldbachMajorArcs N R) :
    ‖goldbachSquareMajorModel N R U θ‖≤(N:ℝ)/Real.log 2 := by
  obtain ⟨r,hr,harc⟩ := (mem_goldbachMajorArcs N (by linarith : 0≤R) θ).mp hθ
  rw [goldbachSquareMajorModel,goldbachArcModel_on_arc N hN hR hsep _ r hr θ harc]
  exact (goldbach_square_model_norm_euclidean hU r _).trans
    (div_le_div_of_nonneg_right hUN (Real.log_pos (by norm_num)).le)

end PrimeSquares
