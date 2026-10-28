import PrimeSquares.CircleGaussAnnularDecomposition
import PrimeSquares.OrdinaryCircleHighCollar
import PrimeSquares.LargeOrdinaryCircleTerm
import PrimeSquares.LargeCircleExceptionalHigh
import PrimeSquares.FiniteExceptionalHigh
import PrimeSquares.WeightedAnnularLargeStartMaximum

open Finset
namespace PrimeSquares

noncomputable def circleThresholdAnnular (N : ℕ) (hN : 1 ≤ N) (β W : ℝ) (r : ℚ) : C(PrimeCircle,ℂ) :=
  if (r.den : ℝ) ≤ W then circleAnnularCollar N hN β (r.den : ℝ) W (Nat.log2 r.den) (r : ℝ)
  else circleAnnularSource N hN β (Nat.log2 r.den) r

noncomputable def thresholdAnnularBlock (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (β W : ℝ) (c : ℚ → ℂ) : C(PrimeCircle,ℂ) := ∑ r ∈ Γ,c r • circleThresholdAnnular N hN β W r

theorem circleHighTerm_threshold_ordinary (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (hq₀ : 0<q₀)
    {Q B : ℝ} (hQ : 0<Q) (hB : 0<B) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (β : ℝ) (r : ℚ) : circleHighTerm N hN q₀ Q B χ (fun _ => 0) β r=
      rationalPrincipalGauss r • circleThresholdAnnular N hN 1 Q r := by
  classical
  by_cases hr : (r.den : ℝ) ≤ Q
  · rw [circleThresholdAnnular,ite_eq_left hr]
    exact circleHighTerm_ordinary_collar N hN q₀ hq₀ hQ hB χ β r hr
  · rw [circleThresholdAnnular,ite_eq_right hr,circleHighTerm_large_ordinary N hN q₀ Q B χ β r (lt_of_not_ge hr),
      circleRationalModel_annular_decomposition]
    simp [rationalExceptionalCoefficient]
    ext θ
    simp only [ContinuousMap.smul_apply,smul_eq_mul,zero_mul,ContinuousMap.zero_apply]

theorem circleExceptionalHigh_threshold (N : ℕ) (hN : 1 ≤ N) {q₀ : ℕ} (hq₀ : 0<q₀)
    {Q B : ℝ} (hQ : 0<Q) (hB : 0<B) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) : circleExceptionalHigh N hN q₀ Q B χ κ β r=
      (κ r*rationalTwistedGauss r (χ r)) • circleThresholdAnnular N hN β (Q*(q₀ : ℝ)/B) r := by
  classical
  by_cases hr : (r.den : ℝ) ≤ Q*(q₀ : ℝ)/B
  · rw [circleThresholdAnnular,ite_eq_left hr]
    exact circleExceptionalHigh_collar N hN hq₀ hQ hB χ κ β r hr
  · rw [circleThresholdAnnular,ite_eq_right hr,circleExceptionalHigh_large N hN hq₀ hQ hB χ κ β r (lt_of_not_ge hr),
      circleRationalModel_annular_decomposition,circleRationalModel_annular_decomposition]
    simp [rationalExceptionalCoefficient,rationalTwistedGauss,mul_comm]
    ext θ
    simp only [ContinuousMap.smul_apply,smul_eq_mul,zero_mul,ContinuousMap.zero_apply]

theorem circleHighModel_threshold_decomposition (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    {q₀ : ℕ} (hq₀ : 0<q₀) {Q B : ℝ} (hQ : 0<Q) (hB : 0<B)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) :
    circleHighModel Γ N hN q₀ Q B χ κ β=thresholdAnnularBlock Γ N hN 1 Q rationalPrincipalGauss-
      thresholdAnnularBlock Γ N hN β (Q*(q₀ : ℝ)/B) (fun r => κ r*rationalTwistedGauss r (χ r)) := by
  rw [circleHighModel_ordinary_sub_exceptional]
  congr 1
  · exact sum_congr rfl (fun r _ => circleHighTerm_threshold_ordinary N hN q₀ hq₀ hQ hB χ β r)
  · exact sum_congr rfl (fun r _ => circleExceptionalHigh_threshold N hN hq₀ hQ hB χ κ β r)

theorem thresholdAnnularBlock_split (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (β W : ℝ) (c : ℚ → ℂ) :
    thresholdAnnularBlock Γ N hN β W c=
      rationalCollarBlock (Γ.filter (fun r => (r.den : ℝ) ≤ W)) N hN W (fun _ => β) c+
      ∑ r ∈ Γ.filter (fun r => W<(r.den : ℝ)),c r • circleAnnularSource N hN β (Nat.log2 r.den) r := by
  classical
  simp only [thresholdAnnularBlock,circleThresholdAnnular,smul_ite,sum_ite,rationalCollarBlock,not_le]

theorem rationalCollarBlock_truncation (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (β W R : ℝ) (c : ℚ → ℂ) :
    rationalCollarBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R)) N hN W (fun _ => β) c=
      rationalCollarBlock Γ N hN W (fun _ => β) (fun r => if (r.den : ℝ) ≤ R then c r else 0) := by
  classical
  simp only [rationalCollarBlock,sum_filter]
  apply sum_congr rfl
  intro r _
  split_ifs
  · rfl
  · ext θ
    simp only [ContinuousMap.zero_apply,ContinuousMap.smul_apply,smul_eq_mul,zero_mul]

end PrimeSquares
