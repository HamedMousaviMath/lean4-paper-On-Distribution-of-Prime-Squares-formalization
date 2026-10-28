import PrimeSquares.SmoothCircleBourgainInput
import PrimeSquares.WeightedSmoothSourceOperator
import PrimeSquares.CanonicalLiftDenominatorBound
import PrimeSquares.DyadicAnnularScales
import PrimeSquares.DyadicAnnularFrequencyDecay
open Finset
open scoped lp
namespace PrimeSquares
theorem bourgain_weightedSource_projection {C : ℝ} (hC : 0≤C) (hB : SmoothCircleBourgainInput C)
    {M s : ℕ} (hM : 2≤M) (hs : 2≤s) (Γ : Finset ℚ)
    (hc : ∀ r∈Γ,r∈Set.Ico (0 : ℚ) 1)
    (hd : ∀ r∈Γ,(r.den : ℝ)≤(2 : ℝ)^(s+1))
    (hwide : (16 : ℝ)^s≤(M : ℝ)^2)
    (hsepScale : 16*((2 : ℝ)^(s+1))^2≤(M : ℝ)^2)
    (c : ℚ→ℂ) {A : ℝ} (hA : 0≤A) (hb : ∀ r∈Γ,‖c r‖≤A) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ=>ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j x,‖integerMultiplier (∑ r∈Γ,c r • circleAnnularSmoothProjection ((2 : ℕ)^j*M) s r) f x‖≤g x) ∧
      ‖g‖≤(C*circleFrequencyLogFactor Γ*A)*‖f‖ := by
  let D : ℝ := (2 : ℝ)^(s+1)
  have hDp : 0<D := by dsimp [D];positivity
  have hD1 : 1≤D := by dsimp [D];exact one_le_pow₀ (by norm_num)
  have hδ : 0<1/D^2 := by positivity
  have hδ1 : 1/D^2≤1 := (div_le_one (by positivity : 0<D^2)).mpr (by nlinarith)
  have hsep : PeriodicFrequencySeparated Γ (1/D^2) := by
    intro r hr t ht hne k
    exact canonical_lift_denominator_bound (hc r hr) (hc t ht) hne (hd r hr) (hd t ht) k
  have hMr : (2 : ℝ)≤M := by exact_mod_cast hM
  have hfour : (4 : ℝ)≤(M : ℝ)^2 := by nlinarith
  have hstart : 16≤(M : ℝ)^2*(1/D^2) := by
    rw [mul_one_div]
    exact (le_div_iff₀ (by positivity : 0<D^2)).mpr hsepScale
  let F := integerMultiplier (weightedSourceCutoff Γ s c) f
  obtain ⟨g,hg,ht,hn⟩ := smoothCircleBourgain_countable hC hB Γ hc hδ hδ1 hsep
    ((M : ℝ)^2) hfour hstart F
  refine ⟨g,hg,?_,?_⟩
  · intro j x
    have hNj := dyadic_annular_scale_lower hM j
    have hNreal : (2 : ℝ)≤((2 : ℕ)^j*M : ℕ) := by exact_mod_cast hNj
    have ha : 1≤(((2 : ℕ)^j*M : ℕ) : ℝ)^2 := by nlinarith
    have heScale : smoothCircleScale ((M : ℝ)^2) j=(((2 : ℕ)^j*M : ℕ) : ℝ)^2 := by
      rw [dyadic_square_scale]
      unfold smoothCircleScale
      ring
    have hsc : (16 : ℝ)^s≤(((2 : ℕ)^j*M : ℕ) : ℝ)^2 := by
      rw [←heScale]
      exact hwide.trans (smoothCircleScale_ge (sq_nonneg _) j)
    rw [weightedSmoothSource_operator hNj hs Γ hc hd c ha hsc f]
    have he : unweightedSmoothCircleFamily Γ ((M : ℝ)^2) hfour j=
        ∑ r∈Γ,circleSmoothCutoff ((((2 : ℕ)^j*M : ℕ) : ℝ)^2) ha r := by
      unfold unweightedSmoothCircleFamily
      simp only [heScale]
    simpa only [he] using ht j x
  · have hF : ‖F‖≤A*‖f‖ := weightedSourceCutoff_input_norm hs Γ hc hd c hA hb f
    exact hn.trans ((mul_le_mul_of_nonneg_left hF
      (mul_nonneg hC (circleFrequencyLogFactor_nonneg Γ))).trans_eq (by ring))
end PrimeSquares
