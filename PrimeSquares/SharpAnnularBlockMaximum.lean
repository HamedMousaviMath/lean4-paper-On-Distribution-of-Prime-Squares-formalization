import PrimeSquares.ThresholdCoefficientAmplitudes
import PrimeSquares.ThresholdAnnularSource
import PrimeSquares.WeightedAnnularTruncationMaximum
import PrimeSquares.CircleEnergyMaximalWitness
import PrimeSquares.CircleRationalCollarEnergy
import PrimeSquares.SourceDyadicDenominatorBounds

open Finset
open scoped lp
namespace PrimeSquares

theorem sharpCollar_block_maximum {M s : ℕ} (hM : 2 ≤ M) (Γ : Finset ℚ)
    (hcan : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) (hlog : ∀ r ∈ Γ,Nat.log2 r.den=s)
    {A B Q W : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hQ : 0<Q) (hW : 0<W)
    (hL : 2 ≤ Real.log Q) (d : ℚ → ℕ) (hd : ∀ r ∈ Γ,0<d r)
    (hscale : ∀ r ∈ Γ,(r.den : ℝ)/W=(d r : ℝ)*B/Q)
    (hsmall : ∀ r ∈ Γ,(r.den : ℝ) ≤ W) (c : ℚ → ℂ)
    (hc : ∀ r ∈ Γ,‖c r‖ ≤ A*(d r : ℝ)^(-(1/2 : ℝ))*conductorRho (d r))
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (R : ℕ → ℝ) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (rationalCollarBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R j))
        ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) W (fun _ => β j) c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ ((192/Real.pi)*sharpThresholdAmplitude A B Q*
        relativeCutoffProfile (1/4) ((2 : ℝ)^s/W))*‖f‖ := by
  classical
  let D := sharpThresholdAmplitude A B Q
  have hD : 0 ≤ D := sharpThresholdAmplitude_nonneg hA (by linarith) hQ.le
  have hprof := relativeCutoffProfile_nonneg (δ := (1/4 : ℝ)) (show 0 ≤ (2 : ℝ)^s/W by positivity)
  by_cases he : Γ=∅
  · refine ⟨0,by simp,?_,?_⟩
    · intro j x
      simp only [he,filter_empty,rationalCollarBlock,sum_empty,integerMultiplier_zero,
        zero_apply,lp.coeFn_zero,Pi.zero_apply,norm_zero,le_refl]
    · simpa only [norm_zero] using mul_nonneg (mul_nonneg
        (mul_nonneg (by positivity : (0 : ℝ) ≤ 192/Real.pi) hD) hprof) (norm_nonneg f)
  obtain ⟨r,hr⟩ := nonempty_iff_ne_empty.mpr he
  have bounds (r : ℚ) (hr : r ∈ Γ) : (2 : ℝ)^s ≤ (r.den : ℝ) ∧ (r.den : ℝ)<(2 : ℝ)^(s+1) := by
    simpa only [hlog r hr] using sourceDyadicRationalCenters_den_bounds
      ((mem_sourceDyadicRationalCenters _ _).mpr ⟨hcan r hr,rfl⟩)
  let t : ℝ := (2 : ℝ)^s/W
  have ht : 0<t := by dsimp [t];positivity
  have ht1 : t ≤ 1 := (div_le_one hW).mpr ((bounds r hr).1.trans (hsmall r hr))
  let b : ℝ := D*t^(-(1/2 : ℝ))
  have hb : 0 ≤ b := by dsimp [b];positivity
  have hcoeff (r : ℚ) (hr : r ∈ Γ) : ‖c r‖ ≤ b :=
    threshold_small_block_amplitude (d r) (hd r hr) hA hB hQ hL (c r) (hc r hr)
      (hscale r hr) ((div_le_one hW).mpr (hsmall r hr)) ht
      (div_le_div_of_nonneg_right (bounds r hr).1 hW.le)
  let cc := fun j r => if (r.den : ℝ) ≤ R j then c r else 0
  have hcc : ∀ j,∀ r ∈ Γ,‖cc j r‖ ≤ b := by
    intro j r hr
    dsimp [cc]
    split_ifs
    · exact hcoeff r hr
    · simpa only [norm_zero] using hb
  have hden : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1) := fun r hr => (bounds r hr).2.le
  let n := fun j => rationalCollarBlock Γ ((2 : ℕ)^j*M)
    (by have h := dyadic_annular_scale_lower hM j;omega) W (fun _ => β j) (cc j)
  obtain ⟨g,_,hg,htg,hng⟩ := circle_energy_maximal_witness n
    (by dsimp [b];positivity : 0 ≤ 96*b*(2 : ℝ)^(s+1)/(Real.pi*W))
    (rationalCollarBlock_finite_energy hM Γ s hcan hlog hW hden
      (fun j _ => β j) (fun j _ _ => hβ0 j) (fun j _ _ => hβ1 j) cc hcc) f
  refine ⟨g,hg,?_,hng.trans ?_⟩
  · intro j x
    rw [rationalCollarBlock_truncation]
    exact htg j x
  · apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
    have hh := small_amplitude_profile ht ht1
    calc
      _=(96/Real.pi)*D*(t^(-(1/2 : ℝ))*(2*t)) := by dsimp [b,t];rw [pow_succ];field_simp
      _ ≤ (96/Real.pi)*D*(2*relativeCutoffProfile (1/4) t) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by ring

theorem sharpLarge_block_maximum {C : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C)
    {M s : ℕ} (hM : 2 ≤ M) (Γ : Finset ℚ)
    (hcan : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) (hlog : ∀ r ∈ Γ,Nat.log2 r.den=s)
    {A B Q W : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hQ : 0<Q) (hW : 16 ≤ W)
    (hL : 2 ≤ Real.log Q) (hSlope : gaussThresholdSlope (Real.log Q) ≤ 1/4)
    (d : ℚ → ℕ) (hd : ∀ r ∈ Γ,0<d r)
    (hscale : ∀ r ∈ Γ,(r.den : ℝ)/W=(d r : ℝ)*B/Q)
    (hlarge : ∀ r ∈ Γ,W<(r.den : ℝ)) (c : ℚ → ℂ)
    (hc : ∀ r ∈ Γ,‖c r‖ ≤ A*(d r : ℝ)^(-(1/2 : ℝ))*conductorRho (d r))
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (R : ℕ → ℝ) (hR : ∀ j,0 ≤ R j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (weightedAnnularSourceBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R j))
        ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (annularTruncationConstant C*sharpThresholdAmplitude A B Q*(2 : ℝ)^(1/4 : ℝ)*
        ((s : ℝ)+1)^3*relativeCutoffProfile (1/4) ((2 : ℝ)^s/W))*‖f‖ := by
  classical
  let D := sharpThresholdAmplitude A B Q
  have hD : 0 ≤ D := sharpThresholdAmplitude_nonneg hA (by linarith) hQ.le
  have hK := annularTruncationConstant_nonneg hC
  have hWp : 0<W := by linarith
  let t : ℝ := (2 : ℝ)^s/W
  have ht : 0<t := by dsimp [t];positivity
  have hprof : 0 ≤ relativeCutoffProfile (1/4) t := relativeCutoffProfile_nonneg ht.le
  by_cases he : Γ=∅
  · refine ⟨0,by simp,?_,?_⟩
    · intro j x
      simp only [he,filter_empty,weightedAnnularSourceBlock,sum_empty,integerMultiplier_zero,
        zero_apply,lp.coeFn_zero,Pi.zero_apply,norm_zero,le_refl]
    · simp only [norm_zero]
      change 0 ≤ (annularTruncationConstant C*D*(2 : ℝ)^(1/4 : ℝ)*((s : ℝ)+1)^3*
        relativeCutoffProfile (1/4) t)*‖f‖
      positivity
  obtain ⟨r,hr⟩ := nonempty_iff_ne_empty.mpr he
  have bounds (r : ℚ) (hr : r ∈ Γ) : (2 : ℝ)^s ≤ (r.den : ℝ) ∧ (r.den : ℝ)<(2 : ℝ)^(s+1) := by
    simpa only [hlog r hr] using sourceDyadicRationalCenters_den_bounds
      ((mem_sourceDyadicRationalCenters _ _).mpr ⟨hcan r hr,rfl⟩)
  have hs : 4 ≤ s := by
    by_contra hn
    have hp : (2 : ℝ)^(s+1) ≤ (2 : ℝ)^4 := pow_le_pow_right₀ (by norm_num) (by omega : s+1 ≤ 4)
    have hh := (bounds r hr).2
    norm_num at hp
    linarith [hlarge r hr]
  have htlow : 1/2 ≤ t := by
    have hh := (bounds r hr).2
    rw [pow_succ] at hh
    have hratio : W<2*(2 : ℝ)^s := by linarith [hlarge r hr]
    dsimp [t]
    exact (le_div_iff₀ hWp).mpr (by linarith)
  let b := D*min 1 (t^(-(1/4 : ℝ)))
  have hb : 0 ≤ b := by dsimp [b];positivity
  have hcoeff (r : ℚ) (hr : r ∈ Γ) : ‖c r‖ ≤ b :=
    threshold_large_block_amplitude (d r) (hd r hr) hA hB hQ hL hSlope (c r) (hc r hr)
      (hscale r hr) ((one_le_div hWp).mpr (hlarge r hr).le) ht
      (div_le_div_of_nonneg_right (bounds r hr).1 hWp.le)
  obtain ⟨g,hg,htg,hng⟩ := weightedAnnular_truncation_maximum hC hBourgain hM hs Γ hcan
    (fun r hr => (bounds r hr).2.le) β hβ0 hβ1 c hb hcoeff f
  refine ⟨g,hg,(fun j x => htg j (R j) (hR j) x),hng.trans ?_⟩
  have hh := large_amplitude_profile htlow
  have hprod := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ annularTruncationConstant C*D*((s : ℝ)+1)^3*‖f‖ by positivity)
  dsimp [b] at hng ⊢
  convert hprod using 1 <;> ring

end PrimeSquares
