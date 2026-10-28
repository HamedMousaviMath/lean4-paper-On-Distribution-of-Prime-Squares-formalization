import PrimeSquares.InterpolationGeometry
import PrimeSquares.DyadicDenominatorPartition
import PrimeSquares.DyadicSparseSum
import PrimeSquares.SourceDyadicDenominatorBounds

open Finset
namespace PrimeSquares

noncomputable def relativeCutoffProfile (δ t : ℝ) : ℝ := min (t^δ) (t^(-δ))

theorem relativeCutoffProfile_nonneg {δ t : ℝ} (ht : 0 ≤ t) :
    0 ≤ relativeCutoffProfile δ t := le_min (Real.rpow_nonneg ht _) (Real.rpow_nonneg ht _)

theorem relativeCutoffProfile_dyadic {δ W q : ℝ} (hδ : 0 ≤ δ) (hW : 0 < W)
    {s : ℕ} (hlo : (2 : ℝ)^s ≤ q) (hhi : q ≤ (2 : ℝ)^(s+1)) :
    relativeCutoffProfile δ (q/W) ≤ interpolationWeight ((2 : ℝ)^δ) 1 δ δ W s := by
  have hq : 0 < q := lt_of_lt_of_le (by positivity) hlo
  have hbase : (2 : ℝ)^s/W ≤ q/W := div_le_div_of_nonneg_right hlo hW.le
  have hup : q/W ≤ 2*((2 : ℝ)^s/W) := by
    have h := div_le_div_of_nonneg_right hhi hW.le
    simpa only [pow_succ] using h.trans_eq (by ring)
  have hp : (q/W)^δ ≤ (2 : ℝ)^δ*((2 : ℝ)^s/W)^δ := by
    rw [←Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hup hδ
  have hn : (q/W)^(-δ) ≤ ((2 : ℝ)^s/W)^(-δ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hbase (neg_nonpos.mpr hδ)
  simpa only [relativeCutoffProfile,interpolationWeight,one_mul] using min_le_min hp hn

theorem rational_dyadic_profile_sum (Γ : Finset ℚ) (M : ℕ) (ξ : ℝ) (F : ℚ → ℂ)
    (w : ℕ → ℝ) (hw : ∀ s,0 ≤ w s)
    (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ M)
    (hzero : ∀ r ∈ Γ,sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ))=0 → F r=0)
    (hF : ∀ r ∈ Γ,‖F r‖ ≤ w (Nat.log2 r.den)) :
    ‖∑ r ∈ Γ,F r‖ ≤ 4*∑ s ∈ range (Nat.log2 M+1),w s := by
  classical
  rw [rational_dyadic_partition Γ M (fun r hr => (hΓ r hr).2) F]
  calc
    _ ≤ ∑ s ∈ range (Nat.log2 M+1),‖∑ r ∈ Γ.filter (fun r => Nat.log2 r.den=s),F r‖ := norm_sum_le _ _
    _ ≤ ∑ s ∈ range (Nat.log2 M+1),4*w s := by
      apply sum_le_sum
      intro s hs
      apply dyadic_sparse_sum_bound _ ξ s F (hw s)
      · intro r hr;exact (hΓ r (mem_filter.mp hr).1).1
      · intro r hr;exact (mem_filter.mp hr).2
      · intro r hr hz;exact hzero r (mem_filter.mp hr).1 hz
      · intro r hr
        simpa only [(mem_filter.mp hr).2] using hF r (mem_filter.mp hr).1
    _ = _ := (mul_sum _ _ _).symm

theorem rational_two_relative_cutoff_sum (Γ : Finset ℚ) (M : ℕ) (ξ : ℝ) (F : ℚ → ℂ)
    {δ W V A B : ℝ} (hδ : 0 < δ) (hW : 0 < W) (hV : 0 < V) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ M)
    (hzero : ∀ r ∈ Γ,sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ))=0 → F r=0)
    (hF : ∀ r ∈ Γ,‖F r‖ ≤ A*relativeCutoffProfile δ ((r.den : ℝ)/W)+
      B*relativeCutoffProfile δ ((r.den : ℝ)/V)) :
    ‖∑ r ∈ Γ,F r‖ ≤
      4*(A+B)*interpolationWeightConstant ((2 : ℝ)^δ) 1 δ δ := by
  classical
  let w := fun s => A*interpolationWeight ((2 : ℝ)^δ) 1 δ δ W s+
    B*interpolationWeight ((2 : ℝ)^δ) 1 δ δ V s
  have hnW := interpolationWeight_nonneg (a := δ) (b := δ)
    (show 0 ≤ (2 : ℝ)^δ by positivity) (by norm_num : (0 : ℝ) ≤ 1) hW
  have hnV := interpolationWeight_nonneg (a := δ) (b := δ)
    (show 0 ≤ (2 : ℝ)^δ by positivity) (by norm_num : (0 : ℝ) ≤ 1) hV
  have hw : ∀ s,0 ≤ w s := fun s => add_nonneg (mul_nonneg hA (hnW s)) (mul_nonneg hB (hnV s))
  have hb : ∀ r ∈ Γ,‖F r‖ ≤ w (Nat.log2 r.den) := by
    intro r hr
    have hm : r ∈ sourceDyadicRationalCenters (Nat.log2 r.den) :=
      (mem_sourceDyadicRationalCenters _ _).mpr ⟨(hΓ r hr).1,rfl⟩
    obtain ⟨hl,hu⟩ := sourceDyadicRationalCenters_den_bounds hm
    exact (hF r hr).trans (add_le_add
      (mul_le_mul_of_nonneg_left (relativeCutoffProfile_dyadic hδ.le hW hl hu.le) hA)
      (mul_le_mul_of_nonneg_left (relativeCutoffProfile_dyadic hδ.le hV hl hu.le) hB))
  have hsW := interpolationWeight_summable (show 0 ≤ (2 : ℝ)^δ by positivity) (by norm_num : (0 : ℝ) ≤ 1) hδ hW (a := δ)
  have hsV := interpolationWeight_summable (show 0 ≤ (2 : ℝ)^δ by positivity) (by norm_num : (0 : ℝ) ≤ 1) hδ hV (a := δ)
  have hsum : (∑ s ∈ range (Nat.log2 M+1),w s) ≤
      (A+B)*interpolationWeightConstant ((2 : ℝ)^δ) 1 δ δ := by
    simp only [w,sum_add_distrib,←mul_sum]
    have hWsum := (hsW.sum_le_tsum (range (Nat.log2 M+1)) (fun s _ => hnW s)).trans
      (interpolationWeight_tsum_le (by positivity) (by norm_num : (0 : ℝ) ≤ 1) hδ hδ hW)
    have hVsum := (hsV.sum_le_tsum (range (Nat.log2 M+1)) (fun s _ => hnV s)).trans
      (interpolationWeight_tsum_le (by positivity) (by norm_num : (0 : ℝ) ≤ 1) hδ hδ hV)
    exact (add_le_add (mul_le_mul_of_nonneg_left hWsum hA) (mul_le_mul_of_nonneg_left hVsum hB)).trans_eq (by ring)
  exact (rational_dyadic_profile_sum Γ M ξ F w hw hΓ hzero hb).trans
    ((mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring))

end PrimeSquares
