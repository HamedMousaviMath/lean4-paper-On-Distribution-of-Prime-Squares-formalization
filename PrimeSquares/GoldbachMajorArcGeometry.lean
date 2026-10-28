import PrimeSquares.GoldbachLinearMajorBV
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false
open Finset MeasureTheory Metric
open scoped ENNReal
namespace PrimeSquares

def GoldbachMajorArcs (N : ℕ) (R : ℝ) : Set PrimeCircle := (GoldbachMinorArcs N R)ᶜ

theorem goldbachMajorArcs_measurable (N : ℕ) (R : ℝ) :
    MeasurableSet (GoldbachMajorArcs N R) := (goldbachMinorArcs_measurable N R).compl

theorem mem_goldbachMajorArcs (N : ℕ) {R : ℝ} (hR : 0≤R) (θ : PrimeCircle) :
    θ∈GoldbachMajorArcs N R ↔ ∃ r∈sourceRationalCenters R,
      dist θ ((r:ℝ):PrimeCircle)≤R/(N:ℝ)^2 := by
  classical
  change (¬θ∈GoldbachMinorArcs N R)↔_
  rw [goldbach_minor_arcs_source_centres N hR θ]
  constructor
  · intro h
    by_contra hh
    apply h
    intro r hr
    exact lt_of_not_ge (fun hb => hh ⟨r,hr,hb⟩)
  · rintro ⟨r,hr,hb⟩ h
    exact (not_lt_of_ge hb) (h r hr)

theorem goldbach_major_arcs_union (N : ℕ) {R : ℝ} (hR : 0≤R) :
    GoldbachMajorArcs N R=⋃ r∈sourceRationalCenters R,
      closedBall ((r:ℝ):PrimeCircle) (R/(N:ℝ)^2) := by
  ext θ
  simp only [mem_goldbachMajorArcs N hR θ,Set.mem_iUnion,mem_closedBall,exists_prop]

theorem goldbach_circle_volume_eq_haar : (volume : Measure PrimeCircle)=AddCircle.haarAddCircle := by
  simpa only [ENNReal.ofReal_one,one_smul] using (AddCircle.volume_eq_smul_haarAddCircle (T:=(1:ℝ)))

theorem goldbach_major_ball_measure (x : PrimeCircle) (ε : ℝ) :
    AddCircle.haarAddCircle (closedBall x ε)≤ENNReal.ofReal (2*ε) := by
  rw [←goldbach_circle_volume_eq_haar,AddCircle.volume_closedBall]
  exact ENNReal.ofReal_le_ofReal (min_le_right _ _)

theorem goldbach_source_centres_card {R : ℝ} (hR : 1≤R) :
    ((sourceRationalCenters R).card:ℝ)≤4*R^2 := by
  have hn := canonicalRationalCenters_card ⌊R⌋₊
  have hc : ((sourceRationalCenters R).card:ℝ)≤((⌊R⌋₊:ℝ)+1)^2 := by exact_mod_cast hn
  have hf : (⌊R⌋₊:ℝ)≤R := Nat.floor_le (by linarith)
  have hp : ((⌊R⌋₊:ℝ)+1)^2≤(R+1)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  exact hc.trans (hp.trans (by nlinarith))

theorem goldbach_major_arcs_measure (N : ℕ) (hN : 1≤N) {R : ℝ} (hR : 1≤R) :
    (AddCircle.haarAddCircle (GoldbachMajorArcs N R)).toReal≤8*R^3/(N:ℝ)^2 := by
  have hnR : (0:ℝ)<N := by exact_mod_cast hN
  have hr0 : 0≤R := by linarith
  have hc := goldbach_source_centres_card hR
  have hb : AddCircle.haarAddCircle (GoldbachMajorArcs N R)≤
      ENNReal.ofReal (8*R^3/(N:ℝ)^2) := by
    rw [goldbach_major_arcs_union N hr0]
    calc
      _≤∑ r∈sourceRationalCenters R,AddCircle.haarAddCircle
        (closedBall ((r:ℝ):PrimeCircle) (R/(N:ℝ)^2)) := measure_biUnion_finset_le _ _
      _≤∑ _r∈sourceRationalCenters R,ENNReal.ofReal (2*(R/(N:ℝ)^2)) :=
        sum_le_sum (fun r _ => goldbach_major_ball_measure _ _)
      _=ENNReal.ofReal (((sourceRationalCenters R).card:ℝ)*(2*(R/(N:ℝ)^2))) := by
        rw [sum_const,nsmul_eq_mul,←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _≤ENNReal.ofReal ((4*R^2)*(2*(R/(N:ℝ)^2))) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hc (by positivity))
      _=ENNReal.ofReal (8*R^3/(N:ℝ)^2) := by congr 1;ring
  have hh := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hb
  simpa only [ENNReal.toReal_ofReal (by positivity : 0≤8*R^3/(N:ℝ)^2)] using hh

theorem goldbach_circle_ball_real_lift (r ξ ε : ℝ) :
    dist (ξ:PrimeCircle) (r:PrimeCircle)≤ε ↔ ∃ k : ℤ,|ξ+(k:ℝ)-r|≤ε := by
  change ξ∈((↑) : ℝ→PrimeCircle)⁻¹' closedBall (r:PrimeCircle) ε ↔_
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion]
  simp only [Set.mem_iUnion,mem_closedBall,Real.dist_eq,zsmul_eq_mul,mul_one]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨-k,?_⟩
    have he : ξ+((-k:ℤ):ℝ)-r=ξ-(r+(k:ℝ)) := by push_cast;ring
    simpa only [he] using hk
  · rintro ⟨k,hk⟩
    refine ⟨-k,?_⟩
    have he : ξ-(r+((-k:ℤ):ℝ))=ξ+(k:ℝ)-r := by push_cast;ring
    simpa only [he] using hk

theorem goldbach_major_balls_disjoint (N : ℕ) (hN : 1≤N) {R : ℝ} (hR : 1≤R)
    (hsep : 2*R^3<(N:ℝ)^2) :
    Set.PairwiseDisjoint (↑(sourceRationalCenters R):Set ℚ)
      (fun r => closedBall ((r:ℝ):PrimeCircle) (R/(N:ℝ)^2)) := by
  intro r hr s hs hne
  apply Set.disjoint_left.mpr
  intro θ hθr hθs
  obtain ⟨ξ,rfl⟩ := Quotient.exists_rep θ
  obtain ⟨k,hk⟩ := (goldbach_circle_ball_real_lift (r:ℝ) ξ (R/(N:ℝ)^2)).mp hθr
  obtain ⟨l,hl⟩ := (goldbach_circle_ball_real_lift (s:ℝ) ξ (R/(N:ℝ)^2)).mp hθs
  have hr' := (mem_sourceRationalCenters (by linarith : 0≤R) r).mp hr
  have hs' := (mem_sourceRationalCenters (by linarith : 0≤R) s).mp hs
  have hnR : (0:ℝ)<N := by exact_mod_cast hN
  have hrR : 0<R := by linarith
  have hw : 2*(R/(N:ℝ)^2)<1/R^2 := by
    rw [←mul_div_assoc,div_lt_div_iff₀ (sq_pos_of_pos hnR) (sq_pos_of_pos hrR)]
    nlinarith only [hsep]
  exact hne (canonicalLift_small_arc_unique hr'.1 hs'.1 hr'.2 hs'.2 hw hk hl).1

theorem goldbach_major_geometry_eventual {C : ℝ} (hC : 0≤C) :
    ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      1≤Real.log N ∧ 1≤(Real.log N)^C ∧
      2*((Real.log N)^C)^3<(N:ℝ)^2 ∧ (Real.log N)^C/(N:ℝ)^2<1/2 := by
  obtain ⟨N₀,hN₀,hbudget⟩ := goldbach_major_radius_eventual_budget (3*C) 0
  refine ⟨N₀,hN₀,?_⟩
  intro N hN
  obtain ⟨hl,hb⟩ := hbudget N hN
  have hl0 : 0<Real.log N := by linarith
  have hnR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hn4 : (4:ℝ)≤N := by exact_mod_cast hN₀.trans hN
  have hr : 1≤(Real.log N)^C := Real.one_le_rpow hl hC
  have he : ((Real.log N)^C)^3=(Real.log N)^(3*C) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hl0.le]
    congr 1
    ring
  have hb' : ((Real.log N)^C)^3≤N := by simpa only [he,neg_zero,Real.rpow_zero,mul_one] using hb
  have hsep : 2*((Real.log N)^C)^3<(N:ℝ)^2 := by nlinarith
  refine ⟨hl,hr,hsep,?_⟩
  apply (div_lt_iff₀ (sq_pos_of_pos hnR)).mpr
  have hcube : (Real.log N)^C≤((Real.log N)^C)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hr (by decide : 1≤3)
  nlinarith

end PrimeSquares
