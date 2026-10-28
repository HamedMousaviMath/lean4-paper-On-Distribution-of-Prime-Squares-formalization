import PrimeSquares.GoldbachHalvingPartials

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

/-- Complement of the source closed major arcs of uniform radius R/N^2.
All rational lifts are included; equal circle centres give the same arc. -/
def GoldbachMinorArcs (N : ℕ) (R : ℝ) : Set PrimeCircle :=
  {θ | ∀ r : ℚ,(r.den:ℝ)≤R → R/(N:ℝ)^2<dist θ ((r:ℝ):PrimeCircle)}

theorem goldbachMinorArcs_measurable (N : ℕ) (R : ℝ) :
    MeasurableSet (GoldbachMinorArcs N R) := by
  unfold GoldbachMinorArcs
  simp_rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro r
  apply MeasurableSet.iInter
  intro _
  exact (isOpen_lt continuous_const (continuous_id.dist continuous_const)).measurableSet

theorem goldbach_minor_arcs_source_centres (N : ℕ) {R : ℝ} (hR : 0≤R)
    (θ : PrimeCircle) :
    θ∈GoldbachMinorArcs N R ↔ ∀ r∈sourceRationalCenters R,
      R/(N:ℝ)^2<dist θ ((r:ℝ):PrimeCircle) := by
  constructor
  · intro h r hr
    exact h r ((mem_sourceRationalCenters hR r).mp hr).2
  · intro h r hr
    have hh := h (Int.fract r) (ratFract_mem_sourceRationalCenters hR r hr)
    have hz : (((⌊r⌋:ℤ):ℝ):PrimeCircle)=0 := by
      exact (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨⌊r⌋,by simp⟩
    have hc : (((Int.fract r:ℚ):ℝ):PrimeCircle)=((r:ℝ):PrimeCircle) := by
      rw [Int.fract,Rat.cast_sub,Rat.cast_intCast,AddCircle.coe_sub,hz,sub_zero]
    simpa only [hc] using hh

theorem goldbach_circle_distance_le_real (ξ η : ℝ) :
    dist (ξ:PrimeCircle) (η:PrimeCircle)≤|ξ-η| := by
  rw [dist_eq_norm,←AddCircle.coe_sub]
  simpa only [Real.norm_eq_abs] using
    (QuotientAddGroup.norm_mk_le_norm (S:=AddSubgroup.zmultiples (1:ℝ)) (m:=ξ-η))

theorem goldbach_minor_arcs_smaller_annular (N M : ℕ) (hM : 1≤M)
    {R S ξ : ℝ} (hS : 0≤S) (hSR : S≤R)
    (hwidth : S/(M:ℝ)^2≤R/(N:ℝ)^2)
    (hout : (ξ:PrimeCircle)∈GoldbachMinorArcs N R) : OutsideSourceMajorArcs M S ξ := by
  intro r hr k
  have hd := ((mem_sourceRationalCenters hS r).mp hr).2
  have hdist := (hout r (hd.trans hSR)).le
  have hk : ((k:ℝ):PrimeCircle)=0 :=
    (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨k,by simp⟩
  have hshift : ((ξ+(k:ℝ):ℝ):PrimeCircle)=(ξ:PrimeCircle) := by
    rw [AddCircle.coe_add,hk,add_zero]
  have hreal : R/(N:ℝ)^2≤|ξ+(k:ℝ)-(r:ℝ)| := by
    exact hdist.trans (by simpa only [hshift] using
      goldbach_circle_distance_le_real (ξ+(k:ℝ)) (r:ℝ))
  have hmR : (0:ℝ)<M := by exact_mod_cast hM
  have hden : (1:ℝ)≤r.den := by exact_mod_cast r.den_pos
  have hdenom : (M:ℝ)^2≤(r.den:ℝ)*(M:ℝ)^2 := by
    nlinarith [sq_nonneg (M:ℝ)]
  exact (div_le_div_of_nonneg_left hS (sq_pos_of_pos hmR) hdenom).trans (hwidth.trans hreal)

theorem goldbach_minor_arcs_rescale (N M : ℕ) (hM : 1≤M) (hMN : M≤N)
    {R ξ : ℝ} (hR : 0≤R) (hout : (ξ:PrimeCircle)∈GoldbachMinorArcs N R) :
    OutsideSourceMajorArcs M (R*((M:ℝ)/(N:ℝ))^2) ξ := by
  have hmR : (0:ℝ)<M := by exact_mod_cast hM
  have hnR : (0:ℝ)<N := hmR.trans_le (by exact_mod_cast hMN)
  have hratio : (M:ℝ)/(N:ℝ)≤1 := (div_le_one hnR).mpr (by exact_mod_cast hMN)
  have hratio2 : ((M:ℝ)/(N:ℝ))^2≤1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by positivity : (0:ℝ)≤(M:ℝ)/(N:ℝ)) hratio 2
  apply goldbach_minor_arcs_smaller_annular N M hM (by positivity)
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio2 hR) _ hout
  have hm0 : (M:ℝ)≠0 := hmR.ne'
  have hn0 : (N:ℝ)≠0 := hnR.ne'
  exact le_of_eq (by field_simp [hm0,hn0])

end PrimeSquares
