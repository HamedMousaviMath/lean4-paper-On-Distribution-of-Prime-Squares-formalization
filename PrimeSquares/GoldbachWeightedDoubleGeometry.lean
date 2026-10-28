import PrimeSquares.GoldbachWeightedMeanValue

set_option autoImplicit false
namespace PrimeSquares

noncomputable def goldbachWeightedUBound (D p : ℝ) : ℝ := Real.exp D/(2*p^2)
noncomputable def goldbachWeightedPBound (D u : ℝ) : ℝ := Real.exp ((D-Real.log (2*u))/2)

theorem goldbach_weighted_u_bound_log (D p : ℝ) (hp : 0<p) :
    0<goldbachWeightedUBound D p ∧
      Real.log (goldbachWeightedUBound D p)=D-Real.log 2-2*Real.log p := by
  have hpos : 0<goldbachWeightedUBound D p := by
    dsimp only [goldbachWeightedUBound]
    positivity
  refine ⟨hpos,?_⟩
  rw [goldbachWeightedUBound,Real.log_div (Real.exp_pos D).ne'
    (show 2*p^2≠0 by positivity),Real.log_exp,
    Real.log_mul (by norm_num) (pow_ne_zero 2 hp.ne'),Real.log_pow]
  norm_num
  ring

theorem goldbach_weighted_double_p_geometry (D a p : ℝ) (hD : 18≤D) (ha : 2≤a)
    (hpz : Real.exp ((4/9:ℝ)*D)≤p) (hap : a≤goldbachWeightedUBound D p) :
    0<p ∧ goldbachWeightedUBound D p≤Real.exp (D/9)/2 ∧
      Real.log p≤D/2 ∧ ∀ u∈Set.Icc a (Real.exp (D/9)/2),
        2≤D-Real.log (2*p)-Real.log u := by
  have hp0 : 0<p := (Real.exp_pos _).trans_le hpz
  obtain ⟨hbp0,hlogbp⟩ := goldbach_weighted_u_bound_log D p hp0
  have ha0 : 0<a := by linarith
  have hloga : 0≤Real.log a := Real.log_nonneg (by linarith)
  have hlog2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hpLow : (4/9:ℝ)*D≤Real.log p := by
    have hh := Real.log_le_log (Real.exp_pos _) hpz
    rwa [Real.log_exp] at hh
  have hpHigh : Real.log p≤D/2 := by
    have hh := Real.log_le_log ha0 hap
    rw [hlogbp] at hh
    linarith
  have hU0 : 0<Real.exp (D/9)/2 := by positivity
  have hlogU : Real.log (Real.exp (D/9)/2)=D/9-Real.log 2 := by
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num),Real.log_exp]
  refine ⟨hp0,?_,hpHigh,?_⟩
  · apply (Real.log_le_log_iff hbp0 hU0).mp
    rw [hlogbp,hlogU]
    linarith
  · intro u hu
    have hu0 : 0<u := ha0.trans_le hu.1
    have hh := Real.log_le_log hu0 hu.2
    rw [hlogU] at hh
    rw [Real.log_mul (by norm_num) hp0.ne']
    linarith

theorem goldbach_weighted_double_u_geometry (D a u : ℝ) (hD : 18≤D) (ha : 2≤a)
    (hu : u∈Set.Icc a (Real.exp (D/9)/2)) :
    0<Real.log (2*u)/D ∧ Real.log (2*u)/D≤1/9 ∧
      Real.exp ((4/9:ℝ)*D)≤goldbachWeightedPBound D u ∧
      (∀ t∈Set.Icc (Real.exp ((4/9:ℝ)*D)) (goldbachWeightedPBound D u),
        0<D-Real.log (2*u)-Real.log t ∧ D-Real.log (2*u)-Real.log t≤2*Real.log t) ∧
      Real.log (Real.exp ((4/9:ℝ)*D))≤D-Real.log (2*u)-Real.log (Real.exp ((4/9:ℝ)*D)) ∧
      Real.log (Real.exp ((4/9:ℝ)*D))≤D-Real.log (2*u)-Real.log (goldbachWeightedPBound D u) := by
  have hD0 : 0<D := by linarith
  have hu2 : 2≤u := ha.trans hu.1
  have hu0 : 0<u := by linarith
  have h2u : 0<2*u := by positivity
  have hlog2u0 : 0<Real.log (2*u) := Real.log_pos (by linarith)
  have hlog2u : Real.log (2*u)≤D/9 := by
    have hh : 2*u≤Real.exp (D/9) := by linarith [hu.2]
    have hh' := Real.log_le_log h2u hh
    rwa [Real.log_exp] at hh'
  have hbLog : Real.log (goldbachWeightedPBound D u)=(D-Real.log (2*u))/2 := Real.log_exp _
  have hzb : Real.exp ((4/9:ℝ)*D)≤goldbachWeightedPBound D u := by
    apply Real.exp_le_exp.mpr
    linarith
  refine ⟨div_pos hlog2u0 hD0,(div_le_iff₀ hD0).mpr (by linarith),hzb,?_,?_,?_⟩
  · intro t ht
    have ht0 : 0<t := (Real.exp_pos _).trans_le ht.1
    have hlogtLow : (4/9:ℝ)*D≤Real.log t := by
      have hh := Real.log_le_log (Real.exp_pos _) ht.1
      rwa [Real.log_exp] at hh
    have hlogtHigh := Real.log_le_log ht0 ht.2
    rw [hbLog] at hlogtHigh
    constructor <;> linarith
  · rw [Real.log_exp]
    linarith
  · rw [Real.log_exp,hbLog]
    linarith

theorem goldbach_weighted_double_domain (D u p : ℝ) (hu : 0<u) (hp : 0<p) :
    u≤goldbachWeightedUBound D p ↔ p≤goldbachWeightedPBound D u := by
  obtain ⟨hb0,hblog⟩ := goldbach_weighted_u_bound_log D p hp
  have hbp0 : 0<goldbachWeightedPBound D u := Real.exp_pos _
  rw [←Real.log_le_log_iff hu hb0,←Real.log_le_log_iff hp hbp0,hblog]
  have hbplog : Real.log (goldbachWeightedPBound D u)=(D-Real.log (2*u))/2 := Real.log_exp _
  rw [hbplog,Real.log_mul (by norm_num) hu.ne']
  constructor <;> intro h <;> linarith

end PrimeSquares
