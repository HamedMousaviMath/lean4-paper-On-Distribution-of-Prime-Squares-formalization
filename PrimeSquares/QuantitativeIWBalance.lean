import PrimeSquares.QuantitativeIWParameters
import PrimeSquares.NearOneGaugeComparison

set_option autoImplicit false
namespace PrimeSquares

noncomputable def iwBalancedRank (v : ℝ) : ℕ :=
  ⌈Real.sqrt (v/Real.log (Real.exp 1+v))⌉₊+4

theorem iwBalancedRank_bounds {v : ℝ} (_hv : 1≤v) :
    4≤ iwBalancedRank v ∧
      Real.sqrt (v/Real.log (Real.exp 1+v))≤(iwBalancedRank v : ℝ) ∧
      (iwBalancedRank v : ℝ)≤Real.sqrt (v/Real.log (Real.exp 1+v))+5 := by
  have hu : 0≤Real.sqrt (v/Real.log (Real.exp 1+v)) := Real.sqrt_nonneg _
  have hlo := Nat.le_ceil (Real.sqrt (v/Real.log (Real.exp 1+v)))
  have hhi := Nat.ceil_lt_add_one hu
  constructor
  · unfold iwBalancedRank
    omega
  · unfold iwBalancedRank
    push_cast
    constructor <;> linarith

theorem iwBalancedRank_optimization {v : ℝ} (hv : 1≤v) :
    (iwBalancedRank v : ℝ)*Real.log (Real.exp 1+v)+v/(iwBalancedRank v : ℝ)≤
      12*Real.sqrt (v*Real.log (Real.exp 1+v)) := by
  let L := Real.log (Real.exp 1+v)
  let u := Real.sqrt (v/L)
  let S := Real.sqrt (v*L)
  have hL : 1≤L := (nearOne_innerLog_bounds hv).1
  have hL2 : L≤2*v := (nearOne_innerLog_bounds hv).2
  have hL0 : 0<L := by linarith
  have hv0 : 0<v := by linarith
  have hu0 : 0<u := Real.sqrt_pos.mpr (div_pos hv0 hL0)
  have hu2 : u^2*L=v := by
    dsimp [u]
    rw [Real.sq_sqrt (div_nonneg hv0.le hL0.le),div_mul_cancel₀ _ hL0.ne']
  have hS0 : 0≤S := Real.sqrt_nonneg _
  have hS2 : S^2=v*L := Real.sq_sqrt (mul_nonneg hv0.le hL0.le)
  have huL : u*L=S := by
    have hh := congrArg (fun z : ℝ => z*L) hu2
    have hsq : (u*L)^2=S^2 := by nlinarith [hh]
    have hprod : 0≤u*L := mul_nonneg hu0.le hL0.le
    nlinarith
  obtain ⟨hk,huk,hku⟩ := iwBalancedRank_bounds hv
  have hkR : (4 : ℝ)≤ iwBalancedRank v := by exact_mod_cast hk
  have hk0 : (0 : ℝ)< iwBalancedRank v := by linarith
  have hterm : v/(iwBalancedRank v : ℝ)≤S := by
    apply (div_le_iff₀ hk0).mpr
    have h := mul_le_mul_of_nonneg_left huk hS0
    have he : v=u*S := by rw [←huL];nlinarith [hu2]
    change S*u≤S*(iwBalancedRank v : ℝ) at h
    nlinarith
  have hfirst := mul_le_mul_of_nonneg_right hku hL0.le
  have hLS : L≤2*S := by
    have h := mul_le_mul_of_nonneg_right hL2 hL0.le
    nlinarith
  change (iwBalancedRank v : ℝ)*L+v/(iwBalancedRank v : ℝ)≤12*S
  change (iwBalancedRank v : ℝ)≤u+5 at hku
  have hkprod := mul_le_mul_of_nonneg_right hku hL0.le
  nlinarith

theorem iwBalancedRank_weighted {v A : ℝ} (hv : 1≤v) (hA : 1≤A) :
    (iwBalancedRank v : ℝ)*Real.log (Real.exp 1+v)+A*v/(iwBalancedRank v : ℝ)≤
      12*A*Real.sqrt (v*Real.log (Real.exp 1+v)) := by
  have h0 := iwBalancedRank_optimization hv
  have hK : 0≤(iwBalancedRank v : ℝ)*Real.log (Real.exp 1+v) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith [(nearOne_innerLog_bounds hv).1])
  have h := mul_le_mul_of_nonneg_left h0 (show 0≤A by linarith)
  have h' := mul_nonneg (show 0≤A-1 by linarith) hK
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith

end PrimeSquares
