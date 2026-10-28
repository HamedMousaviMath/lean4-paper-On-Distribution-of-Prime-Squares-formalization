import PrimeSquares.HighLowNotation
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace PrimeSquares

noncomputable def iwNearOneExponent (r : ℕ) : ℝ := (2*(r : ℝ))/(2*(r : ℝ)-1)
noncomputable def iwRho (k : ℕ) : ℝ := 2/((k : ℝ)-1/2)
noncomputable def iwDenominatorBound (C : ℝ) (k Q : ℕ) : ℝ :=
  C^((k : ℝ)^2*(Q : ℝ)^(1/((k : ℝ)-1/2)))
noncomputable def iwWidth (C : ℝ) (r k Q : ℕ) : ℝ :=
  (2^20*(r : ℝ)*iwDenominatorBound C k Q^(2*r+8))⁻¹
noncomputable def iwMultiplierConstant (C : ℝ) (r k : ℕ) : ℝ :=
  (C*(r : ℝ)*Real.log (2+k : ℝ))^(C*k)
noncomputable def iwMaximalCost (C : ℝ) (r k Q : ℕ) : ℝ :=
  (r : ℝ)*(iwMultiplierConstant C r k)^2*
    Real.log (Real.exp 1+(Q : ℝ)+(r : ℝ)*Real.log (iwDenominatorBound C k Q))

theorem iwNearOneExponent_bounds {r : ℕ} (hr : 2≤r) :
    1< iwNearOneExponent r ∧ iwNearOneExponent r≤4/3 := by
  have hr0 : 0<2*(r : ℝ)-1 := by
    have hrR : (2 : ℝ)≤r := by exact_mod_cast hr
    linarith
  constructor
  · rw [iwNearOneExponent,lt_div_iff₀ hr0]
    linarith
  · rw [iwNearOneExponent,div_le_iff₀ hr0]
    have : (2 : ℝ)≤r := by exact_mod_cast hr
    linarith

theorem iwNearOneExponent_sub_one {r : ℕ} (hr : 2≤r) :
    iwNearOneExponent r-1=1/(2*(r : ℝ)-1) := by
  have h : 2*(r : ℝ)-1≠0 := by
    have hrR : (2 : ℝ)≤r := by exact_mod_cast hr
    linarith
  unfold iwNearOneExponent
  field_simp
  ring

theorem iwNearOneExponent_reciprocal {r : ℕ} (hr : 2≤r) :
    1/iwNearOneExponent r=1-1/(2*(r : ℝ)) := by
  have h0 : (r : ℝ)≠0 := by
    have hrR : (2 : ℝ)≤r := by exact_mod_cast hr
    linarith
  have h1 : 2*(r : ℝ)-1≠0 := by
    have hrR : (2 : ℝ)≤r := by exact_mod_cast hr
    linarith
  unfold iwNearOneExponent
  field_simp

theorem iwRho_bounds {k : ℕ} (hk : 4≤k) : 0< iwRho k ∧ iwRho k<1 := by
  have hkR : (4 : ℝ)≤k := by exact_mod_cast hk
  have h : 0<(k : ℝ)-1/2 := by linarith
  constructor
  · exact div_pos (by norm_num) h
  · rw [iwRho,div_lt_one h]
    linarith

theorem iwRho_half {k : ℕ} (hk : 4≤k) : iwRho k/2=1/((k : ℝ)-1/2) := by
  have h : (k : ℝ)-1/2≠0 := by
    have hkR : (4 : ℝ)≤k := by exact_mod_cast hk
    linarith
  unfold iwRho
  field_simp

theorem iwRho_rank {k : ℕ} (hk : 4≤k) : ⌊2/iwRho k⌋₊+1=k := by
  have hkR : (4 : ℝ)≤k := by exact_mod_cast hk
  have hd : (k : ℝ)-1/2≠0 := by linarith
  have he : 2/iwRho k=(k : ℝ)-1/2 := by unfold iwRho;field_simp
  have hf : ⌊(k : ℝ)-1/2⌋₊=k-1 := by
    apply (Nat.floor_eq_iff (by linarith : 0≤(k : ℝ)-1/2)).mpr
    rw [Nat.cast_sub (by omega : 1≤k),Nat.cast_one]
    constructor <;> linarith
  rw [he,hf]
  omega

theorem iwDenominatorBound_one_le {C : ℝ} (hC : 2≤C) (k Q : ℕ) :
    1≤ iwDenominatorBound C k Q := by
  unfold iwDenominatorBound
  exact Real.one_le_rpow (by linarith) (by positivity)

theorem iwDenominatorBound_log {C : ℝ} (hC : 0<C) (k Q : ℕ) :
    Real.log (iwDenominatorBound C k Q)=
      (k : ℝ)^2*(Q : ℝ)^(1/((k : ℝ)-1/2))*Real.log C := by
  exact Real.log_rpow hC _

theorem iwWidth_pos {C : ℝ} (hC : 2≤C) {r : ℕ} (hr : 2≤r) (k Q : ℕ) :
    0< iwWidth C r k Q := by
  have hB : 0< iwDenominatorBound C k Q := lt_of_lt_of_le (by norm_num) (iwDenominatorBound_one_le hC k Q)
  have hr0 : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
  unfold iwWidth
  positivity

theorem iwWidth_denominator_separation {C : ℝ} (hC : 2≤C) {r : ℕ} (hr : 2≤r) (k Q : ℕ) :
    4*iwWidth C r k Q*(iwDenominatorBound C k Q)^2<1 := by
  let B := iwDenominatorBound C k Q
  have hB : 1≤B := iwDenominatorBound_one_le hC k Q
  have hB0 : 0<B := by linarith
  have hrR : (2 : ℝ)≤r := by exact_mod_cast hr
  have hp : B^2≤B^(2*r+8) := pow_le_pow_right₀ hB (by omega : 2≤2*r+8)
  have hc : 4*B^2<2^20*(r : ℝ)*B^(2*r+8) := by
    have hpow : 1≤B^(2*r+8) := one_le_pow₀ hB
    nlinarith
  change 4*(2^20*(r : ℝ)*B^(2*r+8))⁻¹*B^2<1
  have hd : 0<2^20*(r : ℝ)*B^(2*r+8) := by positivity
  have he : 4*(2^20*(r : ℝ)*B^(2*r+8))⁻¹*B^2=(4*B^2)/(2^20*(r : ℝ)*B^(2*r+8)) := by ring
  rw [he,div_lt_one hd]
  exact hc

end PrimeSquares
