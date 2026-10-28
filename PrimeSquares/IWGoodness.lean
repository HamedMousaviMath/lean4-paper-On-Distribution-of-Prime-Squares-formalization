import PrimeSquares.IWFiniteFrequencyGeometry

set_option autoImplicit false
open Finset
namespace PrimeSquares

/-- Tao Definition 1.3 with c=1/2 and d=1. This is the actual
integer maximum-component condition, stronger than mere pair separation. -/
def IWGood (r k : ℕ) (S : Finset ℕ) (ε : ℝ) : Prop :=
  ∃ qmax : ℕ,1≤qmax ∧ (∀ s∈S,s≤qmax) ∧ 0<ε ∧
    ε<1/(4*(r : ℝ)*(qmax : ℝ)^(2*r*k))

theorem finite_component_maximum {S : Finset ℕ} {T : ℝ} (hT : 1≤T)
    (hS : ∀ s∈S,(s : ℝ)≤T) :
    ∃ qmax : ℕ,1≤qmax ∧ (∀ s∈S,s≤qmax) ∧ (qmax : ℝ)≤T := by
  let qmax := max 1 (S.sup id)
  have hsup : S.sup id≤⌊T⌋₊ := Finset.sup_le (fun s hs => Nat.le_floor (hS s hs))
  have hmax : qmax≤⌊T⌋₊ := max_le (Nat.le_floor (by simpa only [Nat.cast_one] using hT)) hsup
  refine ⟨qmax,le_max_left _ _,fun s hs => ?_,?_⟩
  · exact (Finset.le_sup (f := id) hs).trans (le_max_right _ _)
  · exact (by exact_mod_cast hmax : (qmax : ℝ)≤⌊T⌋₊).trans (Nat.floor_le (by linarith))

theorem quantitative_iw_goodness {C : ℝ} (hC : 2≤C) {r k Q : ℕ}
    (hr : 2≤r) (hk : 4≤k) (d : TaoArcConstructionData C (iwRho k) k Q) :
    IWGood r k d.S (iwWidth C r k Q) := by
  let B := iwDenominatorBound C k Q
  let T := C^((k : ℝ)*(Q : ℝ)^(iwRho k/2))
  have hC0 : 0≤C := by linarith
  have hT : 1≤T := Real.one_le_rpow (by linarith : 1≤C) (by positivity)
  have hB : 1≤B := iwDenominatorBound_one_le hC k Q
  have hB0 : 0<B := by linarith
  obtain ⟨qmax,hq,hmax,hqT⟩ := finite_component_maximum hT d.component_bound
  have hqR : (1 : ℝ)≤qmax := by exact_mod_cast hq
  have hrR : (2 : ℝ)≤r := by exact_mod_cast hr
  have he : T^(2*r*k)=B^(2*r) := by
    dsimp [T,B,iwDenominatorBound]
    rw [←Real.rpow_natCast,←Real.rpow_mul hC0,←Real.rpow_natCast,←Real.rpow_mul hC0,iwRho_half hk]
    congr 1
    push_cast
    ring
  have hp : (qmax : ℝ)^(2*r*k)≤B^(2*r) :=
    (pow_le_pow_left₀ (by positivity) hqT _).trans_eq he
  have hpow : B^(2*r)≤B^(2*r+8) := pow_le_pow_right₀ hB (by omega)
  have hpow1 : 1≤B^(2*r+8) := one_le_pow₀ hB
  have hden : 4*(r : ℝ)*B^(2*r)<2^20*(r : ℝ)*B^(2*r+8) := by
    have h1 := mul_le_mul_of_nonneg_left hpow (show 0≤4*(r : ℝ) by positivity)
    have h2 := mul_pos (show 0<(2^20-4)*(r : ℝ) by positivity)
      (show 0<B^(2*r+8) by positivity)
    nlinarith
  have hd0 : 0<4*(r : ℝ)*B^(2*r) := by positivity
  have hq0 : 0<4*(r : ℝ)*(qmax : ℝ)^(2*r*k) := by positivity
  have hwidth : iwWidth C r k Q<1/(4*(r : ℝ)*B^(2*r)) := by
    change (2^20*(r : ℝ)*B^(2*r+8))⁻¹<_
    simpa only [one_div] using one_div_lt_one_div_of_lt hd0 hden
  refine ⟨qmax,hq,hmax,iwWidth_pos hC hr k Q,hwidth.trans_le ?_⟩
  exact one_div_le_one_div_of_le hq0
    (mul_le_mul_of_nonneg_left hp (show 0≤4*(r : ℝ) by positivity))

theorem quantitative_iw_construction_good {C : ℝ} (hC : 2≤C)
    (HT : RawTaoArcConstructionInput C) {r k Q : ℕ} (hr : 2≤r) (hk : 4≤k) (hQ : 2^k≤Q) :
    ∃ d : TaoArcConstructionData C (iwRho k) k Q,IWGood r k d.S (iwWidth C r k Q) ∧
      (∀ a∈iwFrequencySet d.S k,(a.den : ℝ)≤ iwDenominatorBound C k Q) := by
  obtain ⟨d,hden,_⟩ := quantitative_iw_frequency_geometry hC HT hr hk hQ
  exact ⟨d,quantitative_iw_goodness hC hr hk d,hden⟩

end PrimeSquares
