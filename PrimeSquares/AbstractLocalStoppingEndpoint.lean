import PrimeSquares.LocalizedStoppingTradeoff

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

noncomputable def localizedTradeoffConstant (K D s γ A : ℝ) : ℝ :=
  localizedLowConstant K D s γ+localizedHighConstant K A+1

theorem localizedTradeoffConstant_bounds {K D s γ A : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D) :
    0 < localizedTradeoffConstant K D s γ A ∧
      localizedLowConstant K D s γ ≤ localizedTradeoffConstant K D s γ A ∧
      localizedHighConstant K A ≤ localizedTradeoffConstant K D s γ A := by
  have hlog2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hCA := dyadicLogSquareConstant_nonneg A
  have hlo : 0 ≤ localizedLowConstant K D s γ := by
    unfold localizedLowConstant
    positivity
  have hhi : 0 ≤ localizedHighConstant K A := by
    unfold localizedHighConstant
    positivity
  unfold localizedTradeoffConstant
  constructor
  · linarith
  constructor <;> linarith

theorem localizedStopping_normalized_tradeoff {C v s r γ β A K D L J : ℝ}
    (F G : Finset ℤ) (P : LocalizedStoppingFamily F G C v s r γ β A K) (hK : 0 ≤ K) (hv : v < 1) (hγ : 0 ≤ γ)
    (hA : 1/2 < A) (hD : 0 ≤ D) (hL : 0 < L) (hJ : 2 ≤ J)
    (τ : ℤ → ℕ)
    (hadm : ∀ x ∈ G,
      linearSourceLocalMass C ((2:ℕ)^(τ x)) (finiteIndicatorLp F 1) x ≤ D*((F.card:ℝ)/L)) :
    ‖∑ x ∈ G,P.B (τ x) (finiteIndicatorLp F 2) x‖/L ≤
      localizedTradeoffConstant K D s γ A*
        (finiteSetDensity L F G*J^s*(Real.log J)^γ+
          (finiteSetDensity L F G)^(1/2:ℝ)*J^(-r)*(Real.log J)^β) := by
  obtain ⟨_,hlo,hhi⟩ := localizedTradeoffConstant_bounds (s:=s) (γ:=γ) (A:=A) hK hD
  have hlog : 0 ≤ Real.log J := Real.log_nonneg (by linarith : 1 ≤ J)
  have hh := localizedStopping_finite_tradeoff F G P hK hv hγ hA hD hL hJ τ hadm
  have hraw : ‖∑ x ∈ G,P.B (τ x) (finiteIndicatorLp F 2) x‖ ≤
      (G.card:ℝ)*(localizedTradeoffConstant K D s γ A*((F.card:ℝ)/L)*J^s*(Real.log J)^γ)+
        (localizedTradeoffConstant K D s γ A*J^(-r)*(Real.log J)^β*Real.sqrt (F.card:ℝ))*Real.sqrt (G.card:ℝ) := by
    apply hh.trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlo (by positivity)) (by positivity))
          (by positivity)) (Nat.cast_nonneg _)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hhi (by positivity)) (by positivity))
          (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  apply (div_le_div_of_nonneg_right hraw hL.le).trans_eq
  have he := normalized_pairing_terms L (F.card:ℝ) (G.card:ℝ)
    (J^s*(Real.log J)^γ) (J^(-r)*(Real.log J)^β) (localizedTradeoffConstant K D s γ A)
      hL (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  unfold finiteSetDensity
  convert he using 1 <;> ring

theorem abstract_local_stopping_endpoint {C v s r γ β A K D cap : ℝ}
    (hK : 0 ≤ K) (hv : v < 1)
    (hs : 0 < s) (hr : 0 < r) (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (hA : 1/2 < A) (hD : 0 ≤ D) (hcap : 0 < cap) :
    ∃ Kout : ℝ,0 < Kout ∧ ∀ (L : ℝ) (F G : Finset ℤ)
      (P : LocalizedStoppingFamily F G C v s r γ β A K) (τ : ℤ → ℕ),0 < L →
      finiteSetDensity L F G ≤ cap →
      (∀ x ∈ G,linearSourceLocalMass C ((2:ℕ)^(τ x)) (finiteIndicatorLp F 1) x ≤ D*((F.card:ℝ)/L)) →
      ‖∑ x ∈ G,P.B (τ x) (finiteIndicatorLp F 2) x‖/L ≤
        Kout*highLowEndpoint s r γ β (finiteSetDensity L F G) := by
  have htrade := (localizedTradeoffConstant_bounds (s:=s) (γ:=γ) (A:=A) hK hD).1
  have hlog2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hopt := highLowOptimizationConstant_pos hs hr γ β
  have hcapped : 0 < highLowCappedConstant s r γ β cap := by
    unfold highLowCappedConstant
    positivity
  refine ⟨localizedTradeoffConstant K D s γ A*highLowCappedConstant s r γ β cap,
    mul_pos htrade hcapped,?_⟩
  intro L F G P τ hL hδcap hadm
  by_cases hF : F=∅
  · subst F
    have hf : finiteIndicatorLp (∅:Finset ℤ) 2=0 := by
      apply lp.ext
      funext x
      simp [finiteIndicatorLp,finiteIndicator]
    simp [hf,finiteSetDensity,highLowEndpoint_zero hs hr]
  by_cases hG : G=∅
  · subst G
    simp [finiteSetDensity,highLowEndpoint_zero hs hr]
  have hFpos : (0:ℝ)<F.card := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hF)
  have hGpos : (0:ℝ)<G.card := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hG)
  have hδ : 0 < finiteSetDensity L F G := div_pos (mul_pos hFpos hGpos) (sq_pos_of_pos hL)
  apply unrestricted_highLow_scalar_capped hs hr hβ hβγ hδ hδcap htrade.le
  intro j hj
  exact localizedStopping_normalized_tradeoff F G P hK hv (hβ.trans hβγ) hA hD hL hj τ hadm

end PrimeSquares
