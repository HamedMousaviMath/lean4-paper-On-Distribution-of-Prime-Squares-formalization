import PrimeSquares.AbstractLocalStoppingEndpoint
import PrimeSquares.LinearLocalRadiusComparison

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

theorem localSplittingThreshold_le_iff {v s J M : ℝ}
    (hv : v < 1) (hs : 0 < s) (hJ : 0 < J) (hM : 0 < M) :
    localSplittingThreshold v s J ≤ M ↔ J ≤ M^((1-v)/s)/10 := by
  have he : 0 < (1-v)/s := div_pos (by linarith) hs
  have hbase : 0 ≤ 10*J := by positivity
  have hp : (localSplittingThreshold v s J)^((1-v)/s)=10*J := by
    unfold localSplittingThreshold
    rw [←Real.rpow_mul hbase]
    have hx : s/(1-v)*((1-v)/s)=1 := by
      have hn : 1-v ≠ 0 := by linarith
      field_simp [hn,hs.ne']
    rw [hx,Real.rpow_one]
  have hth : 0 ≤ localSplittingThreshold v s J := by
    unfold localSplittingThreshold
    positivity
  have hi := Real.rpow_le_rpow_iff hth hM.le he
  rw [hp] at hi
  constructor
  · intro h
    have hh := hi.mpr h
    exact (le_div_iff₀ (by norm_num : (0:ℝ)<10)).mpr (by nlinarith)
  · intro h
    apply hi.mp
    have hh := (le_div_iff₀ (by norm_num : (0:ℝ)<10)).mp h
    nlinarith

theorem linearSourceBallMass_indicator_power {M : ℝ} (hM : 0 < M)
    (C v : ℝ) (F : Finset ℤ) (x : ℤ) :
    M^(1-v)*linearSourceBallMass C (finiteIndicatorLp F 1) x M=
      M^(-v)*(linearWindowCount C M F x:ℝ) := by
  rw [linearSourceBallMass_indicator,Real.rpow_sub hM,Real.rpow_one,Real.rpow_neg hM.le]
  field_simp

theorem source_local_stopping_density_cap {cap : ℝ} (hcap : 0 ≤ cap)
    (I : SparseIntegerInterval) (F G : Finset ℤ) (hG : G ⊆ I.points)
    (hF : (F.card:ℝ) ≤ cap*I.length) : finiteSetDensity I.length F G ≤ cap := by
  have hL : (0:ℝ)<I.length := by exact_mod_cast I.length_pos
  have hg : (G.card:ℝ) ≤ I.length := by
    exact_mod_cast (Finset.card_le_card hG).trans_eq (integerInterval_card_points I)
  apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
  calc
    _ ≤ (cap*I.length)*(I.length:ℝ) :=
      mul_le_mul hF hg (Nat.cast_nonneg _) (mul_nonneg hcap hL.le)
    _ = _ := by ring

theorem source_abstract_local_stopping_estimate {C C₀ v s r γ β A K D cap : ℝ}
    (hC₀ : 0 < C₀) (hK : 0 ≤ K) (hv : v < 1) (hs : 1-v ≤ s)
    (hr : 0 < r) (hβ : 0 ≤ β) (hβγ : β ≤ γ) (hA : 1/2 < A)
    (hD : 0 ≤ D) (hcap : 0 < cap) :
    ∃ Kout : ℝ,0 < Kout ∧ ∀ (I : SparseIntegerInterval) (F G : Finset ℤ)
      (P : LocalizedStoppingFamily F G C v s r γ β A K)
      (BM : ℕ → ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ)) (τ : ℤ → ℕ),
      G ⊆ I.points → (F.card:ℝ) ≤ cap*I.length →
      (∀ x ∈ G,∃ j : ℕ,τ x=2^j) → (∀ j,P.B j=BM (2^j)) →
      (∀ x ∈ G,linearSourceLocalMass C₀ (τ x) (finiteIndicatorLp F 1) x ≤ D*((F.card:ℝ)/I.length)) →
      ‖∑ x ∈ G,BM (τ x) (finiteIndicatorLp F 2) x‖/(I.length:ℝ) ≤
        Kout*(finiteSetDensity I.length F G)^(1-s/(2*(s+r)))*
          (paperLog (finiteSetDensity I.length F G))^(γ+s*(β-γ)/(s+r)) := by
  let R : ℝ := max 1 (C/C₀)
  have hR : 1 ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨Kout,hKout,hout⟩ := abstract_local_stopping_endpoint (C:=C) hK hv
    (by linarith : 0 < s) hr hβ hβγ hA (mul_nonneg hR0 hD) hcap
  refine ⟨Kout,hKout,?_⟩
  intro I F G P BM τ hG hF hτ hB hadm
  have hL : (0:ℝ)<I.length := by exact_mod_cast I.length_pos
  let t := fun x : ℤ => Nat.log2 (τ x)
  have ht (x : ℤ) (hx : x ∈ G) : (2:ℕ)^(t x)=τ x := by
    obtain ⟨j,hj⟩ := hτ x hx
    simp only [t,hj,Nat.log2_two_pow]
  have hadm' (x : ℤ) (hx : x ∈ G) :
      linearSourceLocalMass C ((2:ℕ)^(t x)) (finiteIndicatorLp F 1) x ≤
        (R*D)*((F.card:ℝ)/I.length) := by
    have hN : 1 ≤ (2:ℕ)^(t x) := one_le_pow₀ (by norm_num)
    calc
      _ ≤ R*linearSourceLocalMass C₀ ((2:ℕ)^(t x)) (finiteIndicatorLp F 1) x :=
        linearSourceLocalMass_change_radius hN hC₀ _ x
      _ = R*linearSourceLocalMass C₀ (τ x) (finiteIndicatorLp F 1) x := by rw [ht x hx]
      _ ≤ R*(D*((F.card:ℝ)/I.length)) := mul_le_mul_of_nonneg_left (hadm x hx) hR0
      _ = _ := by ring
  have h := hout I.length F G P t hL (source_local_stopping_density_cap hcap.le I F G hG hF) hadm'
  have heq : (∑ x ∈ G,P.B (t x) (finiteIndicatorLp F 2) x)=
      ∑ x ∈ G,BM (τ x) (finiteIndicatorLp F 2) x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hB,ht x hx]
  rw [heq] at h
  simpa only [highLowEndpoint,highLowDensityExponent,highLowLogExponent,mul_assoc] using h

end PrimeSquares
