import PrimeSquares.DyadicFunctionLayers
import Mathlib.Analysis.PSeries

open Finset
namespace PrimeSquares

noncomputable def layerGaugePolynomial (K : ℝ) : ℝ := 4*K*(3+2*Real.log K)^2
noncomputable def layerGaugeConstant (C K : ℝ) : ℝ :=
  2*Real.exp ((1+2*C)*Real.log (layerGaugePolynomial K)+2*(9*C+4)*Real.log 2)

theorem layerGaugeConstant_pos (C K : ℝ) : 0<layerGaugeConstant C K := by
  unfold layerGaugeConstant
  positivity

theorem dyadicLayer_gauge_cost {C K : ℝ} (hC : 0≤C) (hK : 2≤K) (j : ℕ) :
    nearOnePsi C (4*(2 : ℝ)^j*((j : ℝ)+1)^2)≤
      layerGaugeConstant C K*nearOnePsi (9*C+4) ((2 : ℝ)^j/K) := by
  let t := (2 : ℝ)^j/K
  let a := 4*K*((j : ℝ)+1)^2
  have hK0 : 0<K := by linarith
  have ht : 0<t := by dsimp [t];positivity
  have hj : 0≤(j : ℝ) := Nat.cast_nonneg j
  have hLK : 0≤Real.log K := Real.log_nonneg (by linarith)
  have hL := nearOneLog_one_le t
  have hlog2 : (1/2 : ℝ)≤Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h
    exact h
  have hlog : (j : ℝ)*Real.log 2≤Real.log K+nearOneLog t := by
    have h := Real.log_le_log ht (show t≤Real.exp 1+max 0 t by rw [max_eq_right ht.le];linarith [Real.exp_pos (1 : ℝ)])
    change Real.log t≤nearOneLog t at h
    dsimp [t] at h
    rw [Real.log_div (by positivity : (2 : ℝ)^j≠0) hK0.ne',Real.log_pow] at h
    linarith
  have hjs : (j : ℝ)+1≤(3+2*Real.log K)*nearOneLog t := by
    have h1 := mul_le_mul_of_nonneg_left hlog2 hj
    have h2 := mul_nonneg hLK (sub_nonneg.mpr hL)
    nlinarith
  have ha : 1≤a := by dsimp [a];nlinarith [sq_nonneg (j : ℝ)]
  have hD : 1≤layerGaugePolynomial K := by unfold layerGaugePolynomial;nlinarith [sq_nonneg (Real.log K)]
  have haD : a≤layerGaugePolynomial K*(nearOneLog t)^2 := by
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤(j : ℝ)+1) hjs 2
    dsimp [a,layerGaugePolynomial]
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0≤4*K by positivity)]
  have h := nearOnePsi_log_polynomial hC ha ht.le hD haD
  have he : a*t=4*(2 : ℝ)^j*((j : ℝ)+1)^2 := by dsimp [a,t];field_simp
  rw [he] at h
  exact h

theorem finite_inverse_square_sum (I : Finset ℕ) :
    (∑ j∈I,1/((j : ℝ)+1)^2)≤2 := by
  classical
  let m := I.sup id+2
  have hsub : I.image (fun j => j+1) ⊆ Ioo 0 m := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hk
    have h := le_sup (f := id) hj
    simp only [id_eq] at h
    exact mem_Ioo.mpr ⟨by omega,by dsimp [m];omega⟩
  have hinj : Set.InjOn (fun j : ℕ => j+1) I := fun _ _ _ _ h => Nat.add_right_cancel h
  calc
    _ = ∑ k∈I.image (fun j : ℕ => j+1),((k : ℝ)^2)⁻¹ := by
      rw [sum_image hinj]
      apply sum_congr rfl
      intro j hj
      simp only [Nat.cast_add,Nat.cast_one,one_div]
    _ ≤ ∑ k∈Ioo 0 m,((k : ℝ)^2)⁻¹ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2 := by simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 m)

theorem functionLayer_gauge_sum (F : Finset ℤ) (f : ℤ → ℂ) {C K level : ℝ}
    (hC : 0≤C) (hK : 2≤K) (hlevel : 0<level) :
    (∑ j∈functionLayerIndices F (fun y => K*‖f y‖/level),
      (functionLayer F (fun y => K*‖f y‖/level) j).card*
        nearOnePsi C (4*(2 : ℝ)^j*((j : ℝ)+1)^2))≤
      layerGaugeConstant C K*∑ x∈F.filter (fun x => level/K<‖f x‖),nearOnePsi (9*C+4) (‖f x‖/level) := by
  classical
  let u := fun y => K*‖f y‖/level
  have hK0 : 0<K := by linarith
  calc
    _ ≤ ∑ j∈functionLayerIndices F u,(functionLayer F u j).card*
        (layerGaugeConstant C K*nearOnePsi (9*C+4) ((2 : ℝ)^j/K)) := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (dyadicLayer_gauge_cost hC hK j) (by positivity)
    _ = layerGaugeConstant C K*∑ x∈F,
        if 1<u x then nearOnePsi (9*C+4) ((2 : ℝ)^functionLayerIndex (u x)/K) else 0 := by
      simp_rw [mul_left_comm (↑(functionLayer F u _).card) (layerGaugeConstant C K)]
      rw [←mul_sum,functionLayer_partition_cost]
    _ ≤ layerGaugeConstant C K*∑ x∈F,
        if level/K<‖f x‖ then nearOnePsi (9*C+4) (‖f x‖/level) else 0 := by
      apply mul_le_mul_of_nonneg_left _ (layerGaugeConstant_pos C K).le
      apply sum_le_sum
      intro x hx
      have he : 1<u x ↔ level/K<‖f x‖ := by
        dsimp [u]
        rw [lt_div_iff₀ hlevel,div_lt_iff₀ hK0]
        constructor <;> intro h <;> nlinarith
      by_cases hu : 1<u x
      · rw [ite_eq_left hu,ite_eq_left (he.mp hu)]
        apply nearOnePsi_mono
        have hb := (functionLayerIndex_spec hu.le).1
        change (2 : ℝ)^functionLayerIndex (u x)≤K*‖f x‖/level at hb
        have h := (le_div_iff₀ hlevel).mp hb
        apply (div_le_div_iff₀ hK0 hlevel).mpr
        nlinarith
      · rw [ite_eq_right hu,ite_eq_right (fun h => hu (he.mpr h))]
    _ = _ := by rw [sum_filter]

end PrimeSquares
