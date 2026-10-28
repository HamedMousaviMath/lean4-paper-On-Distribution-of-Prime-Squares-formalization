import PrimeSquares.IWMultiplierInterface
import PrimeSquares.CompactLiftSourceAlgebra

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem compactCircleLift_bounded_sub (m n : BoundedContinuousFunction ℝ ℂ)
    (hm : ∀ x : ℝ,1≤|x| → m x=0) (hn : ∀ x : ℝ,1≤|x| → n x=0)
    (hd : ∀ x : ℝ,1≤|x| → (m-n) x=0) (ξ : PrimeCircle) :
    compactCircleLift (m-n).toContinuousMap hd ξ=
      compactCircleLift m.toContinuousMap hm ξ-compactCircleLift n.toContinuousMap hn ξ := by
  change compactPeriodWindow (m-n) _=compactPeriodWindow m _-compactPeriodWindow n _
  simp only [compactPeriodWindow,Pi.sub_apply]
  ring

theorem compactCircleLift_bounded_combination {ι : Type*} (s : Finset ι) (c : ι→ℂ)
    (f : ι→BoundedContinuousFunction ℝ ℂ) (m : BoundedContinuousFunction ℝ ℂ)
    (hf : ∀ i x,1≤|x| → f i x=0) (hm : ∀ x : ℝ,1≤|x| → m x=0)
    (he : ∀ x,m x=∑ i∈s,c i*f i x) (ξ : PrimeCircle) :
    compactCircleLift m.toContinuousMap hm ξ=
      ∑ i∈s,c i*compactCircleLift (f i).toContinuousMap (hf i) ξ := by
  change compactPeriodWindow m _=∑ i∈s,c i*compactPeriodWindow (f i) _
  simp only [compactPeriodWindow]
  simp_rw [he]
  rw [←sum_add_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro i _
  ring

theorem iwCyclicSymbol_sub (S : Finset ℕ) (k P : ℕ) [NeZero P] (ν : ZMod P→ℂ)
    (m n : BoundedContinuousFunction ℝ ℂ)
    (hm : ∀ x : ℝ,1≤|x| → m x=0) (hn : ∀ x : ℝ,1≤|x| → n x=0)
    (hd : ∀ x : ℝ,1≤|x| → (m-n) x=0) :
    iwCyclicSymbol S k P ν (m-n) hd=iwCyclicSymbol S k P ν m hm-iwCyclicSymbol S k P ν n hn := by
  ext ξ
  simp only [iwCyclicSymbol,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    ContinuousMap.comp_apply,ContinuousMap.coe_mk,ContinuousMap.sub_apply,smul_eq_mul]
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro r _
  rw [compactCircleLift_bounded_sub m n hm hn hd]
  ring

theorem iwCyclicSymbol_combination {ι : Type*} (s : Finset ι) (c : ι→ℂ)
    (S : Finset ℕ) (k P : ℕ) [NeZero P] (ν : ZMod P→ℂ)
    (f : ι→BoundedContinuousFunction ℝ ℂ) (m : BoundedContinuousFunction ℝ ℂ)
    (hf : ∀ i x,1≤|x| → f i x=0) (hm : ∀ x : ℝ,1≤|x| → m x=0)
    (he : ∀ x,m x=∑ i∈s,c i*f i x) :
    iwCyclicSymbol S k P ν m hm=∑ i∈s,c i • iwCyclicSymbol S k P ν (f i) (hf i) := by
  ext ξ
  simp only [iwCyclicSymbol,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    ContinuousMap.comp_apply,ContinuousMap.coe_mk,smul_eq_mul]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro r _
  rw [compactCircleLift_bounded_combination s c f m hf hm he]
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  ring

end PrimeSquares
