import PrimeSquares.GoldbachSection11Complete
import PrimeSquares.GoldbachDivisorErrorAbsorption

set_option autoImplicit false
open Finset Filter
namespace PrimeSquares

theorem goldbach_quantitative_exceptional_set_squares (H : GoldbachSection11Inputs)
    (Htwo : PrimitiveTwoSquaresCriterion) (ψ : SchwartzMap ℝ ℝ) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x|→ψ x=0) (A : ℝ) (hA : 0<A) :
    ∃ D : ℝ,0<D ∧ ∀ᶠ N : ℕ in atTop,
      ((goldbachExceptionalSet (goldbachAdmissibleNumbers N)).card:ℝ)≤
        D*(N:ℝ)^2*(Real.log N)^(-A) := by
  classical
  let P := A/2+6
  let S := A+2*P+10
  have hS : 0<S := by dsimp only [S,P];linarith
  obtain ⟨B,C,M,k,K,_,_,_,_,hM,hk,_,η,hη,hJoint⟩ :=
    goldbach_section11_complete H ψ hψ hsψ 0 A S hA hS
  let Δ := H.fHalf (9/8)-goldbachWeightedUpperConstant (9/8)*H.FOne 2*goldbachWeightedW (9/8)
  have hΔ : 0<Δ := goldbach_section11_sieve_gap_positive H
  let κ := Δ*k/4
  have hκ : 0<κ := by dsimp only [κ];positivity
  obtain ⟨N₀,_,hReduce⟩ := goldbach_section9_eventual_count_reduction Htwo A P hκ
  have hNat : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hSmall : ∀ᶠ N : ℕ in atTop,η N≤Δ/4 :=
    ((hη.comp hNat).eventually (gt_mem_nhds (by positivity : (0:ℝ)<Δ/4))).mono (fun _ h=>h.le)
  refine ⟨2*M/κ^2+2,by positivity,?_⟩
  filter_upwards [hJoint (Δ/4) (by positivity),hSmall,eventually_ge_atTop N₀] with N hJ hηN hN
  obtain ⟨cm,cp,_,_,hPoint,hError⟩ := hJ
  let v := fun n : ℕ=>goldbachLowerMainTerm ψ N ((Real.log N)^C) n*
    goldbachLowerTheta ((Real.log N)^C) ((N:ℝ)^(8/9:ℝ)) n
  let a := fun _ : ℕ=>H.fHalf (9/8)-η N
  let b := fun _ : ℕ=>goldbachWeightedUpperConstant (9/8)*H.FOne 2*goldbachWeightedW (9/8)+Δ/4
  let E₁ := goldbachLowerRemainderSum ψ N B ((Real.log N)^C) cm
  let E₂ := goldbachUpperFinalError ψ N B ((Real.log N)^C) K cp
  let t := κ*(N:ℝ)*(Real.log N)^(-P)
  have hret (n : ℕ) (hn : n∈goldbachLargeNumbers N ((N:ℝ)^2*(Real.log N)^(-A))) :
      (n:ZMod 24)=12 ∧ (N:ℝ)^2*(Real.log N)^(-A)≤n ∧ n<N^2 := by
    obtain ⟨hna,hret⟩ := mem_filter.mp hn
    obtain ⟨hnN,hn24⟩ := mem_filter.mp hna
    refine ⟨?_,hret,mem_range.mp hnN⟩
    simpa only [Nat.cast_ofNat] using (ZMod.natCast_eq_natCast_iff n 12 24).mpr hn24
  apply hReduce N hN (9/8) (by norm_num) (by norm_num) v a b E₁ E₂ M t hM.le le_rfl
  · intro n hn
    obtain ⟨hn24,hret,hnN⟩ := hret n hn
    convert (hPoint n hn24 hret hnN).2.1 using 1
    norm_num only [show (1:ℝ)/(9/8)=8/9 by norm_num]
  · intro n hn
    obtain ⟨hn24,hret,hnN⟩ := hret n hn
    convert (hPoint n hn24 hret hnN).2.2 using 1
    norm_num only [show (1:ℝ)/(9/8)=8/9 by norm_num]
  · intro n hn
    obtain ⟨hn24,hret,hnN⟩ := hret n hn
    have hm := (hPoint n hn24 hret hnN).1
    have hv : 0≤v n := by
      have hh : 0≤k*(N:ℝ)*(Real.log N)^(-P) := by positivity
      exact hh.trans hm
    have hcoef : Δ/2≤a n-b n := by dsimp only [a,b,Δ];linarith only [hηN]
    have hp := mul_le_mul_of_nonneg_right hcoef hv
    have hq := mul_le_mul_of_nonneg_left hm (show 0≤Δ/2 by positivity)
    dsimp only [t,κ,P] at hp hq ⊢
    nlinarith only [hp,hq]
  · have hsubset : goldbachLargeNumbers N ((N:ℝ)^2*(Real.log N)^(-A))⊆range (N^2) := by
      intro n hn
      exact (mem_filter.mp (mem_filter.mp hn).1).1
    have h₁ := sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _=>sq_nonneg (E₁ n))
    have h₂ := sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _=>sq_nonneg (E₂ n))
    exact (add_le_add h₁ h₂).trans hError

end PrimeSquares
