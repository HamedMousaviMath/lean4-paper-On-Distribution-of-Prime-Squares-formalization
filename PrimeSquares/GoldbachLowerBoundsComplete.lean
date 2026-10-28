import PrimeSquares.GoldbachLowerMainTermSize
import PrimeSquares.GoldbachLowerCutoffFreedom

set_option autoImplicit false
open Finset Filter
open scoped SchwartzMap
namespace PrimeSquares

theorem goldbach_lower_bounds_complete
    (HSW : RawPrimeSiegelWalfiszInput) (HBV : RawPrimeBombieriVinogradovInput)
    (Hminor : UniformRenGhoshInputs) (ψ : SchwartzMap ℝ ℝ) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x|→ψ x=0)
    (K K₀ c sstar K₁ δ : ℝ) (f F : ℝ→ℝ)
    (hK : 0≤K) (hK₀ : 0≤K₀) (hc : 0<c) (hδ : 0<δ)
    (hMertens : GoldbachClassicalIntervalMertens K)
    (hpre : GoldbachClassicalFundamentalInput 2 K K₀ c sstar)
    (houter : GoldbachClassicalCoefficientInput ((1:ℝ)/2) K K₁ δ f F)
    (hf : ContinuousAt f ((9:ℝ)/8)) (A₀ A : ℝ) (hA₀ : 0<A₀) (hA : 0<A) :
    ∃ B C M k : ℝ,A₀+6≤C ∧ 0≤B ∧ 0<C ∧ 0<M ∧ 0<k ∧
      ∃ η : ℝ→ℝ,Tendsto η atTop (nhds 0) ∧ ∀ᶠ N : ℕ in atTop,
        ∃ cm : ℕ→ℝ,(∀ d : ℕ,|cm d|≤1) ∧
          (∀ n : ℕ,(n:ZMod 24)=12→(N:ℝ)^2*(Real.log N)^(-A₀)≤n→n<N^2→
            k*(N:ℝ)*(Real.log N)^(-(A₀/2+6))≤
              goldbachLowerMainTerm ψ N ((Real.log N)^C) n*
                goldbachLowerTheta ((Real.log N)^C) (goldbachLowerSiftingLimit N) n ∧
            goldbachLowerMainTerm ψ N ((Real.log N)^C) n*
              goldbachLowerTheta ((Real.log N)^C) (goldbachLowerSiftingLimit N) n*
              (f ((9:ℝ)/8)-η N)+goldbachLowerRemainderSum ψ N B ((Real.log N)^C) cm n≤
                ((goldbachSiftedValues n (goldbachLowerSiftingLimit N)).card:ℝ)) ∧
          (∑ n∈range (N^2),(goldbachLowerRemainderSum ψ N B ((Real.log N)^C) cm n)^2)≤
            M*(N:ℝ)^4*(Real.log N)^(-A) := by
  obtain ⟨B,C,M,hCmin,hB,hC,hM,η,hη,hLower⟩ := goldbach_lower_sieve_complete_above (A₀+6)
    HSW HBV Hminor ψ hψ hsψ K K₀ c sstar K₁ δ f F hK hK₀ hc hδ hMertens hpre houter hf hA
  obtain ⟨k,hk,hMain⟩ := (goldbach_lower_main_term_size ψ hψ A₀ K hA₀ hK hMertens).2 C hCmin
  refine ⟨B,C,M,k,hCmin,hB,hC,hM,hk,η,hη,?_⟩
  filter_upwards [hLower,hMain] with N hLower hMain
  obtain ⟨cm,hcm,hPoint,hError⟩ := hLower
  exact ⟨cm,hcm,fun n hn hret hnN=>⟨hMain n hn hret hnN,hPoint n hn⟩,hError⟩

theorem goldbach_half_sieve_closed_value_positive (γ : ℝ) :
    0<Real.sqrt (8*Real.exp γ/(9*Real.pi))*Real.log 2 := by
  have hp := Real.pi_pos
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  exact mul_pos (Real.sqrt_pos.mpr (by positivity)) hl

theorem goldbach_lower_count_from_main_and_error (count T v E f η : ℝ)
    (hT : 0<T) (hf : 0<f) (hη : η≤f/2) (hMain : T≤v)
    (hLower : v*(f-η)+E≤count) (hE : -(T*f/4)≤E) :
    T*f/4≤count := by
  have hv : 0≤v := hT.le.trans hMain
  have hprod := mul_le_mul hMain (show f/2≤f-η by linarith) (by linarith : 0≤f/2) hv
  nlinarith only [hprod,hLower,hE]

theorem goldbach_lower_bad_card (I : Finset ℕ) (count v E : ℕ→ℝ) (T f η : ℝ)
    (hT : 0<T) (hf : 0<f) (hη : η≤f/2)
    (hMain : ∀ n∈I,T≤v n) (hLower : ∀ n∈I,v n*(f-η)+E n≤count n) :
    (((I.filter (fun n=>count n<T*f/4)).card:ℝ))*(T*f/4)^2≤∑ n∈I,(E n)^2 := by
  classical
  let J := I.filter (fun n=>count n<T*f/4)
  have hpoint : ∀ n∈J,(T*f/4)^2≤(E n)^2 := by
    intro n hn
    obtain ⟨hn,hcount⟩ := mem_filter.mp hn
    have hv : 0≤v n := hT.le.trans (hMain n hn)
    have hprod := mul_le_mul (hMain n hn) (show f/2≤f-η by linarith) (by linarith : 0≤f/2) hv
    have hneg : E n< -(T*f/4) := by nlinarith only [hprod,hLower n hn,hcount]
    have hq : 0≤T*f/4 := by positivity
    have hh := mul_nonneg (show 0≤ -E n-T*f/4 by linarith)
      (show 0≤ -E n+T*f/4 by linarith)
    nlinarith only [hh]
  calc
    _=∑ n∈J,(T*f/4)^2 := by simp only [J,sum_const,nsmul_eq_mul]
    _≤∑ n∈J,(E n)^2 := sum_le_sum hpoint
    _≤_ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intro n _ _;exact sq_nonneg _)

end PrimeSquares
