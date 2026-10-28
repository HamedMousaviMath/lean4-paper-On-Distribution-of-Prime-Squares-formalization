import PrimeSquares.GoldbachUpperSieveComplete
import PrimeSquares.GoldbachLowerFixedSieve
import PrimeSquares.GoldbachLowerCommonCircle
import PrimeSquares.GoldbachLowerMainTermSize

set_option autoImplicit false
open Finset Filter
namespace PrimeSquares

/-- Joint Section11 estimates with one cutoff, independent coefficients,
the actual main terms, arbitrary logarithmic saving and the exact sieve constants. -/
theorem goldbach_section11_complete (H : GoldbachSection11Inputs)
    (ψ : SchwartzMap ℝ ℝ) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x|→ψ x=0)
    (Cmin A₀ A : ℝ) (hA₀ : 0<A₀) (hA : 0<A) :
    ∃ B C M k K : ℝ,Cmin≤C ∧ A₀+24≤C ∧ 0≤B ∧ 0<C ∧ 0<M ∧ 0<k ∧ 0<K ∧
      ∃ η : ℝ→ℝ,Tendsto η atTop (nhds 0) ∧ ∀ ε : ℝ,0<ε→∀ᶠ N : ℕ in atTop,
      ∃ cm : ℕ→ℝ,∃ cp : ℕ→ℕ→ℝ,(∀ d : ℕ,|cm d|≤1) ∧ (∀ ℓ d : ℕ,|cp ℓ d|≤1) ∧
      (∀ n : ℕ,(n:ZMod 24)=12→(N:ℝ)^2*(Real.log N)^(-A₀)≤n→n<N^2→
        k*(N:ℝ)*(Real.log N)^(-(A₀/2+6))≤
          goldbachLowerMainTerm ψ N ((Real.log N)^C) n*
            goldbachLowerTheta ((Real.log N)^C) ((N:ℝ)^(8/9:ℝ)) n ∧
        (H.fHalf (9/8)-η N)*(goldbachLowerMainTerm ψ N ((Real.log N)^C) n*
            goldbachLowerTheta ((Real.log N)^C) ((N:ℝ)^(8/9:ℝ)) n)+
          goldbachLowerRemainderSum ψ N B ((Real.log N)^C) cm n≤
            ((goldbachSiftedValues n ((N:ℝ)^(8/9:ℝ))).card:ℝ) ∧
        (goldbachUpperSieveSum n N ((N:ℝ)^(8/9:ℝ)):ℝ)≤
          (goldbachWeightedUpperConstant (9/8)*H.FOne 2*goldbachWeightedW (9/8)+ε)*
            (goldbachLowerMainTerm ψ N ((Real.log N)^C) n*
              goldbachLowerTheta ((Real.log N)^C) ((N:ℝ)^(8/9:ℝ)) n)+
                goldbachUpperFinalError ψ N B ((Real.log N)^C) K cp n) ∧
      ((∑ n∈range (N^2),(goldbachLowerRemainderSum ψ N B ((Real.log N)^C) cm n)^2)+
        (∑ n∈range (N^2),(goldbachUpperFinalError ψ N B ((Real.log N)^C) K cp n)^2))≤
          M*(N:ℝ)^4*(Real.log N)^(-A) := by
  obtain ⟨B,C,M,hCmin,hB,hC,hM,hCircle⟩ := goldbach_sieve_circle_bound_exists_above
    (max Cmin (A₀+24)) H.siegelWalfisz H.bombieriVinogradov H.minorArcs ψ hψ hsψ hA
  have hCA : A₀+24≤C := (le_max_right _ _).trans hCmin
  obtain ⟨K,hK,hUpper⟩ := goldbach_upper_sieve_fixed_circle H ψ hψ B C M A₀ A hB hCA hA₀ hCircle
  obtain ⟨η,hη,hLower⟩ := goldbach_lower_sieve_fixed_analytic ψ hψ B C H.K H.K₀ H.c H.sstar H.K₁ H.δ
    H.fHalf H.FHalf hC H.K_nonneg H.K₀_nonneg H.c_pos H.δ_pos H.intervalHalf H.fundamental
      H.coefficientHalf H.halfContinuous
  obtain ⟨k,hk,hMain⟩ := (goldbach_lower_main_term_size ψ hψ A₀ H.K hA₀ H.K_nonneg H.intervalHalf).2 C
    (by linarith)
  refine ⟨B,C,5*M+2*K^2,k,K,(le_max_left _ _).trans hCmin,hCA,hB,hC,by positivity,hk,hK,η,hη,?_⟩
  intro ε hε
  filter_upwards [hCircle,hLower,hMain,hUpper ε hε] with N hCircle hLower hMain hUpper
  obtain ⟨cm,hcm,hLower⟩ := hLower
  obtain ⟨cp,hcp,hUpper,hError⟩ := hUpper
  refine ⟨cm,cp,hcm,hcp,?_,?_⟩
  · intro n hn hret hnN
    refine ⟨hMain n hn hret hnN,?_,hUpper n hn hret hnN⟩
    convert hLower n hn using 1
    · dsimp only [goldbachLowerSiftingLimit];ring
    · rfl
  · have hLowErr := goldbach_lower_remainder_from_circle ψ N hCircle.1 B ((Real.log N)^C) M A hCircle.2 cm hcm
    calc
      _≤M*(N:ℝ)^4*(Real.log N)^(-A)+(4*M+2*K^2)*(N:ℝ)^4*(Real.log N)^(-A) :=
        add_le_add hLowErr hError
      _=_ := by ring

end PrimeSquares
