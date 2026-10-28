import PrimeSquares.GoldbachLowerCutoffFreedom

set_option autoImplicit false
open Finset Filter
open scoped SchwartzMap
namespace PrimeSquares

theorem goldbach_lower_sieve_fixed_analytic
    (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0) (B C K K₀ c sstar K₁ δ : ℝ) (f F : ℝ→ℝ)
    (hC : 0<C) (hK : 0≤K) (hK₀ : 0≤K₀) (hc : 0<c) (hδ : 0<δ)
    (hM : GoldbachClassicalIntervalMertens K)
    (hpre : GoldbachClassicalFundamentalInput 2 K K₀ c sstar)
    (houter : GoldbachClassicalCoefficientInput ((1:ℝ)/2) K K₁ δ f F)
    (hf : ContinuousAt f ((9:ℝ)/8)) :
    ∃ η : ℝ→ℝ,Tendsto η atTop (nhds 0) ∧ ∀ᶠ N : ℕ in atTop,
      ∃ cm : ℕ→ℝ,(∀ d : ℕ,|cm d|≤1) ∧
        ∀ n : ℕ,(n:ZMod 24)=12→
          goldbachLowerMainTerm ψ N ((Real.log N)^C) n*
            goldbachLowerTheta ((Real.log N)^C) (goldbachLowerSiftingLimit N) n*
            (f ((9:ℝ)/8)-η N)+goldbachLowerRemainderSum ψ N B ((Real.log N)^C) cm n≤
              ((goldbachSiftedValues n (goldbachLowerSiftingLimit N)).card:ℝ) := by
  classical
  let z := goldbachLowerSiftingLimit
  let D₁ := goldbachLowerOuterLevel B
  let P := fun N : ℝ=>goldbachLowerPreliminaryPrimes ((Real.log N)^C) (z N)
  let Q := fun N : ℝ=>goldbachLowerOuterPrimes ((Real.log N)^C) (z N)
  have hlarge : ∀ᶠ N : ℝ in atTop,1<N ∧ Disjoint (P N) (Q N) ∧
      Real.exp (C*Real.log (Real.log N))+1≤z N ∧ z N≤D₁ N ∧ D₁ N≤N^(2:ℝ) ∧
      (∀ p∈P N,p.Prime ∧ (p:ℝ)<Real.exp (C*Real.log (Real.log N))+1) ∧
      (∀ p∈Q N,p.Prime ∧ (p:ℝ)<z N) := by
    filter_upwards [goldbach_lower_sieve_levels_eventually B C] with N hN
    obtain ⟨hN,hR,hD,hU⟩ := hN
    have he := goldbach_presieve_source_R N C hN
    refine ⟨hN,(goldbach_lower_prime_split _ _).1,?_,hD,hU,?_,?_⟩
    · simpa only [←he] using hR
    · intro p hp
      obtain ⟨hp,hpR⟩ := mem_filter.mp hp
      refine ⟨((mem_goldbach_lower_sieve_primes (z N) p).mp hp).1.1,?_⟩
      rw [←he]
      linarith
    · intro p hp
      have hs := (mem_goldbach_lower_sieve_primes (z N) p).mp (mem_filter.mp hp).1
      exact ⟨hs.1.1,hs.2⟩
  obtain ⟨hε,hAt⟩ := goldbach_corrected_presieving.{0} C 2 2 ((1:ℝ)/2) K K₀ c sstar K₁ δ
    z D₁ P Q f F hC (by norm_num) (by norm_num) hK hK₀ hc hδ hpre houter hlarge
  let η := fun N : ℝ=>goldbachLowerSieveError B C K K₀ c K₁ δ N+
    |f (Real.log (D₁ N)/Real.log (z N))-f ((9:ℝ)/8)|
  have hflim := hf.tendsto.comp (goldbach_lower_sieve_parameter_tendsto B)
  have hη : Tendsto η atTop (nhds 0) := by
    have hh := hε.add ((hflim.sub_const (f ((9:ℝ)/8))).abs)
    simpa only [η,goldbachLowerSieveError,z,D₁,sub_self,abs_zero,add_zero,Function.comp_def] using hh
  refine ⟨η,hη,?_⟩
  have hRlarge : ∀ᶠ N : ℝ in atTop,3≤(Real.log N)^C :=
    ((tendsto_rpow_atTop hC).comp Real.tendsto_log_atTop).eventually_ge_atTop 3
  have hNat : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hNat.eventually hAt,hNat.eventually hRlarge,eventually_ge_atTop (2:ℕ)] with N hAt hR hN
  have hN2 : 2≤N := hN
  obtain ⟨cm,hcm,hpoint⟩ := goldbach_lower_presieve_application ψ hψ N hN2
    B C K K₀ c K₁ δ f F hR hM hAt
  refine ⟨cm,hcm,?_⟩
  intro n hn
  have hp := hpoint n hn
  have hnonneg := mul_nonneg (goldbach_lower_main_term_nonneg ψ hψ N hN2 _ hR n hn)
    (goldbach_lower_theta_positive ((Real.log N)^C) (z N) n).le
  have hcoef : f ((9:ℝ)/8)-η N≤
      f (Real.log (D₁ N)/Real.log (z N))-goldbachLowerSieveError B C K K₀ c K₁ δ N := by
    dsimp only [η]
    linarith only [neg_abs_le (f (Real.log (D₁ N)/Real.log (z N))-f ((9:ℝ)/8))]
  exact (add_le_add (mul_le_mul_of_nonneg_left hcoef hnonneg) le_rfl).trans hp

end PrimeSquares
