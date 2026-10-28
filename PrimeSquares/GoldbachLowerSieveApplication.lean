import PrimeSquares.GoldbachLowerSieveRemainder

set_option autoImplicit false
open Finset Filter
open scoped SchwartzMap
namespace PrimeSquares

noncomputable def goldbachLowerTheta (R z : ℝ) (n : ℕ) : ℝ :=
  ∏ p∈goldbachLowerSievePrimes z,(1-goldbachLowerDensity R n p)

noncomputable def goldbachLowerSieveError (B C K K₀ c K₁ δ N : ℝ) : ℝ :=
  K₁*(Real.log (goldbachLowerOuterLevel B N))^(-δ)+
    (K₀*Real.exp (-c*goldbachPresievePreliminaryS C N))*
      (((1+K/Real.log 2)*(2/Real.log 2)^((1:ℝ)/2))*(Real.log N)^((1:ℝ)/2))^2

theorem goldbach_lower_theta_positive (R z : ℝ) (n : ℕ) :
    0<goldbachLowerTheta R z n := by
  apply prod_pos
  intro p hp
  exact sub_pos.mpr (goldbach_lower_prime_density_range R n
    ((mem_goldbach_lower_sieve_primes z p).mp hp).1).2

theorem goldbach_lower_presieve_application
    (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0) (N : ℕ) (hN : 2≤N)
    (B C K K₀ c K₁ δ : ℝ) (f F : ℝ→ℝ)
    (hR : 3≤(Real.log N)^C) (hM : GoldbachClassicalIntervalMertens K)
    (hAt : GoldbachCorrectedPresieveAt.{0} N C 2 2 ((1:ℝ)/2) K K₀ c K₁ δ
      (goldbachLowerSiftingLimit N) (goldbachLowerOuterLevel B N)
      (goldbachLowerPreliminaryPrimes ((Real.log N)^C) (goldbachLowerSiftingLimit N))
      (goldbachLowerOuterPrimes ((Real.log N)^C) (goldbachLowerSiftingLimit N)) f F) :
    ∃ cm : ℕ→ℝ,(∀ d : ℕ,|cm d|≤1) ∧ ∀ n : ℕ,(n:ZMod 24)=12→
      goldbachLowerMainTerm ψ N ((Real.log N)^C) n*
        goldbachLowerTheta ((Real.log N)^C) (goldbachLowerSiftingLimit N) n*
        (f (Real.log (goldbachLowerOuterLevel B N)/Real.log (goldbachLowerSiftingLimit N))-
          goldbachLowerSieveError B C K K₀ c K₁ δ N)+
        goldbachLowerRemainderSum ψ N B ((Real.log N)^C) cm n≤
          ((goldbachSiftedValues n (goldbachLowerSiftingLimit N)).card:ℝ) := by
  classical
  dsimp only [GoldbachCorrectedPresieveAt] at hAt
  obtain ⟨cm,cp,hcoeff,_,hbound⟩ := hAt
  refine ⟨cm,fun d=>(hcoeff d).1,?_⟩
  intro n hn
  let R := (Real.log (N:ℝ))^C
  let z := goldbachLowerSiftingLimit N
  let P := goldbachLowerPreliminaryPrimes R z
  let Q := goldbachLowerOuterPrimes R z
  let g := goldbachPrimeDensityProduct (goldbachLowerDensity R (n:ℤ))
  let r := fun d : ℕ=>if d=0 then 0 else
    (goldbachFullRemainder ψ N 1 (24*d) (goldbachLowerSieveResidue d) R n).re
  have hsplit := goldbach_lower_prime_split R z
  have hg : GoldbachMultiplicativeDensityOn (P∪Q) g := by
    rw [show P∪Q=goldbachLowerSievePrimes z from hsplit.2]
    exact goldbach_lower_density_multiplicative R z n
  have hX := goldbach_lower_main_term_nonneg ψ hψ N hN R hR n hn
  have hdata : ∀ d : ℕ,Squarefree d→d.primeFactors⊆P∪Q→
      (d:ℝ)<Real.exp ((Real.log (Real.log N))^3)*goldbachLowerOuterLevel B N→
      goldbachSequenceDivisorCount (goldbachAdmissibleRepresentations n) (fun t=>t-1) d=
        goldbachLowerMainTerm ψ N R n*g d+r d := by
    intro d hd hs _
    have hs' : ∀ p∈d.primeFactors,3<p := by
      intro p hp
      have h := hs hp
      rw [show P∪Q=goldbachLowerSievePrimes z from hsplit.2] at h
      exact ((mem_goldbach_lower_sieve_primes z p).mp h).1.2.1
    simpa only [g,r,ite_eq_right hd.ne_zero] using
      goldbach_lower_divisor_real_identity ψ N n d R hR hn hd hs'
  have hb := (hbound g hg (goldbach_lower_preliminary_dimension K R z _ hM n)
    (goldbach_lower_outer_dimension K R z hM n) ℕ (goldbachAdmissibleRepresentations n)
    (fun t=>t-1) (goldbachLowerMainTerm ψ N R n) hX r hdata).1
  have htheta : goldbachSieveProduct P g*goldbachSieveProduct Q g=goldbachLowerTheta R z n := by
    dsimp only [goldbachSieveProduct]
    rw [←prod_union hsplit.1,hsplit.2]
    apply prod_congr rfl
    intro p hp
    have hprime := ((mem_goldbach_lower_sieve_primes z p).mp hp).1.1
    simp only [g,goldbachPrimeDensityProduct,hprime.primeFactors,prod_singleton]
  have hmain : goldbachLowerMainTerm ψ N R n*goldbachSieveProduct P g*
      goldbachSieveProduct Q g=goldbachLowerMainTerm ψ N R n*goldbachLowerTheta R z n := by
    rw [mul_assoc,htheta]
  change goldbachLowerMainTerm ψ N R n*goldbachSieveProduct P g*goldbachSieveProduct Q g*
    (f (Real.log (goldbachLowerOuterLevel B N)/Real.log z)-goldbachLowerSieveError B C K K₀ c K₁ δ N)+
    (∑ d∈range (Nat.ceil (Real.exp ((Real.log (Real.log N))^3)*goldbachLowerOuterLevel B N)),cm d*r d)≤
      goldbachSequenceSiftedCount (goldbachAdmissibleRepresentations n) (fun t=>t-1) (P∪Q) at hb
  rw [hmain,goldbach_lower_product_level,show P∪Q=goldbachLowerSievePrimes z from hsplit.2,
    goldbach_lower_sifted_sequence] at hb
  dsimp only [r] at hb
  rw [goldbach_lower_remainder_zero_extension] at hb
  exact hb.trans (by exact_mod_cast goldbach_fixed_lower_count n z)

theorem goldbach_lower_sieve_complete
    (HSW : RawPrimeSiegelWalfiszInput) (HBV : RawPrimeBombieriVinogradovInput)
    (Hminor : UniformRenGhoshInputs) (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x|→ψ x=0)
    (K K₀ c sstar K₁ δ : ℝ) (f F : ℝ→ℝ)
    (hK : 0≤K) (hK₀ : 0≤K₀) (hc : 0<c) (hδ : 0<δ)
    (hM : GoldbachClassicalIntervalMertens K)
    (hpre : GoldbachClassicalFundamentalInput 2 K K₀ c sstar)
    (houter : GoldbachClassicalCoefficientInput ((1:ℝ)/2) K K₁ δ f F)
    (hf : ContinuousAt f ((9:ℝ)/8)) {A : ℝ} (hA : 0<A) :
    ∃ B C M : ℝ,0≤B ∧ 0<C ∧ 0<M ∧ ∃ η : ℝ→ℝ,
      Tendsto η atTop (nhds 0) ∧ ∀ᶠ N : ℕ in atTop,
        ∃ cm : ℕ→ℝ,(∀ d : ℕ,|cm d|≤1) ∧
          (∀ n : ℕ,(n:ZMod 24)=12→
            goldbachLowerMainTerm ψ N ((Real.log N)^C) n*
              goldbachLowerTheta ((Real.log N)^C) (goldbachLowerSiftingLimit N) n*
              (f ((9:ℝ)/8)-η N)+goldbachLowerRemainderSum ψ N B ((Real.log N)^C) cm n≤
                ((goldbachSiftedValues n (goldbachLowerSiftingLimit N)).card:ℝ)) ∧
          (∑ n∈range (N^2),(goldbachLowerRemainderSum ψ N B ((Real.log N)^C) cm n)^2)≤
            M*(N:ℝ)^4*(Real.log N)^(-A) := by
  classical
  obtain ⟨B,C,M,hB,hC,hMpos,N₀,hN₀,hRem⟩ :=
    goldbach_lower_remainder_mean_square HSW HBV Hminor ψ hψ hsψ hA
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
  refine ⟨B,C,M,hB,hC,hMpos,η,hη,?_⟩
  have hRlarge : ∀ᶠ N : ℝ in atTop,3≤(Real.log N)^C :=
    ((tendsto_rpow_atTop hC).comp Real.tendsto_log_atTop).eventually_ge_atTop 3
  have hNat : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hNat.eventually hAt,hNat.eventually hRlarge,eventually_ge_atTop N₀] with N hAt hR hN
  have hN2 : 2≤N := by omega
  obtain ⟨cm,hcm,hpoint⟩ := goldbach_lower_presieve_application ψ hψ N hN2
    B C K K₀ c K₁ δ f F hR hM hAt
  refine ⟨cm,hcm,?_,hRem N hN B le_rfl cm hcm⟩
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
