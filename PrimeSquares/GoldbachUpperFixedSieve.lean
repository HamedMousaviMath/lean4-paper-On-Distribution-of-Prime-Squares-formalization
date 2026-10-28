import PrimeSquares.GoldbachUpperPresieveApplication
import PrimeSquares.GoldbachWeightedSourceOuter

set_option autoImplicit false
open Finset Filter
namespace PrimeSquares

theorem goldbach_upper_fixed_sieve_analytic
    (ψ : SchwartzMap ℝ ℝ) (hψ : ψ≠0)
    (B C K K₀ c sstar K₁ δ : ℝ) (f F : ℝ→ℝ)
    (hB : 0≤B) (hC : 0<C) (hK : 0≤K) (hK₀ : 0≤K₀) (hc : 0<c) (hδ : 0<δ)
    (hM : GoldbachClassicalFullIntervalMertens K)
    (hpre : GoldbachClassicalFundamentalInput 2 K K₀ c sstar)
    (houter : GoldbachClassicalCoefficientInput 1 K K₁ δ f F)
    (hF : ContinuousAt F 2) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∃ cp : ℕ→ℕ→ℝ,(∀ ℓ d : ℕ,|cp ℓ d|≤1) ∧
      ∀ n : ℕ,0<n→n<N^2→(n:ZMod 24)=12→
        (goldbachFixedUpperSieveSum n N ((N:ℝ)^(8/9:ℝ)):ℝ)≤
          (F 2+ε)*goldbachWeightedUpperSum ψ N ((Real.log N)^C) n+
            goldbachUpperRemainderSum ψ N B ((Real.log N)^C) cp n := by
  classical
  have hNat : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hR : ∀ᶠ N : ℝ in atTop,3≤(Real.log N)^C :=
    ((tendsto_rpow_atTop hC).comp Real.tendsto_log_atTop).eventually_ge_atTop 3
  have hz : ∀ᶠ N : ℕ in atTop,(3:ℝ)<(N:ℝ)^(8/9:ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<8/9)).comp hNat).eventually_gt_atTop 3
  filter_upwards [hNat.eventually (goldbach_upper_presieving_uniform B C K K₀ c sstar K₁ δ f F
    hB hC hK hK₀ hc hδ hpre houter hF ε hε),hNat.eventually hR,hz,eventually_ge_atTop (2:ℕ)]
    with N hAt hR hz hN
  have hchoose : ∀ ℓ : ℕ,∃ cp : ℕ→ℝ,(∀ d : ℕ,|cp d|≤1) ∧
      (ℓ∈goldbachClosedLSet N ((N:ℝ)^(8/9:ℝ))→∀ n : ℕ,0<n→n<N^2→(n:ZMod 24)=12→
        ((goldbachFixedUpperSifted n N ℓ).card:ℝ)≤
          goldbachUpperMainTerm ψ N ((Real.log N)^C) ℓ n*
            goldbachUpperTheta ((Real.log N)^C) (goldbachUpperSieveLimit N ℓ) ℓ n*(F 2+ε)+
              goldbachUpperSingleRemainder ψ N ℓ B ((Real.log N)^C) cp n) := by
    intro ℓ
    by_cases hℓ : ℓ∈goldbachClosedLSet N ((N:ℝ)^(8/9:ℝ))
    · have hpos := goldbach_closed_multiplier_positive hℓ
      obtain ⟨_,_,_,_,_,_,_,hbound,_,_,_⟩ := goldbach_weighted_multiplier_geometry hN hℓ
      obtain ⟨cp,hcp,hpoint⟩ := goldbach_upper_presieve_application ψ hψ N hN ℓ hℓ hz
        B C K K₀ c K₁ δ ε f F hR hM (hAt ℓ hpos hbound.le).1 (hAt ℓ hpos hbound.le).2
      exact ⟨cp,hcp,fun _=>hpoint⟩
    · exact ⟨fun _=>0,by intro d;norm_num,fun h=>False.elim (hℓ h)⟩
  choose cp hcp hpoint using hchoose
  refine ⟨cp,hcp,?_⟩
  intro n hn hnN hn24
  have hh := sum_le_sum (fun ℓ hℓ=>hpoint ℓ hℓ n hn hnN hn24)
  simpa only [goldbachFixedUpperSieveSum,Nat.cast_sum,goldbachWeightedUpperSum,
    goldbachUpperSieveLimit,goldbachUpperSieveLevel,goldbachUpperRemainderSum,sum_add_distrib,←sum_mul,mul_comm (F 2+ε)] using hh

end PrimeSquares
