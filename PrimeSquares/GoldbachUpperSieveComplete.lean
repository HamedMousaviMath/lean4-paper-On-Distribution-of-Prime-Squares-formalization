import PrimeSquares.GoldbachUpperFixedSieve
import PrimeSquares.GoldbachUpperSieveErrors
import PrimeSquares.GoldbachSection11Inputs

set_option autoImplicit false
open Finset Filter
namespace PrimeSquares

theorem goldbach_upper_sieve_fixed_circle (H : GoldbachSection11Inputs)
    (ψ : SchwartzMap ℝ ℝ) (hψ : ψ≠0) (B C M A₀ A : ℝ)
    (hB : 0≤B) (hC : A₀+24≤C) (hA₀ : 0<A₀)
    (hCircle : ∀ᶠ N : ℕ in atTop,4≤N ∧ GoldbachSieveCircleBoundAt ψ N B ((Real.log N)^C) M A) :
    ∃ K : ℝ,0<K ∧ ∀ η : ℝ,0<η→∀ᶠ N : ℕ in atTop,
      ∃ cp : ℕ→ℕ→ℝ,(∀ ℓ d : ℕ,|cp ℓ d|≤1) ∧
      (∀ n : ℕ,(n:ZMod 24)=12→(N:ℝ)^2*(Real.log N)^(-A₀)≤n→n<N^2→
        (goldbachUpperSieveSum n N ((N:ℝ)^(8/9:ℝ)):ℝ)≤
          (goldbachWeightedUpperConstant (9/8)*H.FOne 2*goldbachWeightedW (9/8)+η)*
            (goldbachLowerMainTerm ψ N ((Real.log N)^C) n*
              goldbachLowerTheta ((Real.log N)^C) ((N:ℝ)^(8/9:ℝ)) n)+
                goldbachUpperFinalError ψ N B ((Real.log N)^C) K cp n) ∧
      (∑ n∈range (N^2),(goldbachUpperFinalError ψ N B ((Real.log N)^C) K cp n)^2)≤
        (4*M+2*K^2)*(N:ℝ)^4*(Real.log N)^(-A) := by
  classical
  have hC0 : 0<C := by linarith
  obtain ⟨K,hK,hCompare⟩ := goldbach_fixed_sieve_sets (by norm_num : (0:ℝ)<1/4)
  refine ⟨K,hK,?_⟩
  intro η hη
  let a := goldbachWeightedUpperConstant (9/8)*goldbachWeightedW (9/8)
  let G := fun ε : ℝ=>(H.FOne 2+ε)*(a+ε)
  have hG : ContinuousAt G 0 := by dsimp only [G];fun_prop
  obtain ⟨ε,hε,_,hGe⟩ := goldbach_choose_positive_tolerance G (H.FOne 2*a+η) hG
    (by dsimp [G];linarith)
  have hF : 0<H.FOne 2 := by rw [H.oneValue];exact Real.exp_pos _
  have hNat : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hR : ∀ᶠ N : ℝ in atTop,3≤(Real.log N)^C :=
    ((tendsto_rpow_atTop hC0).comp Real.tendsto_log_atTop).eventually_ge_atTop 3
  filter_upwards [hCircle,hNat.eventually hR,goldbach_upper_arithmetic_error_eventually A,
    goldbach_upper_fixed_sieve_analytic ψ hψ B C H.K H.K₀ H.c H.sstar H.K₁ H.δ H.fOne H.FOne
      hB hC0 H.K_nonneg H.K₀_nonneg H.c_pos H.δ_pos H.intervalFull H.fundamental H.coefficientOne
        H.oneContinuous ε hε,
    goldbach_weighted_upper_main_term_complete H.halfMean H.K H.K H.K H.K_nonneg H.K_nonneg
      H.K_nonneg H.primeLogs H.primeRatios H.intervalHalf ψ hψ A₀ hA₀ C hC ε hε]
    with N hCircle hR hLog hFixed hWeighted
  obtain ⟨hN,hCircle⟩ := hCircle
  obtain ⟨cp,hcp,hFixed⟩ := hFixed
  refine ⟨cp,hcp,?_,goldbach_upper_error_square_sum ψ N hN B ((Real.log N)^C) M A K hLog cp
    (goldbach_upper_remainder_from_circle ψ N hN B ((Real.log N)^C) M A hCircle cp hcp)⟩
  intro n hn24 hret hnN
  have hn0 : 0<n := by
    have hh := (ZMod.natCast_eq_natCast_iff n 12 24).mp (by simpa only [Nat.cast_ofNat] using hn24)
    change n%24=12%24 at hh
    norm_num at hh
    omega
  have hT : 0≤goldbachLowerMainTerm ψ N ((Real.log N)^C) n*
      goldbachLowerTheta ((Real.log N)^C) ((N:ℝ)^(8/9:ℝ)) n :=
    mul_nonneg (goldbach_lower_main_term_nonneg ψ hψ N (by omega) _ hR n hn24)
      (goldbach_lower_theta_positive _ _ n).le
  have hw := mul_le_mul_of_nonneg_left (hWeighted n hn24 hret hnN) (show 0≤H.FOne 2+ε by linarith)
  have hc' : (H.FOne 2+ε)*(a+ε)≤
      goldbachWeightedUpperConstant (9/8)*H.FOne 2*goldbachWeightedW (9/8)+η := by
    convert hGe.le using 1;dsimp only [a];ring
  have hMain := mul_le_mul_of_nonneg_right hc' hT
  have hp := (hCompare N n (by omega) hn0 hnN.le ((N:ℝ)^(8/9:ℝ))).2
  have hf := hFixed n hn0 hnN hn24
  unfold goldbachUpperFinalError
  nlinarith only [hp,hf,hw,hMain]

theorem goldbach_upper_sieve_complete (H : GoldbachSection11Inputs)
    (ψ : SchwartzMap ℝ ℝ) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x|→ψ x=0)
    (Cmin A₀ A : ℝ) (hA₀ : 0<A₀) (hA : 0<A) :
    ∃ B C M K : ℝ,Cmin≤C ∧ A₀+24≤C ∧ 0≤B ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀ η : ℝ,0<η→∀ᶠ N : ℕ in atTop,
      ∃ cp : ℕ→ℕ→ℝ,(∀ ℓ d : ℕ,|cp ℓ d|≤1) ∧
      (∀ n : ℕ,(n:ZMod 24)=12→(N:ℝ)^2*(Real.log N)^(-A₀)≤n→n<N^2→
        (goldbachUpperSieveSum n N ((N:ℝ)^(8/9:ℝ)):ℝ)≤
          (goldbachWeightedUpperConstant (9/8)*H.FOne 2*goldbachWeightedW (9/8)+η)*
            (goldbachLowerMainTerm ψ N ((Real.log N)^C) n*
              goldbachLowerTheta ((Real.log N)^C) ((N:ℝ)^(8/9:ℝ)) n)+
                goldbachUpperFinalError ψ N B ((Real.log N)^C) K cp n) ∧
      (∑ n∈range (N^2),(goldbachUpperFinalError ψ N B ((Real.log N)^C) K cp n)^2)≤
        M*(N:ℝ)^4*(Real.log N)^(-A) := by
  obtain ⟨B,C,M,hCmin,hB,hC,hM,hCircle⟩ := goldbach_sieve_circle_bound_exists_above
    (max Cmin (A₀+24)) H.siegelWalfisz H.bombieriVinogradov H.minorArcs ψ hψ hsψ hA
  have hCA : A₀+24≤C := (le_max_right _ _).trans hCmin
  obtain ⟨K,hK,hUpper⟩ := goldbach_upper_sieve_fixed_circle H ψ hψ B C M A₀ A hB hCA hA₀ hCircle
  refine ⟨B,C,4*M+2*K^2,K,(le_max_left _ _).trans hCmin,hCA,hB,hC,?_,hK,hUpper⟩
  positivity

end PrimeSquares
