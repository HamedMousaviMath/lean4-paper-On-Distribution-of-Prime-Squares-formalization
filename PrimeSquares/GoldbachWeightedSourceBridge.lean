import PrimeSquares.GoldbachWeightedMovingKernel
import PrimeSquares.GoldbachWeightedSourceOuter
import PrimeSquares.GoldbachWeightedErrorBounds

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_weighted_source_bridge (ψ : SchwartzMap ℝ ℝ) (hψ : ψ≠0)
    (K₁ K₂ : ℝ) (hK₁ : 0≤K₁) (hK₂ : 0≤K₂)
    (hV : ClassicalPrimeMertensRatios K₁) (hI : GoldbachClassicalIntervalMertens K₂) :
    ∃ K : ℝ,0<K ∧ ∀ A C η : ℝ,0<A→A+24≤C→0<η→∀ N n : ℕ,
      2≤N→2≤Real.log N→64≤n→n<N^2→((n:ℤ):ZMod 24)=12→
      (N:ℝ)^2*(Real.log N)^(-A)≤n→
      3≤(Real.log N)^C→(Real.log N)^C<(N:ℝ)^(2/9:ℝ)→
      Real.log ((Real.log N)^C)≤Real.log N→K₁/Real.log ((Real.log N)^C)≤1→
      2≤(N:ℝ)^2*(Real.log N)^(-(A+14))→
      (∀ m : ℝ,(N:ℝ)^2*(Real.log N)^(-(A+14))≤m→m≤(N:ℝ)^2→
        goldbachWeightedKernelSum (goldbachWeightedPairs N ((N:ℝ)^(8/9:ℝ))) (fun i=>2*i.1*i.2)
          (fun i=>goldbachWeightedMultiplicative ((Real.log N)^C) n i.1/((2*i.1*i.2:ℕ):ℝ)) m≤
          (goldbachHalfMeanConstant*goldbachWeightedW (9/8)+η)*
            (goldbachWeightedC ((Real.log N)^C) n/goldbachWeightedB ((Real.log N)^C) n)/
            (Real.sqrt (Real.log ((Real.log N)^C))*Real.log N*Real.sqrt (Real.log N)))→
      0<goldbachWeightedReference N ((Real.log N)^C) n ∧
      goldbachWeightedUpperSum ψ N ((Real.log N)^C) n≤
        (48*(1+K₁/Real.log ((Real.log N)^C))*(goldbachHalfMeanConstant*goldbachWeightedW (9/8)+η)+
          ((768*goldbachWeightedMassConstant K₂/(Real.log 2)^3)/(Real.log N)^3+
            (48*goldbachWeightedMassConstant K₂*K)/(Real.log N)^2))*
              goldbachWeightedReference N ((Real.log N)^C) n := by
  obtain ⟨K,hK,hOuter⟩ := goldbach_weighted_upper_outer ψ hψ K₁ hK₁ hV
  refine ⟨K,hK,?_⟩
  intro A C η hA hC hη N n hN hL hn hnN hn24 hret hR hRN hqL hKq hT hKernel
  let L := Real.log (N:ℝ)
  let R := L^C
  let q := Real.log R
  let H := (goldbachArchimedeanIntegral 1 n (N:ℝ) ((N:ℝ)^2)).re
  let density := goldbachWeightedC R n
  let base := goldbachWeightedB R n
  let S := goldbachWeightedReference N R n
  let mass := goldbachWeightedReciprocalMass N R n
  let M := goldbachWeightedMassConstant K₂
  let B := (goldbachHalfMeanConstant*goldbachWeightedW (9/8)+η)*(density/base)/
    (Real.sqrt q*L*Real.sqrt L)
  let I := goldbachWeightedPairs N ((N:ℝ)^(8/9:ℝ))
  let ℓ := fun i : ℕ×ℕ=>2*i.1*i.2
  let w := fun i : ℕ×ℕ=>goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ)
  have hL0 : 0<L := by dsimp only [L];linarith
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hR0 : 0<R := by dsimp only [R];positivity
  have hq : 1≤q := by
    have hh := Real.add_one_le_exp (1:ℝ)
    have hlogR3 := Real.log_le_log (by norm_num : (0:ℝ)<3) hR
    have h3 : (1:ℝ)≤Real.log 3 := by
      have hh' : Real.exp 1<3 := Real.exp_one_lt_three
      have hg := Real.log_le_log (Real.exp_pos 1) hh'.le
      rwa [Real.log_exp] at hg
    exact h3.trans hlogR3
  have hq0 : 0<q := by linarith
  have hd : 0<density := goldbach_weighted_C_positive R hR0.le n
  have hb : 0<base := goldbach_weighted_B_positive R hR0.le n
  have hbd : base≤density := goldbach_weighted_B_le_C R hR0.le n
  have hH := goldbach_archimedean_retained_lower A N n hN hn hnN.le hret
  have hH0 : 0≤H := goldbach_weighted_arch_real_nonneg N n 1
  have hRef := goldbach_weighted_reference_lower_scalar A L q N density H
    (by dsimp only [L];linarith) hq hN0.le hd.le hH
  have hSpos : 0<S := (by dsimp only [L] at hRef;positivity : 0<density*(N:ℝ)/(8*L^(A/2+3))).trans_le hRef
  have hmass0 : 0≤mass := sum_nonneg (fun i _=>div_nonneg
    (goldbach_weighted_multiplicative_nonneg R n _) (Nat.cast_nonneg _))
  have hM : 0<M := goldbach_weighted_mass_constant_positive K₂ hK₂
  have hmass := goldbach_weighted_mass_log_bound R ((N:ℝ)^(8/9:ℝ)) K₂ N n hK₂ hN (by linarith) hI
  have hroot := goldbach_retained_sqrt_lower A N n (by exact_mod_cast (show 1<N by omega))
    (Nat.cast_nonneg _) hret
  have hB : 0≤B := by
    have hc := goldbach_half_mean_constant_positive
    have hW := goldbach_weighted_W_nonneg
    dsimp only [B]
    positivity
  have hℓ : ∀ i∈I,0<ℓ i := fun i hi=>(goldbach_weighted_pair_levels N hN R hRN i hi).1
  have hw : ∀ i∈I,0≤w i := fun i _=>div_nonneg
    (goldbach_weighted_multiplicative_nonneg R n _) (Nat.cast_nonneg _)
  have hbase : ∀ i∈I,2≤(N:ℝ)^2/(ℓ i:ℝ) := fun i hi=>(goldbach_weighted_pair_levels N hN R hRN i hi).2.2.2.2
  have hTn := goldbach_weighted_thin_cutoff A N L n hL hN0.le hret
  have hInt := goldbach_weighted_arch_kernel_integrated I N n
    ((N:ℝ)^2*L^(-(A+14))) B ℓ w hN (by exact_mod_cast (show 4≤n by omega))
    (by exact_mod_cast hnN.le) hT hTn hB hℓ hw hbase hKernel
  have hsource := hOuter N n hN hnN R hR hRN hn24
  have hcoef : 0≤24*base*(1+K₁/q)*q := by positivity
  have hthin := goldbach_weighted_thin_error_relative A N L (Real.sqrt n) density base q
    (1+K₁/q) mass M S (by dsimp only [L];linarith) hN0 hroot hd.le hb.le hbd hq0.le hqL
    (by positivity) (by linarith) hmass0 hM.le hmass hRef
  have hsmooth := goldbach_weighted_smooth_error_relative A C N L density base K mass M S
    (by dsimp only [L];linarith) hC hN0.le hd.le hb.le hbd hK.le hmass0 hM.le hmass hRef
  have hmain : 24*base*(1+K₁/q)*q*(2*B*L*H)=
      48*(1+K₁/q)*(goldbachHalfMeanConstant*goldbachWeightedW (9/8)+η)*S := by
    have hsQ := (Real.sqrt_pos.mpr hq0).ne'
    have hsL := (Real.sqrt_pos.mpr hL0).ne'
    dsimp only [B,S,goldbachWeightedReference]
    change 24*base*(1+K₁/q)*q*(2*((goldbachHalfMeanConstant*goldbachWeightedW (9/8)+η)*(density/base)/
      (Real.sqrt q*L*Real.sqrt L))*L*H)=48*(1+K₁/q)*(goldbachHalfMeanConstant*goldbachWeightedW (9/8)+η)*
      (density*H*Real.sqrt q/Real.sqrt L)
    field_simp
    rw [Real.sq_sqrt hq0.le]
    ring
  change goldbachWeightedUpperSum ψ N R n≤_ at hsource
  change goldbachWeightedArchSum N R n≤2*B*L*H+
    (2*((N:ℝ)^2*L^(-(A+14)))/Real.sqrt n)*mass/(Real.log 2)^3 at hInt
  have hInt'' := mul_le_mul_of_nonneg_left hInt hcoef
  rw [mul_add (24*base*(1+K₁/q)*q) (2*B*L*H) _,hmain] at hInt''
  refine ⟨hSpos,?_⟩
  apply hsource.trans
  apply (add_le_add hInt'' le_rfl).trans
  have hh := add_le_add hthin hsmooth
  dsimp only [M] at hh
  nlinarith only [hh]

end PrimeSquares
