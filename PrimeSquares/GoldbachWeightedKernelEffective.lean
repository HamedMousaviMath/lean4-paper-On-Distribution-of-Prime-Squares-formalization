import PrimeSquares.GoldbachWeightedScalarBounds
import PrimeSquares.GoldbachWeightedKernelCoefficient
import PrimeSquares.GoldbachWeightedHarmonicCutoff

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_weighted_kernel_effective (hT : ClassicalHalfMeanValueInput)
    (K₀ K₁ K₂ : ℝ) (hK₀ : 0≤K₀) (hK₁ : 0≤K₁) (hK₂ : 0≤K₂)
    (hM : ClassicalPrimeLogMertens K₀) (hV : ClassicalPrimeMertensRatios K₁)
    (hI : GoldbachClassicalIntervalMertens K₂) :
    ∃ K δ D A₀ P : ℝ,0<K ∧ 0<δ ∧ 1<D ∧ 0<A₀ ∧ 0<P ∧
      ∀ C ε : ℝ,0<C→0<ε→ε≤1/2→∀ N : ℕ,2≤N→
      9≤Real.log N→K₀≤Real.log N→Real.exp 2≤(Real.log N)^C→
      2≤Real.exp (Real.sqrt (Real.log N))→
      Real.exp 16<Real.exp (Real.sqrt (Real.log N))→
      Real.exp (Real.sqrt (Real.log N))≤Real.exp ((2*Real.log N)/9)/2→
      (((Real.log N)^C)^D)≤Real.exp (Real.sqrt (Real.log N))→
      1/Real.sqrt (Real.log (Real.exp (Real.sqrt (Real.log N))))<ε→
      (Real.log N)^C≤(Real.exp (Real.sqrt (Real.log N)))^ε→
      6*Real.log ((Real.log N)^C)+10*K₀≤ε^2*Real.log (Real.exp (Real.sqrt (Real.log N)))→
      Real.log N≤Real.exp ((8/9:ℝ)*Real.log N)→∀ n : ℤ,
      goldbachWeightedFixedKernel N ((N:ℝ)^(8/9:ℝ)) ((Real.log N)^C) n≤
        ((goldbachWeightedC ((Real.log N)^C) n/goldbachWeightedB ((Real.log N)^C) n)/
          (Real.sqrt (C*Real.log (Real.log N))*Real.log N*Real.sqrt (Real.log N)))*
          goldbachWeightedKernelCoefficient (C*Real.log (Real.log N)) P A₀ K δ K₀ K₁ ε (Real.log N) := by
  obtain ⟨K,δ,hK,hδ,hmean⟩ := goldbach_weighted_mean_interval hT K₀ K₁ hK₀ hK₁ hM hV
  obtain ⟨D,A₀,P,hD,hA₀,hP,hharm⟩ := goldbach_weighted_harmonic_cutoff hT K₀ K₁ K₂
    hK₀ hK₁ hK₂ hM hV hI
  refine ⟨K,δ,D,A₀,P,hK,hδ,hD,hA₀,hP,?_⟩
  intro C ε hC hε hεB N hN hL hKL hR ha ha16 haU hRD hInv hRa hbudget hexp n
  let L := Real.log (N:ℝ)
  let R := L^C
  let a := Real.exp (Real.sqrt L)
  let ratio := goldbachWeightedC R n/goldbachWeightedB R n
  let A := goldbachWeightedMeanAmplitude K δ K₁ R n ε
  let H := ratio*(P*(Real.log R)^6+A₀*(1+Real.sqrt L)/Real.log R)
  have hL0 : 0<L := by dsimp only [L];linarith
  have hlogL : 0<Real.log L := Real.log_pos (by dsimp only [L];linarith)
  have hR3 : 3≤R := by have hh := Real.add_one_le_exp (2:ℝ);dsimp only [R,L];linarith
  have hlogR : Real.log R=C*Real.log L := Real.log_rpow hL0 C
  have hlogR0 : 0<Real.log R := Real.log_pos (by linarith)
  have hB := goldbach_weighted_B_positive R (by linarith) n
  have hCpos := goldbach_weighted_C_positive R (by linarith) n
  have hratio : 0≤ratio := div_nonneg hCpos.le hB.le
  have hA : 0≤A := by
    have hc := goldbach_half_mean_constant_positive
    dsimp only [A,goldbachWeightedMeanAmplitude]
    positivity
  have hH : 0≤H := by dsimp only [H];positivity
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hExpN : Real.exp (2*L)=(N:ℝ)^2 := by
    rw [show 2*L=L+L by ring,Real.exp_add]
    dsimp only [L]
    rw [Real.exp_log hN0]
    ring
  have hz : Real.exp ((4/9:ℝ)*(2*L))=(N:ℝ)^(8/9:ℝ) := by
    rw [Real.rpow_def_of_pos hN0]
    congr 1
    dsimp only [L]
    ring
  have hharm' := hharm R hR n a hRD
  rw [show Real.log a=Real.sqrt L by exact Real.log_exp _] at hharm'
  have hf := goldbach_weighted_finite_kernel N (2*L) a R A H K₀ n hN (by dsimp only [L];linarith)
    hExpN ha haU hA hH hK₀ hM
    (fun t ht=>hmean R hR3 n a ε ha16 hInv hεB hRa hbudget t ht.1) hharm'
  have hs := goldbach_weighted_small_scalar L H K₀ (by dsimp only [L];linarith) hH hKL
  have hl := goldbach_weighted_large_scalar L a A K₀ hL ha haU hA hK₀ hKL hexp
  rw [hz] at hf
  apply (hf.trans (add_le_add hs hl)).trans_eq
  dsimp only [H,A,goldbachWeightedMeanAmplitude]
  rw [show Real.log a=Real.sqrt L by exact Real.log_exp _,hlogR]
  have hh := goldbach_weighted_coefficient_factor L (C*Real.log L) ratio P A₀ K δ K₀ K₁ ε
    hL0 (mul_pos hC hlogL)
  dsimp only [ratio] at hh
  convert hh using 1;ring

end PrimeSquares
