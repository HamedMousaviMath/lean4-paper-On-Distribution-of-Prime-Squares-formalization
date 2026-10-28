import PrimeSquares.GoldbachWeightedLargeRectangle
import PrimeSquares.GoldbachWeightedKernelSplit

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachWeightedFixedKernel (N : ℕ) (z R : ℝ) (n : ℤ) : ℝ :=
  ∑ i∈goldbachWeightedPairs N z,goldbachWeightedMultiplicative R n i.1/
    (((2*i.1*i.2:ℕ):ℝ)*(Real.log ((N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ)))^2)

theorem goldbach_weighted_finite_kernel (N : ℕ) (D a R A H K : ℝ) (n : ℤ)
    (hN : 2≤N) (hD : 18≤D) (hexp : Real.exp D=(N:ℝ)^2)
    (ha : 2≤a) (haU : a≤Real.exp (D/9)/2) (hA : 0≤A) (hH : 0≤H) (hK : 0≤K)
    (hM : ClassicalPrimeLogMertens K)
    (hmean : ∀ t∈Set.Icc a (Real.exp (D/9)/2),
      goldbachRealSummatory (goldbachWeightedMultiplicative R n) t≤A*t/Real.sqrt (Real.log t))
    (hharm : (∑ u∈Icc 1 ⌊a⌋₊,goldbachWeightedMultiplicative R n u/(u:ℝ))≤H) :
    goldbachWeightedFixedKernel N (Real.exp ((4/9:ℝ)*D)) R n≤
      H*((D/2+K)/((4/9:ℝ)*D))/(2*((4/9:ℝ)*D)^2)+
      (1/2:ℝ)*((A/(2*D^2))*Real.sqrt (1+Real.log 2/Real.log a)*Real.sqrt D*
        (8*Real.sqrt 2*goldbachWeightedW (9/8))+
        A*goldbachWeightedPrimeError D K*
          ((Real.log (Real.exp (D/9)/2)-Real.log a)/Real.sqrt (Real.log a))+
        A/(Real.sqrt (Real.log a)*((4/9:ℝ)*D)^2)*((D/2+K)/((4/9:ℝ)*D))) := by
  classical
  let z := Real.exp ((4/9:ℝ)*D)
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlogN : Real.log N=D/2 := by
    have hh := congrArg Real.log hexp
    rw [Real.log_exp,Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hlogNN : Real.log ((N:ℝ)^2)=D := by rw [←hexp,Real.log_exp]
  have hz2 : 2≤z := by
    have hh := Real.add_one_le_exp ((4/9:ℝ)*D)
    dsimp only [z]
    linarith
  have hzN : z≤N := by
    apply (Real.log_le_log_iff (Real.exp_pos _) hN0).mp
    rw [Real.log_exp,hlogN]
    linarith
  have hpRec : (∑ p∈goldbachWeightedRectanglePrimes N z,1/(p:ℝ))≤
      (D/2+K)/((4/9:ℝ)*D) := by
    have hh := goldbach_weighted_prime_reciprocal K z N hM hz2 hzN
      (goldbachWeightedRectanglePrimes N z) (by
        intro p hp
        obtain ⟨hpr,hp3,hpz⟩ := (mem_filter.mp hp).2
        have hpN : p≤N := by have := mem_range.mp (mem_filter.mp hp).1;omega
        exact ⟨hpr,hpz,by exact_mod_cast hpN⟩)
    simpa only [hlogN,z,Real.log_exp] using hh
  have hs := goldbach_weighted_kernel_small R z a N n hz2 ha
  have hharm0 : 0≤∑ u∈Icc 1 ⌊a⌋₊,goldbachWeightedMultiplicative R n u/(u:ℝ) :=
    sum_nonneg (fun u _=>div_nonneg (goldbach_weighted_multiplicative_nonneg R n u) (Nat.cast_nonneg _))
  have hpRec0 : 0≤∑ p∈goldbachWeightedRectanglePrimes N z,1/(p:ℝ) := by positivity
  have hprod := mul_le_mul hharm hpRec hpRec0 hH
  have hsmall := mul_le_mul_of_nonneg_left hprod
    (show 0≤1/(2*(Real.log z)^2) by positivity)
  have hsmall' : (1/(2*(Real.log z)^2))*
      (∑ u∈Icc 1 ⌊a⌋₊,goldbachWeightedMultiplicative R n u/(u:ℝ))*
      (∑ p∈goldbachWeightedRectanglePrimes N z,1/(p:ℝ))≤
      H*((D/2+K)/((4/9:ℝ)*D))/(2*((4/9:ℝ)*D)^2) := by
    convert hsmall using 1 <;> dsimp only [z] <;> rw [Real.log_exp] <;> ring
  have hl := goldbach_weighted_large_rectangle D a R A K n (goldbachWeightedActivePrimes N z a)
    hD ha haU hA hK hM (by
      intro p hp
      obtain ⟨hpP,hpa⟩ := mem_filter.mp hp
      obtain ⟨hpr,hp3,hpz⟩ := (mem_filter.mp hpP).2
      exact ⟨hpr,hp3,hpz,by simpa only [goldbachWeightedUBound,hexp] using hpa⟩) hmean
  have hl' := mul_le_mul_of_nonneg_left hl (by norm_num : (0:ℝ)≤1/2)
  simp only [goldbachWeightedUBound,hexp] at hl'
  have hlarge := goldbach_weighted_kernel_large R z a N n hN ha
  rw [hlogNN] at hlarge
  have he := sum_filter_add_sum_filter_not (goldbachWeightedPairs N z)
    (fun i : ℕ×ℕ=>(i.1:ℝ)≤a)
    (fun i=>goldbachWeightedMultiplicative R n i.1/
      (((2*i.1*i.2:ℕ):ℝ)*(Real.log ((N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ)))^2))
  dsimp only [goldbachWeightedFixedKernel]
  rw [←he]
  exact add_le_add (hs.trans hsmall') (hlarge.trans hl')

theorem goldbach_weighted_prime_error_coarse (L K : ℝ) (hL : 1≤L) (hK : 0≤K)
    (hexp : L≤Real.exp ((8/9:ℝ)*L)) :
    goldbachWeightedPrimeError (2*L) K≤8*(K+1)/L^3 := by
  have hL0 : 0<L := by linarith
  have hpow : 0<L^3 := pow_pos hL0 _
  have hden : 0<((4/9:ℝ)*(2*L))^3 := by positivity
  have hfirst : 2*(2*K+1)/((4/9:ℝ)*(2*L))^3≤6*(K+1)/L^3 := by
    apply (div_le_div_iff₀ hden hpow).mpr
    have hh := mul_nonneg hK hpow.le
    nlinarith only [hh,hpow.le]
  have hsecond : 1/(Real.exp ((4/9:ℝ)*(2*L))*((4/9:ℝ)*(2*L))^2)≤2/L^3 := by
    apply (div_le_div_iff₀ (by positivity) hpow).mpr
    have he : Real.exp ((4/9:ℝ)*(2*L))=Real.exp ((8/9:ℝ)*L) := by congr 1;ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_right hexp (sq_nonneg ((4/9:ℝ)*(2*L)))
    nlinarith only [hh,hpow.le]
  dsimp only [goldbachWeightedPrimeError]
  have hh := add_le_add hfirst hsecond
  apply hh.trans
  rw [←add_div]
  apply (div_le_div_iff_of_pos_right hpow).mpr
  nlinarith

end PrimeSquares
