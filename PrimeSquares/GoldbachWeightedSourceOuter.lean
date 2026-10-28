import PrimeSquares.GoldbachWeightedSmoothing
import PrimeSquares.GoldbachWeightedMass
import PrimeSquares.GoldbachWeightedMeanValue

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachWeightedUpperSum (ψ : SchwartzMap ℝ ℝ) (N : ℕ) (R : ℝ) (n : ℕ) : ℝ :=
  ∑ ℓ∈goldbachClosedLSet N ((N:ℝ)^(8/9:ℝ)),
    goldbachUpperMainTerm ψ N R ℓ n*goldbachUpperTheta R (goldbachUpperSieveLevel N ℓ) ℓ n

noncomputable def goldbachWeightedReciprocalMass (N : ℕ) (R : ℝ) (n : ℤ) : ℝ :=
  ∑ i∈goldbachWeightedPairs N ((N:ℝ)^(8/9:ℝ)),
    goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ)

noncomputable def goldbachWeightedArchSum (N : ℕ) (R : ℝ) (n : ℤ) : ℝ :=
  ∑ i∈goldbachWeightedPairs N ((N:ℝ)^(8/9:ℝ)),
    (goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ))/
      Real.log ((N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ))*
      (goldbachArchimedeanIntegral (2*i.1*i.2) ((n:ℝ)-1) (N:ℝ) ((N:ℝ)^2)).re

noncomputable def goldbachWeightedReference (N : ℕ) (R : ℝ) (n : ℕ) : ℝ :=
  goldbachWeightedC R n*(goldbachArchimedeanIntegral 1 n (N:ℝ) ((N:ℝ)^2)).re*
    Real.sqrt (Real.log R)/Real.sqrt (Real.log N)

theorem goldbach_weighted_upper_outer (ψ : SchwartzMap ℝ ℝ) (hψ : ψ≠0)
    (K₁ : ℝ) (_hK₁ : 0≤K₁) (hV : ClassicalPrimeMertensRatios K₁) :
    ∃ K : ℝ,0<K ∧ ∀ N n : ℕ,2≤N→n<N^2→∀ R : ℝ,3≤R→R<(N:ℝ)^(2/9:ℝ)→
      ((n:ℤ):ZMod 24)=12→
      goldbachWeightedUpperSum ψ N R n≤
        24*goldbachWeightedB R n*(1+K₁/Real.log R)*Real.log R*goldbachWeightedArchSum N R n+
        6*goldbachWeightedB R n*(K*(N:ℝ)/Real.sqrt R)*goldbachWeightedReciprocalMass N R n := by
  obtain ⟨K,hK,hbound⟩ := goldbach_weighted_main_term_smoothing ψ hψ
  refine ⟨K,hK,?_⟩
  intro N n hN hnN R hR hRN hn
  have hh := hbound N n hN hnN R hR hRN hn
  let I := goldbachWeightedPairs N ((N:ℝ)^(8/9:ℝ))
  let w := fun i : ℕ×ℕ=>goldbachWeightedMultiplicative R n i.1/((2*i.1*i.2:ℕ):ℝ)
  let H := fun i : ℕ×ℕ=>(goldbachArchimedeanIntegral (2*i.1*i.2) ((n:ℝ)-1) (N:ℝ) ((N:ℝ)^2)).re
  have hsum : (∑ i∈I,w i*goldbachWeightedOuterProduct R (goldbachUpperSieveLevel N (2*i.1*i.2)) 0*H i)≤
      4*(1+K₁/Real.log R)*Real.log R*
        ∑ i∈I,w i/Real.log ((N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ))*H i := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    obtain ⟨hℓ,hRz,_,_,hbase⟩ := goldbach_weighted_pair_levels N hN R hRN i hi
    have hℓ0 : (0:ℝ)<((2*i.1*i.2:ℕ):ℝ) := by exact_mod_cast hℓ
    have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    have hb0 : 0<(N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ) := div_pos (sq_pos_of_pos hN0) hℓ0
    have hlevel : Real.log (goldbachUpperSieveLevel N (2*i.1*i.2))=
        (1/4:ℝ)*Real.log ((N:ℝ)^2/((2*i.1*i.2:ℕ):ℝ)) := Real.log_rpow hb0 _
    have hV' := hV.full R (goldbachUpperSieveLevel N (2*i.1*i.2)) hR hRz
    have hw : 0≤w i := div_nonneg (goldbach_weighted_multiplicative_nonneg R n _) (Nat.cast_nonneg _)
    have hH : 0≤H i := goldbach_weighted_arch_real_nonneg N ((n:ℝ)-1) (2*i.1*i.2)
    have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV' hw) hH
    rw [hlevel] at hp
    apply hp.trans_eq
    ring
  have hB : 0≤6*goldbachWeightedB R n := by
    have hb := goldbach_weighted_B_positive R (by linarith) n
    positivity
  have hp := mul_le_mul_of_nonneg_left hsum hB
  apply hh.trans
  apply (add_le_add hp le_rfl).trans_eq
  dsimp only [I,w,H,goldbachWeightedArchSum,goldbachWeightedReciprocalMass]
  simp only [Int.cast_natCast]
  ring

theorem goldbach_weighted_lower_outer (ψ : SchwartzMap ℝ ℝ) (N n : ℕ) (R K ε : ℝ)
    (hN : 2≤N) (hR : 3≤R) (hRz : R<(N:ℝ)^(8/9:ℝ))
    (_hK : 0≤K) (hV : ClassicalPrimeMertensRatios K) (_hε0 : 0≤ε) (hε1 : ε≤1)
    (hM : K/Real.log R≤ε) (hn : ((n:ℤ):ZMod 24)=12)
    (hH : (1-ε)*(goldbachArchimedeanIntegral 1 n (N:ℝ) ((N:ℝ)^2)).re≤
      (goldbachSingularIntegral ψ N 1 R n (N:ℝ) ((N:ℝ)^2)).re) :
    3*Real.sqrt (9/8:ℝ)*(1-ε)^2*goldbachWeightedReference N R n≤
      goldbachLowerMainTerm ψ N R n*goldbachLowerTheta R ((N:ℝ)^(8/9:ℝ)) n := by
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlogN : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hlogR : 0<Real.log R := Real.log_pos (by linarith)
  have hC := goldbach_weighted_C_positive R (by linarith) n
  have hA := goldbach_weighted_arch_real_nonneg N n 1
  have hV' := hV.half R ((N:ℝ)^(8/9:ℝ)) hR hRz
  have hV'' : (1-ε)*Real.sqrt (Real.log R)/Real.sqrt (Real.log ((N:ℝ)^(8/9:ℝ)))≤
      goldbachWeightedOuterProduct R ((N:ℝ)^(8/9:ℝ)) 3 := by
    apply le_trans _ hV'
    have hh := mul_le_mul_of_nonneg_right (show 1-ε≤1-K/Real.log R by linarith)
      (Real.sqrt_nonneg (Real.log R))
    convert div_le_div_of_nonneg_right hh
      (Real.sqrt_nonneg (Real.log ((N:ℝ)^(8/9:ℝ)))) using 1;ring
  have hfac : 0≤(1-ε)*Real.sqrt (Real.log R)/Real.sqrt (Real.log ((N:ℝ)^(8/9:ℝ))) := by positivity
  have hH0 : 0≤(goldbachSingularIntegral ψ N 1 R n (N:ℝ) ((N:ℝ)^2)).re :=
    (mul_nonneg (by linarith) hA).trans hH
  have hp := mul_le_mul hH hV'' hfac hH0
  have hp' := mul_le_mul_of_nonneg_left hp (show 0≤3*goldbachWeightedC R n by positivity)
  rw [goldbach_weighted_lower_normalization ψ N n R _ hR hRz hn]
  rw [mul_assoc (3*goldbachWeightedC R n) _ _]
  apply le_trans _ hp'
  apply le_of_eq
  dsimp only [goldbachWeightedReference]
  rw [Real.log_rpow hN0,Real.sqrt_mul (by norm_num : (0:ℝ)≤8/9)]
  have hsN := (Real.sqrt_pos.mpr hlogN).ne'
  have hsβ : Real.sqrt (8/9:ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<8/9)).ne'
  have hid : Real.sqrt (9/8:ℝ)*Real.sqrt (8/9:ℝ)=1 := by
    rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤9/8)]
    norm_num
  have hAlpha : Real.sqrt (9/8:ℝ)=1/Real.sqrt (8/9:ℝ) := (eq_div_iff hsβ).mpr hid
  rw [hAlpha]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end PrimeSquares
