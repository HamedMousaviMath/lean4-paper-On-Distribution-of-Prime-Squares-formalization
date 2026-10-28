import PrimeSquares.DyadicSquareReconstruction
import PrimeSquares.PrimeSquareDyadicAnnularEndpoint
import PrimeSquares.InterpolationGeometry

open Finset
open scoped lp
namespace PrimeSquares

theorem mangoldtPairing_dyadic_reconstruction (k : ℕ) (F G : Finset ℤ) :
    restrictedKernelPairing (weightedSquareAverageKernel (2^k) ArithmeticFunction.vonMangoldt) F G=
      ∑ j ∈ range k,(((2 : ℂ)^j)⁻¹)*restrictedKernelPairing
        (annularWeightedSquareAverageKernel (2^(k-j)) ArithmeticFunction.vonMangoldt) F G := by
  have hrec := mangoldtSquareAverage_dyadic_reconstruction
    (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) k
  have hpoint (x : ℤ) : indicatorConvolution (weightedSquareAverageKernel (2^k) ArithmeticFunction.vonMangoldt) F x=
      ∑ j ∈ range k,((2 : ℂ)^j)⁻¹*indicatorConvolution
        (annularWeightedSquareAverageKernel (2^(k-j)) ArithmeticFunction.vonMangoldt) F x := by
    have hx := congrArg (fun T : ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ) => T (finiteIndicatorLp F 2) x) hrec
    have hn := weightedSquareAverage_finiteInput
      (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (2^k) ArithmeticFunction.vonMangoldt F (fun _ => 1) x
    have hm (j : ℕ) := annularWeightedSquareAverage_finiteInput
      (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (2^(k-j)) ArithmeticFunction.vonMangoldt F (fun _ => 1) x
    simp only [finiteConvolution_indicator,finiteInputLp_one] at hn hm
    simp only [_root_.sum_apply,smul_apply,lp.coeFn_sum,
      Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul] at hx
    rw [←hn] at hx
    simpa only [←hm] using hx
  dsimp [restrictedKernelPairing]
  simp_rw [hpoint]
  rw [sum_comm]
  exact sum_congr rfl (fun _ _ => (mul_sum _ _ _).symm)

theorem square_density_ratio {M N : ℝ} (hM : 0 < M) (hN : 0 < N) (F G : Finset ℤ) :
    finiteSetDensity (M^2) F G=(N/M)^4*finiteSetDensity (N^2) F G := by
  dsimp [finiteSetDensity]
  field_simp [hM.ne',hN.ne']

theorem square_endpoint_rescale {M N δ : ℝ} (hM : 0 < M) (hN : 0 < N) (hδ : 0 ≤ δ) :
    (M/N)*M^2/N^2*((N/M)^4*δ)^(2/3 : ℝ)=(M/N)^(1/3 : ℝ)*δ^(2/3 : ℝ) := by
  rw [Real.mul_rpow (by positivity) hδ,
    ←Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ N/M)]
  norm_num only [Nat.cast_ofNat]
  rw [Real.div_rpow hN.le hM.le,Real.div_rpow hM.le hN.le]
  have hm : M^2=M^((2 : ℝ)) := (Real.rpow_two M).symm
  have hn : N^2=N^((2 : ℝ)) := (Real.rpow_two N).symm
  rw [hm,hn]
  have hprod (x : ℝ) (hx : 0 < x) : x*x^(2 : ℝ)=x^(3 : ℝ) := by
    calc
      _ = x^(1 : ℝ)*x^(2 : ℝ) := by rw [Real.rpow_one]
      _ = x^((1 : ℝ)+2) := (Real.rpow_add hx _ _).symm
      _ = _ := by norm_num
  have hMe : M*(M^(2 : ℝ)) / M^(4*(2/3 : ℝ))=M^(1/3 : ℝ) := by
    rw [hprod M hM,←Real.rpow_sub hM]
    norm_num
  have hNe : N^(4*(2/3 : ℝ))/(N*N^(2 : ℝ))=N^(-(1/3 : ℝ)) := by
    rw [hprod N hN,←Real.rpow_sub hN]
    norm_num
  calc
    _ = (M*M^(2 : ℝ)/M^(4*(2/3 : ℝ)))*(N^(4*(2/3 : ℝ))/(N*N^(2 : ℝ)))*δ^(2/3 : ℝ) := by ring_nf
    _ = _ := by rw [hMe,hNe,Real.rpow_neg hN.le];ring

end PrimeSquares
