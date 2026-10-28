import PrimeSquares.GoldbachCenterArithmetic

set_option autoImplicit false
open Finset MeasureTheory
open scoped SchwartzMap
namespace PrimeSquares

noncomputable def goldbachRadialProductKernel (N ℓ : ℕ) (w : ℝ→ℂ) (U W : ℝ) (n : ℤ) (γ : ℝ) : ℂ :=
  w γ*(goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ)*realFourierPhase (-(n:ℝ)*γ)

theorem goldbach_radial_major_family_identity (N : ℕ) (I : Finset (ℕ×ℕ))
    (b : ℕ×ℕ→ℤ) (d : ℕ×ℕ→ℂ) (w : ℝ→ℂ) (U W Y : ℝ) (β : ℕ→ℂ) (n : ℤ)
    (hK : ∀ i∈I,Integrable (goldbachRadialProductKernel N i.1 w U W n)) :
    (∑ r∈sourceRationalCenters Y,β r.den*realFourierPhase (-(n:ℝ)*(r:ℝ))*
      (∫ γ : ℝ,w γ*goldbachMajorFamilyIntegrand N I b d U W r γ*realFourierPhase (-(n:ℝ)*γ)))=
      ∑ i∈I,(d i/(i.2.totient:ℂ))*(∫ γ : ℝ,goldbachRadialProductKernel N i.1 w U W n γ)*
        (∑ q∈Icc 1 ⌊Y⌋₊,β q*generalCoefficient q i.2 (i.1:ℤ) (b i) n) := by
  classical
  let c := fun (r : ℚ) (i : ℕ×ℕ)=>principalSquareSum r.den (-(r.num:ZMod r.den))*
    (d i*upsilon r.den i.2 (b i) (-(r.num:ZMod r.den)*(i.1:ZMod r.den)))/(i.2.totient:ℂ)
  have hF (r : ℚ) : (∫ γ : ℝ,w γ*goldbachMajorFamilyIntegrand N I b d U W r γ*realFourierPhase (-(n:ℝ)*γ))=
      ∑ i∈I,c r i*(∫ γ : ℝ,goldbachRadialProductKernel N i.1 w U W n γ) := by
    have he : (fun γ : ℝ=>w γ*goldbachMajorFamilyIntegrand N I b d U W r γ*realFourierPhase (-(n:ℝ)*γ))=
        (fun γ=>∑ i∈I,c r i*goldbachRadialProductKernel N i.1 w U W n γ) := by
      funext γ
      simp only [goldbachMajorFamilyIntegrand,mul_sum,sum_mul]
      apply sum_congr rfl
      intro i _
      dsimp only [c,goldbachRadialProductKernel]
      ring
    rw [he,integral_finsetSum I (fun i hi=>(hK i hi).const_mul (c r i))]
    simp only [integral_const_mul]
  calc
    _=∑ r∈sourceRationalCenters Y,∑ i∈I,β r.den*realFourierPhase (-(n:ℝ)*(r:ℝ))*
        (c r i*(∫ γ : ℝ,goldbachRadialProductKernel N i.1 w U W n γ)) := by simp only [hF,mul_sum]
    _=∑ i∈I,∑ r∈sourceRationalCenters Y,β r.den*realFourierPhase (-(n:ℝ)*(r:ℝ))*
        (c r i*(∫ γ : ℝ,goldbachRadialProductKernel N i.1 w U W n γ)) := sum_comm
    _=∑ i∈I,(d i/(i.2.totient:ℂ))*(∫ γ : ℝ,goldbachRadialProductKernel N i.1 w U W n γ)*
        (∑ r∈sourceRationalCenters Y,β r.den*goldbachCenterArithmetic r.den i.2 (i.1:ℤ) (b i) n r.num) := by
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      rw [goldbach_center_arithmetic_rational]
      simp only [Int.cast_natCast]
      dsimp only [c]
      ring
    _=_ := by simp only [goldbach_centers_weighted_arithmetic]

theorem goldbach_smoothed_radial_kernel_integrable (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (N ℓ : ℕ) (hN : 0<N) (hℓ : 0<ℓ) {U W : ℝ} (hU : 2≤U) (hUN : U≤N) (hW : 2≤W)
    (R : ℝ) (n : ℤ) :
    Integrable (goldbachRadialProductKernel N ℓ (fun γ=>(goldbachEta ψ ((N:ℝ)^2*γ/R))^2) U W n) := by
  change Integrable (fun γ : ℝ=>(goldbachEta ψ ((N:ℝ)^2*γ/R))^2*
    (goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ)*realFourierPhase (-(n:ℝ)*γ))
  by_cases hX : 2≤(N:ℝ)^2/ℓ
  · simpa only [mul_assoc] using
      goldbach_singular_integrand_integrable ψ hψ N ℓ hN hℓ hU hUN hW hX R (n:ℝ)
  · simp only [goldbach_linear_source_integral_empty N ℓ hℓ (le_of_not_ge hX),mul_zero,zero_mul]
    exact MeasureTheory.integrable_zero ℝ ℂ volume

theorem goldbach_smoothed_radial_kernel_integral (ψ : 𝓢(ℝ,ℝ)) (N ℓ : ℕ) (hℓ : 0<ℓ)
    (R U W : ℝ) (n : ℤ) :
    (∫ γ : ℝ,goldbachRadialProductKernel N ℓ (fun γ=>(goldbachEta ψ ((N:ℝ)^2*γ/R))^2) U W n γ)=
      goldbachSingularIntegral ψ N ℓ R (n:ℝ) U W/(ℓ:ℂ) := by
  have he : goldbachSingularIntegral ψ N ℓ R (n:ℝ) U W=
      (ℓ:ℂ)*(∫ γ : ℝ,goldbachRadialProductKernel N ℓ (fun γ=>(goldbachEta ψ ((N:ℝ)^2*γ/R))^2) U W n γ) := by
    unfold goldbachSingularIntegral
    congr 1
    apply integral_congr_ae
    filter_upwards with γ
    dsimp only [goldbachRadialProductKernel]
    ring
  rw [he]
  have hcz : (ℓ:ℂ)≠0 := by exact_mod_cast hℓ.ne'
  field_simp

theorem goldbach_smoothed_major_family_identity (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (N : ℕ) (hN : 0<N) (I : Finset (ℕ×ℕ)) (hI : ∀ i∈I,0 < i.1)
    (b : ℕ×ℕ→ℤ) (d : ℕ×ℕ→ℂ) {U W : ℝ} (hU : 2≤U) (hUN : U≤N) (hW : 2≤W)
    (R Y : ℝ) (β : ℕ→ℂ) (n : ℤ) :
    (∑ r∈sourceRationalCenters Y,β r.den*realFourierPhase (-(n:ℝ)*(r:ℝ))*
      (∫ γ : ℝ,goldbachSmoothMajorFamilyIntegrand ψ N R I b d U W r γ*realFourierPhase (-(n:ℝ)*γ)))=
      ∑ i∈I,(d i*goldbachSingularIntegral ψ N i.1 R (n:ℝ) U W)/((i.1:ℂ)*(i.2.totient:ℂ))*
        (∑ q∈Icc 1 ⌊Y⌋₊,β q*generalCoefficient q i.2 (i.1:ℤ) (b i) n) := by
  have hK : ∀ i∈I,Integrable (goldbachRadialProductKernel N i.1
      (fun γ=>(goldbachEta ψ ((N:ℝ)^2*γ/R))^2) U W n) := by
    intro i hi
    exact goldbach_smoothed_radial_kernel_integrable ψ hψ N i.1 hN (hI i hi) hU hUN hW R n
  have h := goldbach_radial_major_family_identity N I b d
    (fun γ=>(goldbachEta ψ ((N:ℝ)^2*γ/R))^2) U W Y β n hK
  change (∑ r∈sourceRationalCenters Y,β r.den*realFourierPhase (-(n:ℝ)*(r:ℝ))*
      (∫ γ : ℝ,(goldbachEta ψ ((N:ℝ)^2*γ/R))^2*goldbachMajorFamilyIntegrand N I b d U W r γ*
        realFourierPhase (-(n:ℝ)*γ)))=_
  rw [h]
  apply sum_congr rfl
  intro i hi
  rw [goldbach_smoothed_radial_kernel_integral ψ N i.1 (hI i hi)]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end PrimeSquares
