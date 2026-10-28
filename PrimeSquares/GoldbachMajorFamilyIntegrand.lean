import PrimeSquares.GoldbachMajorEnvelope

set_option autoImplicit false
open Finset MeasureTheory
open scoped SchwartzMap
namespace PrimeSquares

noncomputable def goldbachMajorFamilyIntegrand (N : ℕ) (I : Finset (ℕ×ℕ))
    (b : ℕ×ℕ→ℤ) (d : ℕ×ℕ→ℂ) (U W : ℝ) (r : ℚ) (γ : ℝ) : ℂ :=
  principalSquareSum r.den (-(r.num:ZMod r.den))*
    ∑ i∈I,(d i*upsilon r.den i.2 (b i) (-(r.num:ZMod r.den)*(i.1:ZMod r.den)))/(i.2.totient:ℂ)*
      (goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N i.1 W γ)

noncomputable def goldbachSmoothMajorFamilyIntegrand (ψ : 𝓢(ℝ,ℝ)) (N : ℕ) (R : ℝ)
    (I : Finset (ℕ×ℕ)) (b : ℕ×ℕ→ℤ) (d : ℕ×ℕ→ℂ) (U W : ℝ) (r : ℚ) (γ : ℝ) : ℂ :=
  (goldbachEta ψ ((N:ℝ)^2*γ/R))^2*goldbachMajorFamilyIntegrand N I b d U W r γ

noncomputable def goldbachMajorArithmeticPrefactor (N q : ℕ) : ℝ :=
  (9*Real.exp 2)*(q.divisors.card:ℝ)^6/((q:ℝ)*Real.sqrt q)*(Real.log N)^2

theorem goldbach_major_arithmetic_prefactor_nonnegative (N q : ℕ) :
    0≤goldbachMajorArithmeticPrefactor N q := by unfold goldbachMajorArithmeticPrefactor;positivity

theorem goldbach_major_family_integrand_measurable (N : ℕ) (I : Finset (ℕ×ℕ))
    (hI : ∀ i∈I,0< i.1) (b : ℕ×ℕ→ℤ) (d : ℕ×ℕ→ℂ) (U W : ℝ) (r : ℚ) :
    StronglyMeasurable (goldbachMajorFamilyIntegrand N I b d U W r) := by
  apply stronglyMeasurable_const.mul
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  exact stronglyMeasurable_const.mul ((goldbachSquareIntegral_stronglyMeasurable U).mul
    (goldbachLinearSourceIntegral_stronglyMeasurable N i.1 (hI i hi) W))

theorem goldbach_major_family_integrand_bound (N : ℕ) (hN : 1≤N) (hlog : 1≤Real.log N)
    (L B : ℝ) (V : ℕ→ℝ) (hB : 0≤B) (hL : L≤(N:ℝ)^2)
    (hV : ∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L →V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B))
    (b : ℕ×ℕ→ℤ) (hb : ∀ i∈goldbachCoefficientIndices L V,IsCoprime (i.2:ℤ) (b i))
    (d : ℕ×ℕ→ℂ) (hd : ∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1)
    {U W : ℝ} (hU : 2≤U) (hUN : U≤N) (hW : 2≤W) (r : ℚ) (γ : ℝ) :
    ‖goldbachMajorFamilyIntegrand N (goldbachCoefficientIndices L V) b d U W r γ‖≤
      goldbachMajorArithmeticPrefactor N r.den*goldbachMajorEnvelope N γ := by
  have hα : IsUnit (-(r.num:ZMod r.den)) :=
    ((ZMod.coe_int_isUnit_iff_isCoprime r.num r.den).mpr r.isCoprime_num_den.symm).neg
  have hG := goldbach_principal_square_divisor_bound r.den (-(r.num:ZMod r.den)) hα
  have hE := goldbach_major_envelope_nonnegative N γ
  have hterm (i : ℕ×ℕ) (hi : i∈goldbachCoefficientIndices L V) :
      ‖(d i*upsilon r.den i.2 (b i) (-(r.num:ZMod r.den)*(i.1:ZMod r.den)))/(i.2.totient:ℂ)*
        (goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N i.1 W γ)‖≤
      ((r.den.divisors.card:ℝ)/(r.den:ℝ))*goldbachMajorEnvelope N γ*
        ((r.den.gcd (i.1*i.2):ℝ)/((i.1:ℝ)*(i.2.totient:ℝ))) := by
    obtain ⟨hℓ,_,hk,_⟩ := (mem_goldbachCoefficientIndices L V i.1 i.2).mp hi
    let : NeZero i.2 := ⟨hk.ne'⟩
    have hlR : (0:ℝ)< i.1 := by exact_mod_cast hℓ
    have hu := goldbach_upsilon_integer_gcd_decay r.den i.2 i.1 (b i) (hb i hi) _ hα
    rw [Nat.mul_comm i.2 i.1] at hu
    have hdu : ‖d i‖*‖upsilon r.den i.2 (b i) (-(r.num:ZMod r.den)*(i.1:ZMod r.den))‖≤
        (r.den.divisors.card:ℝ)*(r.den.gcd (i.1*i.2):ℝ)/(r.den:ℝ) := by
      simpa only [one_mul] using mul_le_mul (hd i hi) hu (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
    have hIJ : ‖goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N i.1 W γ‖≤
        goldbachMajorEnvelope N γ/(i.1:ℝ) :=
      (le_div_iff₀ hlR).mpr (by simpa only [mul_comm] using goldbach_euclidean_product_envelope N i.1 hℓ hU hUN hW γ)
    rw [norm_mul,norm_div,norm_mul,Complex.norm_natCast]
    apply (mul_le_mul (div_le_div_of_nonneg_right hdu (Nat.cast_nonneg _)) hIJ (norm_nonneg _)
      (by positivity)).trans_eq
    ring
  have hH := goldbach_source_arithmetic_harmonic N r.den hN r.den_pos hlog L B V hB hL hV
  unfold goldbachMajorFamilyIntegrand
  rw [norm_mul]
  calc
    _≤((r.den.divisors.card:ℝ)^3/Real.sqrt r.den)*
        (∑ i∈goldbachCoefficientIndices L V,‖(d i*upsilon r.den i.2 (b i)
          (-(r.num:ZMod r.den)*(i.1:ZMod r.den)))/(i.2.totient:ℂ)*
          (goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N i.1 W γ)‖) :=
      mul_le_mul hG (norm_sum_le _ _) (norm_nonneg _) (by positivity)
    _≤((r.den.divisors.card:ℝ)^3/Real.sqrt r.den)*
        (∑ i∈goldbachCoefficientIndices L V,((r.den.divisors.card:ℝ)/(r.den:ℝ))*goldbachMajorEnvelope N γ*
          ((r.den.gcd (i.1*i.2):ℝ)/((i.1:ℝ)*(i.2.totient:ℝ)))) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)
    _=((r.den.divisors.card:ℝ)^3/Real.sqrt r.den)*
        (((r.den.divisors.card:ℝ)/(r.den:ℝ))*goldbachMajorEnvelope N γ*
          (∑ i∈goldbachCoefficientIndices L V,(r.den.gcd (i.1*i.2):ℝ)/((i.1:ℝ)*(i.2.totient:ℝ)))) := by simp only [mul_sum]
    _≤((r.den.divisors.card:ℝ)^3/Real.sqrt r.den)*
        (((r.den.divisors.card:ℝ)/(r.den:ℝ))*goldbachMajorEnvelope N γ*
          ((9*Real.exp 2)*(r.den.divisors.card:ℝ)^2*(Real.log N)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH (by positivity)) (by positivity)
    _=_ := by unfold goldbachMajorArithmeticPrefactor;ring

theorem goldbach_smooth_major_family_measurable (ψ : 𝓢(ℝ,ℝ)) (N : ℕ) (R : ℝ)
    (I : Finset (ℕ×ℕ)) (hI : ∀ i∈I,0< i.1) (b : ℕ×ℕ→ℤ) (d : ℕ×ℕ→ℂ)
    (U W : ℝ) (r : ℚ) : StronglyMeasurable (goldbachSmoothMajorFamilyIntegrand ψ N R I b d U W r) :=
  ((((goldbachEta ψ).continuous.comp (by fun_prop)).pow 2).stronglyMeasurable).mul
    (goldbach_major_family_integrand_measurable N I hI b d U W r)

theorem goldbach_smooth_major_family_norm (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (N : ℕ) (R : ℝ) (I : Finset (ℕ×ℕ)) (b : ℕ×ℕ→ℤ) (d : ℕ×ℕ→ℂ)
    (U W : ℝ) (r : ℚ) (γ : ℝ) :
    ‖goldbachSmoothMajorFamilyIntegrand ψ N R I b d U W r γ‖≤
      ‖goldbachMajorFamilyIntegrand N I b d U W r γ‖ := by
  rw [goldbachSmoothMajorFamilyIntegrand,norm_mul,norm_pow]
  have hη := goldbach_eta_norm_le_one ψ hψ ((N:ℝ)^2*γ/R)
  exact mul_le_of_le_one_left (norm_nonneg _) (by nlinarith [norm_nonneg (goldbachEta ψ ((N:ℝ)^2*γ/R))])

theorem goldbach_smooth_major_family_support (ψ : 𝓢(ℝ,ℝ))
    (hs : ∀ t : ℝ,(1/8:ℝ)≤|t| →ψ t=0) (N : ℕ) (hN : 0<N) {R : ℝ} (hR : 0<R)
    (I : Finset (ℕ×ℕ)) (b : ℕ×ℕ→ℤ) (d : ℕ×ℕ→ℂ) (U W : ℝ) (r : ℚ)
    {γ : ℝ} (hγ : R/(4*(N:ℝ)^2)≤|γ|) :
    goldbachSmoothMajorFamilyIntegrand ψ N R I b d U W r γ=0 := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hh : (1/4:ℝ)≤|(N:ℝ)^2*γ/R| := by
    rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg (N:ℝ)),abs_of_pos hR]
    apply (le_div_iff₀ hR).mpr
    have hb := (div_le_iff₀ (by positivity : (0:ℝ)<4*(N:ℝ)^2)).mp hγ
    nlinarith
  rw [goldbachSmoothMajorFamilyIntegrand,goldbach_eta_support ψ hs hh,zero_pow (by decide : 2≠0),zero_mul]

end PrimeSquares
