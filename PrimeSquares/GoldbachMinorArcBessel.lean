import PrimeSquares.GoldbachFourierInversion
import PrimeSquares.ThreeTermSquareBound

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

/-- Both arithmetic indices are positive and have the exact strict real cutoffs. -/
noncomputable def goldbachCoefficientIndices (L : ℝ) (V : ℕ→ℝ) : Finset (ℕ×ℕ) :=
  ((range ⌈L⌉₊).filter (fun ℓ => 0<ℓ)).biUnion (fun ℓ =>
    ((range ⌈V ℓ⌉₊).filter (fun k => 0<k)).image (fun k => (ℓ,k)))

theorem mem_goldbachCoefficientIndices (L : ℝ) (V : ℕ→ℝ) (ℓ k : ℕ) :
    (ℓ,k)∈goldbachCoefficientIndices L V ↔
      0<ℓ ∧ (ℓ:ℝ)<L ∧ 0<k ∧ (k:ℝ)<V ℓ := by
  classical
  simp only [goldbachCoefficientIndices,mem_biUnion,mem_filter,mem_range,
    Nat.lt_ceil,mem_image,Prod.mk.injEq]
  constructor
  · rintro ⟨l,⟨hl,hpos⟩,j,⟨hj,hjpos⟩,rfl,rfl⟩
    exact ⟨hpos,hl,hjpos,hj⟩
  · rintro ⟨hlpos,hl,hkpos,hk⟩
    exact ⟨ℓ,⟨hl,hlpos⟩,k,⟨hk,hkpos⟩,rfl,rfl⟩

noncomputable def goldbachWeightedProgressionPolynomial (N : ℕ)
    (I : Finset (ℕ×ℕ)) (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (W : ℝ) :
    C(PrimeCircle,ℂ) :=
  ∑ i∈I,d i • goldbachProgressionPolynomial N i.1 i.2 (a i) W

theorem goldbach_weighted_fourier_inversion (N n : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (U W : ℝ) :
    (∫ θ : PrimeCircle,goldbachPrimeSquarePolynomial U θ*
      goldbachWeightedProgressionPolynomial N I a d W θ*
        fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle)=
      ∑ i∈I,d i*((goldbachCutoffPrimePairs N i.1 i.2 (a i) n U W).card:ℂ) := by
  simp only [goldbachWeightedProgressionPolynomial,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,smul_eq_mul,mul_sum,sum_mul]
  have hi (i : ℕ×ℕ) : Integrable (fun θ : PrimeCircle =>
      d i*(goldbachPrimeSquarePolynomial U θ*
        goldbachProgressionPolynomial N i.1 i.2 (a i) W θ*
          fourier (-(n:ℤ)) θ)) AddCircle.haarAddCircle :=
    (continuous_const.mul (((goldbachPrimeSquarePolynomial U).continuous.mul
      (goldbachProgressionPolynomial N i.1 i.2 (a i) W).continuous).mul
        (fourier _).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [show ∀ i θ,goldbachPrimeSquarePolynomial U θ*
      (d i*goldbachProgressionPolynomial N i.1 i.2 (a i) W θ)*
        fourier (-(n:ℤ)) θ=d i*(goldbachPrimeSquarePolynomial U θ*
          goldbachProgressionPolynomial N i.1 i.2 (a i) W θ*fourier (-(n:ℤ)) θ)
      from fun i θ => by ring]
  rw [integral_finsetSum I (fun i _ => hi i)]
  simp_rw [integral_const_mul,goldbach_cutoff_fourier_inversion]

theorem goldbach_weighted_full_fourier_inversion {N n : ℕ}
    (I : Finset (ℕ×ℕ)) (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ)
    (hI : ∀ i ∈ I, 1 ≤ (i.1 : ℕ)) (hn : n<N^2) :
    (∫ θ : PrimeCircle,goldbachPrimeSquarePolynomial (N:ℝ) θ*
      goldbachWeightedProgressionPolynomial N I a d ((N:ℝ)^2) θ*
        fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle)=
      ∑ i∈I,d i*((goldbachProgressionPairs i.1 i.2 (a i) n).card:ℂ) := by
  rw [goldbach_weighted_fourier_inversion]
  apply sum_congr rfl
  intro i hi
  rw [goldbach_full_cutoffs_redundant (hI i hi) hn]

theorem goldbach_finite_fourier_bessel (S : Finset ℤ) (f : PrimeCircle→ℂ)
    (hf : MemLp f 2 AddCircle.haarAddCircle) :
    (∑ n∈S,‖fourierCoeff f n‖^2)≤
      ∫ θ : PrimeCircle,‖f θ‖^2 ∂AddCircle.haarAddCircle := by
  have hc := fourierCoeff_congr_ae hf.coeFn_toLp
  have hsum : HasSum (fun n : ℤ => ‖fourierCoeff ((hf.toLp f) : PrimeCircleL2) n‖^2)
      (∫ θ : PrimeCircle,‖(hf.toLp f) θ‖^2 ∂AddCircle.haarAddCircle) :=
    hasSum_sq_fourierCoeff ((hf.toLp f) : PrimeCircleL2)
  have he := sum_le_hasSum S (fun n _ => sq_nonneg ‖fourierCoeff (hf.toLp f) n‖) hsum
  calc
    _=(∑ n∈S,‖fourierCoeff (hf.toLp f) n‖^2) := by rw [hc]
    _≤∫ θ : PrimeCircle,‖(hf.toLp f) θ‖^2 ∂AddCircle.haarAddCircle := he
    _=_ := integral_congr_ae (hf.coeFn_toLp.fun_comp (fun z : ℂ => ‖z‖^2))

/-- The minor set is arbitrary measurable; its analytic exponential-sum bound
is a separate internal obligation when this lemma is applied. -/
theorem goldbach_restricted_fourier_bessel (S : Finset ℤ) (s : Set PrimeCircle)
    (hs : MeasurableSet s) (P F : C(PrimeCircle,ℂ)) {B : ℝ}
    (hP : ∀ θ∈s,‖P θ‖≤B) :
    (∑ n∈S,‖∫ θ : PrimeCircle in s,P θ*F θ*fourier (-n) θ
      ∂AddCircle.haarAddCircle‖^2)≤
        B^2*(∫ θ : PrimeCircle,‖F θ‖^2 ∂AddCircle.haarAddCircle) := by
  classical
  let f : PrimeCircle→ℂ := s.indicator (fun θ => P θ*F θ)
  have hf : MemLp f 2 AddCircle.haarAddCircle :=
    (ContinuousMap.memLp AddCircle.haarAddCircle ℂ (P*F)).indicator hs
  have hcoeff (n : ℤ) : fourierCoeff f n=
      ∫ θ : PrimeCircle in s,P θ*F θ*fourier (-n) θ ∂AddCircle.haarAddCircle := by
    rw [←integral_indicator hs]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun θ => by
      by_cases hθ : θ∈s <;>
        simp [f,Set.indicator_of_mem,Set.indicator_of_notMem,hθ,
          smul_eq_mul,mul_comm])
  have hpoint (θ : PrimeCircle) : ‖f θ‖^2≤B^2*‖F θ‖^2 := by
    by_cases hθ : θ∈s
    · simp only [f,Set.indicator_of_mem hθ,norm_mul,mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hP θ hθ) 2)
        (sq_nonneg _)
    · simp only [f,Set.indicator_of_notMem hθ,norm_zero,zero_pow (by decide : 2≠0)]
      positivity
  have hiF : Integrable (fun θ : PrimeCircle => B^2*‖F θ‖^2) AddCircle.haarAddCircle :=
    ((ContinuousMap.memLp (p:=2) AddCircle.haarAddCircle ℂ F).integrable_norm_pow
      (by decide : 2≠0)).const_mul _
  calc
    _=(∑ n∈S,‖fourierCoeff f n‖^2) := by simp_rw [hcoeff]
    _≤∫ θ : PrimeCircle,‖f θ‖^2 ∂AddCircle.haarAddCircle :=
      goldbach_finite_fourier_bessel S f hf
    _≤∫ θ : PrimeCircle,B^2*‖F θ‖^2 ∂AddCircle.haarAddCircle :=
      integral_mono (hf.integrable_norm_pow (by decide : 2≠0)) hiF hpoint
    _=_ := integral_const_mul _ _

theorem goldbach_actual_minor_bessel (N : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (U W : ℝ) (S : Finset ℤ)
    (minor : Set PrimeCircle) (hminor : MeasurableSet minor) {B E : ℝ}
    (hP : ∀ θ∈minor,‖goldbachPrimeSquarePolynomial U θ‖≤B)
    (hE : (∫ θ : PrimeCircle,‖goldbachWeightedProgressionPolynomial N I a d W θ‖^2
      ∂AddCircle.haarAddCircle)≤E) :
    (∑ n∈S,‖∫ θ : PrimeCircle in minor,goldbachPrimeSquarePolynomial U θ*
      goldbachWeightedProgressionPolynomial N I a d W θ*fourier (-n) θ
        ∂AddCircle.haarAddCircle‖^2)≤B^2*E :=
  (goldbach_restricted_fourier_bessel S minor hminor _ _ hP).trans
    (mul_le_mul_of_nonneg_left hE (sq_nonneg B))

theorem goldbach_major_minor_partition (N n : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (U W : ℝ)
    (major : Set PrimeCircle) (hmajor : MeasurableSet major) :
    (∑ i∈I,d i*((goldbachCutoffPrimePairs N i.1 i.2 (a i) n U W).card:ℂ))=
      (∫ θ : PrimeCircle in major,goldbachPrimeSquarePolynomial U θ*
        goldbachWeightedProgressionPolynomial N I a d W θ*fourier (-(n:ℤ)) θ
          ∂AddCircle.haarAddCircle)+
      ∫ θ : PrimeCircle in majorᶜ,goldbachPrimeSquarePolynomial U θ*
        goldbachWeightedProgressionPolynomial N I a d W θ*fourier (-(n:ℤ)) θ
          ∂AddCircle.haarAddCircle := by
  rw [←goldbach_weighted_fourier_inversion]
  exact (integral_add_compl hmajor
    ((((goldbachPrimeSquarePolynomial U).continuous.mul
      (goldbachWeightedProgressionPolynomial N I a d W).continuous).mul
      (fourier _).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))).symm

/-- The three source errors are internal estimates, not independent inputs.
This is only their exact finite mean-square assembly. -/
theorem goldbach_circle_three_stage_bound (S : Finset ℤ)
    (T M₀ M₁ M₂ : ℤ→ℂ) {B₁ B₂ B₃ : ℝ}
    (h₁ : (∑ n∈S,‖T n-M₀ n‖^2)≤B₁)
    (h₂ : (∑ n∈S,‖M₀ n-M₁ n‖^2)≤B₂)
    (h₃ : (∑ n∈S,‖M₁ n-M₂ n‖^2)≤B₃) :
    (∑ n∈S,‖T n-M₂ n‖^2)≤3*(B₁+B₂+B₃) := by
  calc
    _≤∑ n∈S,3*(‖T n-M₀ n‖^2+‖M₀ n-M₁ n‖^2+‖M₁ n-M₂ n‖^2) := by
      apply sum_le_sum
      intro n _
      have he : T n-M₂ n=(T n-M₀ n)+(M₀ n-M₁ n)+(M₁ n-M₂ n) := by ring
      rw [he]
      exact norm_three_sum_square _ _ _
    _=3*((∑ n∈S,‖T n-M₀ n‖^2)+(∑ n∈S,‖M₀ n-M₁ n‖^2)+
      (∑ n∈S,‖M₁ n-M₂ n‖^2)) := by rw [←mul_sum,sum_add_distrib,sum_add_distrib]
    _≤_ := by linarith

end PrimeSquares
