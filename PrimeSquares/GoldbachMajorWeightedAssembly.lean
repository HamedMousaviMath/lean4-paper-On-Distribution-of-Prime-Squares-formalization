import PrimeSquares.GoldbachMajorBesselAssembly

set_option autoImplicit false
open Finset MeasureTheory
open scoped ENNReal
namespace PrimeSquares

noncomputable def goldbachWeightedProgressionMajorModel (N : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (R W : ℝ) (θ : PrimeCircle) : ℂ :=
  ∑ i∈I,d i*goldbachProgressionMajorModel N i.1 i.2 (a i) R W θ

theorem goldbachWeightedProgressionMajorModel_memLp (N : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (R : ℝ) {W : ℝ} (hW : 2≤W)
    (hI : ∀ i∈I,0 < i.1) (hX : ∀ i∈I,2≤(N:ℝ)^2/i.1) (p : ℝ≥0∞) :
    MemLp (goldbachWeightedProgressionMajorModel N I a d R W) p AddCircle.haarAddCircle := by
  apply memLp_finsetSum
  intro i hi
  exact (goldbachProgressionMajorModel_memLp N i.1 i.2 (a i) (hI i hi) R hW (hX i hi) p).const_mul (d i)

theorem goldbach_weighted_major_error_le_sum (N : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (R W : ℝ)
    (hd : ∀ i∈I,‖d i‖≤1) (θ : PrimeCircle) :
    ‖goldbachWeightedProgressionPolynomial N I a d W θ-
      goldbachWeightedProgressionMajorModel N I a d R W θ‖≤
      ∑ i∈I,‖goldbachProgressionPolynomial N i.1 i.2 (a i) W θ-
        goldbachProgressionMajorModel N i.1 i.2 (a i) R W θ‖ := by
  have he : goldbachWeightedProgressionPolynomial N I a d W θ-
      goldbachWeightedProgressionMajorModel N I a d R W θ=
      ∑ i∈I,d i*(goldbachProgressionPolynomial N i.1 i.2 (a i) W θ-
        goldbachProgressionMajorModel N i.1 i.2 (a i) R W θ) := by
    simp only [goldbachWeightedProgressionPolynomial,goldbachWeightedProgressionMajorModel,
      ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,mul_sub,sum_sub_distrib]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hd i hi) (norm_nonneg _)

theorem goldbach_major_weighted_coefficient_identity (N n : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (R : ℝ) {U W : ℝ} (hU : 2≤U) (hW : 2≤W)
    (hI : ∀ i∈I,0 < i.1) (hX : ∀ i∈I,2≤(N:ℝ)^2/i.1) (s : Set PrimeCircle) :
    (∑ i∈I,d i*(∫ θ : PrimeCircle in s,
      (goldbachPrimeSquarePolynomial U θ*goldbachProgressionPolynomial N i.1 i.2 (a i) W θ-
        goldbachSquareMajorModel N R U θ*goldbachProgressionMajorModel N i.1 i.2 (a i) R W θ)*
          fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle))=
      ∫ θ : PrimeCircle in s,
        (goldbachPrimeSquarePolynomial U θ*goldbachWeightedProgressionPolynomial N I a d W θ-
          goldbachSquareMajorModel N R U θ*goldbachWeightedProgressionMajorModel N I a d R W θ)*
            fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle := by
  have hP : MemLp (goldbachPrimeSquarePolynomial U) ∞ AddCircle.haarAddCircle := ContinuousMap.memLp AddCircle.haarAddCircle ℂ _
  have hQ := goldbachSquareMajorModel_memLp N R hU ∞
  have hφ : MemLp ((fourier (-(n:ℤ))) : PrimeCircle→ℂ) ∞ AddCircle.haarAddCircle := ContinuousMap.memLp AddCircle.haarAddCircle ℂ _
  have hi (i : ℕ×ℕ) (hi : i∈I) : Integrable (fun θ : PrimeCircle =>
      (goldbachPrimeSquarePolynomial U θ*goldbachProgressionPolynomial N i.1 i.2 (a i) W θ-
        goldbachSquareMajorModel N R U θ*goldbachProgressionMajorModel N i.1 i.2 (a i) R W θ)*
          fourier (-(n:ℤ)) θ) (AddCircle.haarAddCircle.restrict s) := by
    have hF : MemLp (goldbachProgressionPolynomial N i.1 i.2 (a i) W) 2 AddCircle.haarAddCircle :=
      ContinuousMap.memLp AddCircle.haarAddCircle ℂ _
    have hG := goldbachProgressionMajorModel_memLp N i.1 i.2 (a i) (hI i hi) R hW (hX i hi) 2
    have hm : MemLp (fun θ => goldbachPrimeSquarePolynomial U θ*goldbachProgressionPolynomial N i.1 i.2 (a i) W θ-
        goldbachSquareMajorModel N R U θ*goldbachProgressionMajorModel N i.1 i.2 (a i) R W θ)
        2 AddCircle.haarAddCircle := (hP.mul hF).sub (hQ.mul hG)
    have hn : MemLp (fun θ => (goldbachPrimeSquarePolynomial U θ*goldbachProgressionPolynomial N i.1 i.2 (a i) W θ-
        goldbachSquareMajorModel N R U θ*goldbachProgressionMajorModel N i.1 i.2 (a i) R W θ)*fourier (-(n:ℤ)) θ)
        2 AddCircle.haarAddCircle := hm.mul hφ
    exact (hn.integrable (by norm_num : (1:ℝ≥0∞)≤2)).restrict
  simp_rw [←integral_const_mul]
  rw [←integral_finsetSum I (fun i h => (hi i h).const_mul (d i))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro θ
  simp only [goldbachWeightedProgressionPolynomial,goldbachWeightedProgressionMajorModel,
    ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  rw [mul_sum,mul_sum,←sum_sub_distrib,sum_mul]
  apply sum_congr rfl
  intro i _
  ring

theorem goldbach_major_square_log_identity {l : ℝ} (hl : 0<l) (A C : ℝ) :
    (l^C)^3*(l^(-((A+3*C)/2)))^2=l^(-A) := by
  rw [←Real.rpow_natCast (l^C) 3,←Real.rpow_mul hl.le,
    ←Real.rpow_natCast (l^(-((A+3*C)/2))) 2,←Real.rpow_mul hl.le,←Real.rpow_add hl]
  congr 1
  ring

theorem goldbach_major_mean_square_budget (N : ℕ) (hN : 1≤N)
    (hlog : 0<Real.log N) (A C KP KE : ℝ) :
    2*(((N:ℝ)/Real.log 2)^2*(KE*(N:ℝ)^2*(Real.log N)^(-((A+3*C)/2)))^2*
        (8*((Real.log N)^C)^3/(N:ℝ)^2)+
      (KP*(N:ℝ)*(Real.log N)^(-((A+6)/2)))^2*((256/Real.log 2)*(N:ℝ)^2*(Real.log N)^6))=
      (2*(8*KE^2/(Real.log 2)^2+KP^2*(256/Real.log 2)))*(N:ℝ)^4*(Real.log N)^(-A) := by
  have hn0 : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hl2 : Real.log 2≠0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  calc
    _=2*((8*KE^2/(Real.log 2)^2)*(N:ℝ)^4*
        (((Real.log N)^C)^3*((Real.log N)^(-((A+3*C)/2)))^2)+
      (KP^2*(256/Real.log 2))*(N:ℝ)^4*(((Real.log N)^(-((A+6)/2)))^2*(Real.log N)^6)) := by
      field_simp [hn0,hl2]
    _=2*((8*KE^2/(Real.log 2)^2)*(N:ℝ)^4*(Real.log N)^(-A)+
      (KP^2*(256/Real.log 2))*(N:ℝ)^4*(Real.log N)^(-A)) := by
      rw [goldbach_major_square_log_identity hlog A C,goldbach_minor_logarithmic_exponents hlog A]
    _=_ := by ring

end PrimeSquares
