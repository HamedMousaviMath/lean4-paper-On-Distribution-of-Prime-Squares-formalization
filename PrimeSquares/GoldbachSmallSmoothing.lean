import PrimeSquares.GoldbachHardSmoothing

set_option autoImplicit false
open Finset
open scoped SchwartzMap
namespace PrimeSquares

theorem goldbach_divisor_harmonic_initial_sum :
    ∃ K : ℝ,0<K ∧ ∀ R : ℝ,2≤R →
      (∑ q∈Icc 1 ⌊R⌋₊,(q.divisors.card:ℝ)^11/(q:ℝ))≤
        K*R^(1/4:ℝ)*(1+Real.log R) := by
  obtain ⟨K,hK,hb⟩ := divisors_card_rpow_le_rpow (by norm_num : (0:ℝ)<11) (by norm_num : (0:ℝ)<1/4)
  refine ⟨K,hK,?_⟩
  intro R hR
  have hRp : 0<R := by linarith
  have hJ : 1≤⌊R⌋₊ := (Nat.le_floor_iff hRp.le).mpr (by norm_num only [Nat.cast_one];linarith)
  have hJp : (0:ℝ)<⌊R⌋₊ := by exact_mod_cast (show 0<⌊R⌋₊ by omega)
  have hH : (∑ q∈Icc 1 ⌊R⌋₊,(q:ℝ)⁻¹)≤1+Real.log R := by
    have he : (∑ q∈Icc 1 ⌊R⌋₊,(q:ℝ)⁻¹)=(harmonic ⌊R⌋₊:ℝ) := by
      rw [harmonic_eq_sum_Icc,Rat.cast_sum]
      simp only [Rat.cast_inv,Rat.cast_natCast]
    rw [he]
    exact (harmonic_le_one_add_log _).trans (by linarith [Real.log_le_log hJp (Nat.floor_le hRp.le)])
  calc
    _≤∑ q∈Icc 1 ⌊R⌋₊,K*R^(1/4:ℝ)*(q:ℝ)⁻¹ := by
      apply sum_le_sum
      intro q hq
      have hqpos : 0<q := by have := (mem_Icc.mp hq).1;omega
      have hqJ : (q:ℝ)≤(⌊R⌋₊:ℕ) := by exact_mod_cast (mem_Icc.mp hq).2
      have hqR : (q:ℝ)≤R := hqJ.trans (Nat.floor_le hRp.le)
      have hτ : (q.divisors.card:ℝ)^11≤K*(q:ℝ)^(1/4:ℝ) := by
        simpa only [show (11:ℝ)=((11:ℕ):ℝ) by norm_num,Real.rpow_natCast] using hb q hqpos
      have hh := hτ.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg q) hqR (by norm_num : (0:ℝ)≤1/4)) hK.le)
      simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg q)
    _=K*R^(1/4:ℝ)*(∑ q∈Icc 1 ⌊R⌋₊,(q:ℝ)⁻¹) := (mul_sum _ _ _).symm
    _≤_ := mul_le_mul_of_nonneg_left hH (by positivity)

theorem goldbach_small_smoothing_uniform (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0) :
    ∃ K : ℝ,0<K ∧ ∀ N : ℕ,1≤N →1≤Real.log N →∀ L B : ℝ,∀ V : ℕ→ℝ,
      0≤B →L≤(N:ℝ)^2 →
      (∀ ℓ : ℕ,0<ℓ →(ℓ:ℝ)<L →V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) →
      ∀ b : ℕ×ℕ→ℤ,(∀ i∈goldbachCoefficientIndices L V,IsCoprime (i.2:ℤ) (b i)) →
      ∀ d : ℕ×ℕ→ℂ,(∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1) →
      ∀ R U W : ℝ,2≤R →2≤U →U≤N →2≤W →∀ n : ℤ,
      ‖∑ i∈goldbachCoefficientIndices L V,
        (d i*(goldbachHardSingularIntegral N i.1 R (n:ℝ) U W-goldbachSingularIntegral ψ N i.1 R (n:ℝ) U W))/
          ((i.1:ℂ)*(i.2.totient:ℂ))*(∑ q∈Icc 1 ⌊R⌋₊,generalCoefficient q i.2 (i.1:ℤ) (b i) n)‖≤
        K*(N:ℝ)*(Real.log N)^2*(1+Real.log R)/R^(1/4:ℝ) := by
  obtain ⟨K₁,hK₁,h₁⟩ := goldbach_hard_singular_smoothing_uniform ψ hψ
  obtain ⟨K₂,hK₂,h₂⟩ := goldbach_divisor_harmonic_initial_sum
  refine ⟨(9*Real.exp 2)*K₁*K₂,by positivity,?_⟩
  intro N hN hlog L B V hB hL hV b hb d hd R U W hR hU hUN hW n
  have hRp : 0<R := by linarith
  have hM : 0≤K₁*(N:ℝ)/Real.sqrt R := by positivity
  have hH (i : ℕ×ℕ) (hi : i∈goldbachCoefficientIndices L V) :
      ‖goldbachHardSingularIntegral N i.1 R (n:ℝ) U W-goldbachSingularIntegral ψ N i.1 R (n:ℝ) U W‖≤K₁*(N:ℝ)/Real.sqrt R :=
    h₁ N i.1 (by omega) ((mem_goldbachCoefficientIndices _ _ _ _).mp hi).1 R U W n hRp hU hUN hW
  have ht := goldbach_source_finite_arithmetic_tail N hN hlog L B V hB hL hV b hb d
    (fun i=>goldbachHardSingularIntegral N i.1 R (n:ℝ) U W-goldbachSingularIntegral ψ N i.1 R (n:ℝ) U W)
    hd hM hH (Icc 1 ⌊R⌋₊) (fun q hq=>by have := (mem_Icc.mp hq).1;omega) n
  apply ht.trans
  calc
    _≤(9*Real.exp 2)*(K₁*(N:ℝ)/Real.sqrt R)*(Real.log N)^2*(K₂*R^(1/4:ℝ)*(1+Real.log R)) :=
      mul_le_mul_of_nonneg_left (h₂ R hR) (by positivity)
    _=(9*Real.exp 2)*K₁*K₂*(N:ℝ)*(Real.log N)^2*(1+Real.log R)/R^(1/4:ℝ) := by
      have hroot : Real.sqrt R=R^(1/4:ℝ)*R^(1/4:ℝ) := by
        rw [Real.sqrt_eq_rpow,←Real.rpow_add hRp]
        norm_num
      rw [hroot]
      have hp : R^(1/4:ℝ)≠0 := (Real.rpow_pos_of_pos hRp _).ne'
      field_simp

end PrimeSquares
