import PrimeSquares.GoldbachRankinSource

set_option autoImplicit false
open Finset Filter
open scoped SchwartzMap
namespace PrimeSquares

noncomputable def goldbachArithmeticTailConstant : ℝ :=
  9*Real.exp 2*goldbachEuclideanL1Constant

theorem goldbachArithmeticTailConstant_pos : 0<goldbachArithmeticTailConstant := by
  have := goldbachEuclideanL1Constant_pos
  unfold goldbachArithmeticTailConstant
  positivity

theorem goldbach_source_rankin_arithmetic_tail (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    {C t : ℝ} (hC : 1≤C) (ht : 0<t) :
    ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →2≤Real.log N ∧ 2≤(Real.log N)^C ∧
      ∀ L B : ℝ,∀ V : ℕ→ℝ,0≤B →L≤(N:ℝ)^2 →
      (∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L →V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) →
      ∀ b : ℕ×ℕ→ℤ,(∀ i∈goldbachCoefficientIndices L V,IsCoprime (i.2:ℤ) (b i)) →
      ∀ d : ℕ×ℕ→ℂ,(∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1) →
      ∀ U W : ℝ,2≤U →U≤N →2≤W →∀ D : ℕ,D≠0 →
      (∀ p∈D.primeFactors,(p:ℝ)≤(Real.log N)^C) →∀ S : Finset ℕ,
      (∀ q∈S,q∈D.divisors ∧ (N:ℝ)/(100*Real.sqrt ((Real.log N)^C))<(q:ℝ)) →∀ n : ℤ,
      ‖∑ i∈goldbachCoefficientIndices L V,
        (d i*goldbachSingularIntegral ψ N i.1 ((Real.log N)^C) (n:ℝ) U W)/
          ((i.1:ℂ)*(i.2.totient:ℂ))*(∑ q∈S,generalCoefficient q i.2 (i.1:ℤ) (b i) n)‖≤
        goldbachArithmeticTailConstant*(N:ℝ)*(Real.log N)^(-t) := by
  obtain ⟨N₁,hN₁,hRankin⟩ := goldbach_source_rankin_tail hC (by linarith : 0<t+2)
  have hlog : Tendsto (fun N : ℕ=>Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp (hlog.eventually (eventually_ge_atTop (2:ℝ)))
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro N hN
  have hl2 := hN₂ N ((le_max_right _ _).trans hN)
  have hl0 : 0<Real.log N := by linarith
  have hR : 2≤(Real.log N)^C := hl2.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤Real.log N) hC)
  refine ⟨hl2,hR,?_⟩
  intro L B V hB hL hV b hb d hd U W hU hUN hW D hD hDR S hS n
  have hNpos : 0<N := by omega
  have hNR : (0:ℝ)<N := by exact_mod_cast hNpos
  have hY : (0:ℝ)<(N:ℝ)/(100*Real.sqrt ((Real.log N)^C)) := by positivity
  have hSpos : ∀ q∈S,0<q := by
    intro q hq
    have hh := hY.trans (hS q hq).2
    exact_mod_cast hh
  have hRank := hRankin N ((le_max_left _ _).trans hN) D hD hDR S hS
  have hH : ∀ i∈goldbachCoefficientIndices L V,
      ‖goldbachSingularIntegral ψ N i.1 ((Real.log N)^C) (n:ℝ) U W‖≤
        goldbachEuclideanL1Constant*(N:ℝ) := by
    intro i hi
    have hℓ := ((mem_goldbachCoefficientIndices L V i.1 i.2).mp hi).1
    exact goldbach_singular_integral_norm ψ hψ N i.1 hNpos hℓ hU hUN hW _ _
  have hcoeff := goldbach_source_finite_arithmetic_tail N (by omega) (by linarith) L B V hB hL hV b hb d
    (fun i=>goldbachSingularIntegral ψ N i.1 ((Real.log N)^C) (n:ℝ) U W) hd
    (by have := goldbachEuclideanL1Constant_pos;positivity) hH S hSpos n
  have hp : (Real.log N)^2*(Real.log N)^(-(t+2))=(Real.log N)^(-t) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hl0]
    congr 1
    ring
  calc
    _≤(9*Real.exp 2)*(goldbachEuclideanL1Constant*(N:ℝ))*(Real.log N)^2*
        (∑ q∈S,(q.divisors.card:ℝ)^11/(q:ℝ)) := hcoeff
    _≤(9*Real.exp 2)*(goldbachEuclideanL1Constant*(N:ℝ))*(Real.log N)^2*(Real.log N)^(-(t+2)) :=
      mul_le_mul_of_nonneg_left hRank (by have := goldbachEuclideanL1Constant_pos;positivity)
    _=goldbachArithmeticTailConstant*(N:ℝ)*((Real.log N)^2*(Real.log N)^(-(t+2))) := by
      unfold goldbachArithmeticTailConstant
      ring
    _=_ := by rw [hp]

end PrimeSquares
