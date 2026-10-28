import PrimeSquares.GoldbachPrimeMinorUniform
import PrimeSquares.GoldbachHybridMinorReduction

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

noncomputable def goldbachHybridMinorConstant (D : UniformRenGhoshInputs) : ℝ :=
  (goldbachMinorPrimeConstant D)^2*(256/Real.log 2)

theorem goldbachHybridMinorConstant_pos (D : UniformRenGhoshInputs) :
    0<goldbachHybridMinorConstant D := by
  have hz := goldbachMinorPrimeConstant_pos D
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold goldbachHybridMinorConstant
  positivity

/-- Complete source hybrid minor-arc estimate. It is uniform in every printed
cutoff and coefficient parameter, and uses only the existing raw Ren/Ghosh
input. The source pointwise estimate and progression energy are both proved. -/
theorem goldbach_hybrid_minor_complete (D : UniformRenGhoshInputs) {A : ℝ} (hA : 0<A) :
    ∃ C₀ : ℝ,0<C₀ ∧ ∀ C : ℝ,C₀≤C →
      ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      ∀ (L B δ : ℝ) (V : ℕ→ℝ),0≤B → 0<δ → L<(N:ℝ)^(2-δ) →
      (∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L →
        V ℓ≤Real.sqrt ((N:ℝ)^2/(ℓ:ℝ))*(Real.log N)^(-B)) →
      ∀ (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (U W : ℝ),
      (∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1) → 0≤U → U≤N →
      (∑ n∈range (N^2),‖∫ θ : PrimeCircle in GoldbachMinorArcs N ((Real.log N)^C),
        goldbachPrimeSquarePolynomial U θ*
          goldbachWeightedProgressionPolynomial N (goldbachCoefficientIndices L V) a d W θ*
            fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle‖^2)≤
              goldbachHybridMinorConstant D*(N:ℝ)^4*(Real.log N)^(-A) := by
  have ht : 0<(A+6)/2 := by linarith
  refine ⟨goldbachMinorRadiusThreshold D ((A+6)/2),goldbachMinorRadiusThreshold_pos D ht,?_⟩
  intro C hC
  obtain ⟨N₀,hN₀,hpoint⟩ := goldbach_prime_minor_uniform D ht C hC
  refine ⟨N₀,hN₀,?_⟩
  intro N hN L B δ V hB hδ hL hV a d U W hd hU hUN
  obtain ⟨hlog,hprime⟩ := hpoint N hN
  exact goldbach_hybrid_minor_from_pointwise N (by omega) hlog L B δ A
    (goldbachMinorPrimeConstant D) V hB hδ hL hV a d U W hd
      (GoldbachMinorArcs N ((Real.log N)^C))
      (goldbachMinorArcs_measurable N ((Real.log N)^C)) (hprime U hU hUN)

end PrimeSquares
