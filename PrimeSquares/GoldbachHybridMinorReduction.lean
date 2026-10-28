import PrimeSquares.GoldbachSourceEnergy

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

theorem goldbach_minor_logarithmic_exponents {x : ℝ} (hx : 0<x) (A : ℝ) :
    (x^(-((A+6)/2)))^2*x^6=x^(-A) := by
  rw [←Real.rpow_natCast (x^(-((A+6)/2))) 2,←Real.rpow_mul hx.le,
    ←Real.rpow_natCast x 6,←Real.rpow_add hx]
  congr 1
  ring

/-- The progression-energy obligation is discharged. The displayed pointwise
bound is still an internal analytic obligation for the actual minor set;
this implication is not a completed source hybrid-minor theorem. -/
theorem goldbach_hybrid_minor_from_pointwise (N : ℕ) (hN : 1≤N)
    (hlog : 1≤Real.log N) (L B δ A C : ℝ) (V : ℕ→ℝ) (hB : 0≤B) (hδ : 0<δ)
    (hL : L<(N:ℝ)^(2-δ))
    (hV : ∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L →
      V ℓ≤Real.sqrt ((N:ℝ)^2/(ℓ:ℝ))*(Real.log N)^(-B))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (U W : ℝ)
    (hd : ∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1)
    (minor : Set PrimeCircle) (hminor : MeasurableSet minor)
    (hP : ∀ θ∈minor,‖goldbachPrimeSquarePolynomial U θ‖≤
      C*(N:ℝ)*(Real.log N)^(-((A+6)/2))) :
    (∑ n∈range (N^2),‖∫ θ : PrimeCircle in minor,goldbachPrimeSquarePolynomial U θ*
      goldbachWeightedProgressionPolynomial N (goldbachCoefficientIndices L V) a d W θ*
        fourier (-(n:ℤ)) θ ∂AddCircle.haarAddCircle‖^2)≤
          (C^2*(256/Real.log 2))*(N:ℝ)^4*(Real.log N)^(-A) := by
  let e : ℕ↪ℤ := ⟨fun n => (n:ℤ),Nat.cast_injective⟩
  have he := goldbach_actual_minor_bessel N (goldbachCoefficientIndices L V) a d U W
    ((range (N^2)).map e) minor hminor hP
      (goldbach_source_progression_energy_printed_range N hN hlog L B δ V hB hδ hL hV a d W hd)
  have hc : (C*(N:ℝ)*(Real.log N)^(-((A+6)/2)))^2*
      ((256/Real.log 2)*(N:ℝ)^2*(Real.log N)^6)=
      (C^2*(256/Real.log 2))*(N:ℝ)^4*(Real.log N)^(-A) := by
    calc
      _=(C^2*(256/Real.log 2))*(N:ℝ)^4*
        (((Real.log N)^(-((A+6)/2)))^2*(Real.log N)^6) := by ring
      _=_ := by rw [goldbach_minor_logarithmic_exponents (by linarith : 0<Real.log N)]
  rw [hc] at he
  simpa only [sum_map,e,Function.Embedding.coeFn_mk] using he

end PrimeSquares
