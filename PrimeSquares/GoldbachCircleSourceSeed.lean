import PrimeSquares.GoldbachCircleMethodComplete

set_option autoImplicit false
open Finset MeasureTheory
open scoped ContDiff
namespace PrimeSquares

noncomputable def goldbachSourceSingularIntegral (ψ : ℝ→ℝ) (N ℓ : ℕ) (R n U W : ℝ) : ℂ :=
  (ℓ:ℂ)*∫ γ : ℝ,
    (Complex.ofReal ((∫ t : ℝ,ψ t*ψ (t-(N:ℝ)^2*γ/R))/(∫ t : ℝ,ψ t*ψ t)))^2*
      goldbachSquareIntegral U γ*goldbachLinearSourceIntegral N ℓ W γ*realFourierPhase (-n*γ)

theorem goldbach_source_singular_integral_eq (ψ : ℝ→ℝ) (hc : HasCompactSupport ψ)
    (hs : ContDiff ℝ ∞ ψ) (N ℓ : ℕ) (R n U W : ℝ) :
    goldbachSingularIntegral (hc.toSchwartzMap hs) N ℓ R n U W=
      goldbachSourceSingularIntegral ψ N ℓ R n U W := by
  unfold goldbachSingularIntegral goldbachSourceSingularIntegral
  simp_rw [goldbach_eta_of_smooth_compact_seed ψ hc hs]

noncomputable def goldbachSourceFullRemainder (ψ : ℝ→ℝ) (N ℓ k a : ℕ) (R : ℝ) (n : ℕ) : ℂ :=
  ((goldbachProgressionPairs ℓ k a n).card:ℂ)-
    goldbachArithmeticFactor R k (ℓ:ℤ) (a:ℤ) n/((ℓ:ℂ)*(k.totient:ℂ))*
      goldbachSourceSingularIntegral ψ N ℓ R (n:ℝ) (N:ℝ) ((N:ℝ)^2)

theorem goldbach_circle_method_source_complete
    (HSW : RawPrimeSiegelWalfiszInput) (HBV : RawPrimeBombieriVinogradovInput)
    (D : UniformRenGhoshInputs) (ψ : ℝ→ℝ) (hc : HasCompactSupport ψ)
    (hs : ContDiff ℝ ∞ ψ) (hψ : ψ≠0) (hSupport : ∀ x : ℝ,(1/8:ℝ)≤|x| →ψ x=0)
    {A δ : ℝ} (hA : 0<A) (hδ : 0<δ) :
    ∃ B₀ C K : ℝ,0≤B₀ ∧ 0<C ∧ 0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      ∀ B L : ℝ,B₀≤B →L<(N:ℝ)^(2-δ) →∀ V : ℕ→ℝ,
      (∀ ℓ : ℕ,0<ℓ →(ℓ:ℝ)<L →V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) →
      ∀ a : ℕ×ℕ→ℕ,(∀ i∈goldbachCoefficientIndices L V,(a i).Coprime i.2) →
      ∀ d : ℕ×ℕ→ℂ,(∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1) →
      (∑ n∈range (N^2),‖∑ i∈goldbachCoefficientIndices L V,d i*
        goldbachSourceFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n‖^2)≤
        K*(N:ℝ)^4*(Real.log N)^(-A) := by
  have hSeed := goldbach_smooth_compact_seed_nonzero ψ hc hs hψ
  have hSeedSupport : ∀ x : ℝ,(1/8:ℝ)≤|x| →hc.toSchwartzMap hs x=0 := hSupport
  obtain ⟨B₀,C,K,hB₀,hC,hK,N₀,hN₀,hBound⟩ :=
    goldbach_circle_method_complete HSW HBV D (hc.toSchwartzMap hs) hSeed hSeedSupport hA hδ
  refine ⟨B₀,C,K,hB₀,hC,hK,N₀,hN₀,?_⟩
  intro N hN B L hB hL V hV a ha d hd
  have h := hBound N hN B L hB hL V hV a ha d hd
  simpa only [goldbachFullRemainder,goldbachSourceFullRemainder,goldbach_source_singular_integral_eq ψ hc hs] using h

theorem goldbach_source_singular_integral_positive_comparison
    (ψ : ℝ→ℝ) (hc : HasCompactSupport ψ) (hs : ContDiff ℝ ∞ ψ) (hψ : ψ≠0) :
    ∃ K : ℝ,0<K ∧ ∀ N ℓ : ℕ,0<N →0<ℓ →∀ R U W n : ℝ,
      0<R →2≤U →U≤N →2≤W →n<(N:ℝ)^2 →
      0≤(goldbachSourceSingularIntegral ψ N ℓ R n U W).re ∧
      (goldbachSourceSingularIntegral ψ N ℓ R n U W).im=0 ∧
      ‖goldbachSourceSingularIntegral ψ N ℓ R n U W-goldbachArchimedeanIntegral ℓ n U W‖≤
        K*(N:ℝ)/Real.sqrt R := by
  have h := goldbach_positive_singular_integral_complete (hc.toSchwartzMap hs)
    (goldbach_smooth_compact_seed_nonzero ψ hc hs hψ)
  simpa only [goldbach_source_singular_integral_eq ψ hc hs] using h

end PrimeSquares
