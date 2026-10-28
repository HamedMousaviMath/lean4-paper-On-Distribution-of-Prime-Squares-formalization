import PrimeSquares.SourceAbstractLocalStopping

set_option autoImplicit false
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares

theorem fourierSymbol_operator_bound {B : ℝ} (hB : 0 ≤ B)
    (T : ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ)) (m : PrimeCircle → ℂ)
    (hm : ∀ᵐ θ ∂AddCircle.haarAddCircle,‖m θ‖ ≤ B)
    (hT : ∀ f : ℓ²(ℤ,ℂ),∀ᵐ θ ∂AddCircle.haarAddCircle,
      integerFourier (T f) θ=m θ*integerFourier f θ) : ‖T‖ ≤ B := by
  apply T.opNorm_le_bound hB
  intro f
  rw [←integerFourier_norm (T f),←integerFourier_norm f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hm,hT f] with θ hmθ hTθ
  rw [hTθ,norm_mul]
  exact mul_le_mul_of_nonneg_right hmθ (norm_nonneg _)

/-- The source hypotheses, with physical scales M and an arbitrary error
symbol bounded almost everywhere. Low bounds are imposed only for F on G.
No endpoint or stopping pairing is a field. -/
structure SourceLocalStoppingHypotheses (F G : Finset ℤ) (C v s r γ β A K : ℝ) where
  B : ℕ → ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ)
  Lo : ℝ → ℕ → ℓ²(ℤ,ℂ) → ℤ → ℂ
  Hi : ℝ → ℕ → ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ)
  Er : ℝ → ℕ → ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ)
  errorSymbol : ℝ → ℕ → PrimeCircle → ℂ
  local_bound : ∀ j : ℕ,∀ x ∈ G,
    ‖B (2^j) (finiteIndicatorLp F 2) x‖ ≤
      K*(((2:ℕ)^j:ℕ):ℝ)^(-v)*(linearWindowCount C ((2:ℕ)^j) F x:ℝ)
  decomposition : ∀ J : ℝ,2 ≤ J → ∀ j : ℕ,
    J ≤ (((2:ℕ)^j:ℕ):ℝ)^((1-v)/s)/10 → ∀ x ∈ G,
      B (2^j) (finiteIndicatorLp F 2) x=Lo J (2^j) (finiteIndicatorLp F 2) x+
        Hi J (2^j) (finiteIndicatorLp F 2) x+Er J (2^j) (finiteIndicatorLp F 2) x
  low : ∀ J : ℝ,2 ≤ J → ∀ j : ℕ,
    localSplittingThreshold v s J ≤ (((2:ℕ)^j:ℕ):ℝ) → ∀ x ∈ G,
      ‖Lo J (2^j) (finiteIndicatorLp F 2) x‖ ≤
        K*J^s*(Real.log J)^γ*linearSourceLocalMass C ((2:ℕ)^j) (finiteIndicatorLp F 1) x
  high : ∀ J : ℝ,2 ≤ J → ∀ f : ℓ²(ℤ,ℂ),∃ H : ℓ²(ℤ,ℝ),
    (∀ x,0 ≤ H x) ∧
      (∀ j : ℕ,localSplittingThreshold v s J ≤ (((2:ℕ)^j:ℕ):ℝ) → ∀ x,
        ‖Hi J (2^j) f x‖ ≤ H x) ∧
      ‖H‖ ≤ K*J^(-r)*(Real.log J)^β*‖f‖
  fourier_representation : ∀ J : ℝ,2 ≤ J → ∀ (j : ℕ) (f : ℓ²(ℤ,ℂ)),
    ∀ᵐ θ ∂AddCircle.haarAddCircle,
      integerFourier (Er J (2^j) f) θ=errorSymbol J (2^j) θ*integerFourier f θ
  error_bound : ∀ J : ℝ,2 ≤ J → ∀ j : ℕ,∀ᵐ θ ∂AddCircle.haarAddCircle,
    ‖errorSymbol J (2^j) θ‖ ≤
      K*J^(-r)*(Real.log J)^β*(1+Real.log (((2:ℕ)^j:ℕ):ℝ))^(-A)

noncomputable def sourceLocalStoppingFamily {F G : Finset ℤ} {C v s r γ β A K : ℝ}
    (H : SourceLocalStoppingHypotheses F G C v s r γ β A K)
    (hK : 0 ≤ K) (hv : v < 1) (hs : 0 < s) :
    LocalizedStoppingFamily F G C v s r γ β A K where
  B j := H.B (2^j)
  Lo J j := H.Lo J (2^j)
  Hi J j := H.Hi J (2^j)
  Er J j := H.Er J (2^j)
  local_bound j x hx := by
    have hM : (0:ℝ)<(((2:ℕ)^j:ℕ):ℝ) := by positivity
    have hh := H.local_bound j x hx
    calc
      _ ≤ K*(((2:ℕ)^j:ℕ):ℝ)^(-v)*(linearWindowCount C ((2:ℕ)^j) F x:ℝ) := hh
      _ = K*(((2:ℕ)^j:ℕ):ℝ)^(1-v)*linearSourceBallMass C (finiteIndicatorLp F 1) x ((2:ℕ)^j) := by
        have he := congrArg (fun z : ℝ => K*z) (linearSourceBallMass_indicator_power hM C v F x)
        simpa only [mul_assoc,Nat.cast_pow,Nat.cast_ofNat] using he.symm
      _ = _ := by simp only [Nat.cast_pow,Nat.cast_ofNat]
  decomposition J hJ j hj x hx := H.decomposition J hJ j
    ((localSplittingThreshold_le_iff hv hs (by linarith) (by positivity)).mp hj) x hx
  low := H.low
  high := H.high
  error J hJ j := by
    have hlog : 0 ≤ Real.log J := Real.log_nonneg (by linarith : 1 ≤ J)
    have hscale : 1 ≤ (((2:ℕ)^j:ℕ):ℝ) := by exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2:ℕ)) : 1≤(2:ℕ)^j)
    have hlogM := Real.log_nonneg hscale
    exact fourierSymbol_operator_bound (by positivity) _ _ (H.error_bound J hJ j)
      (H.fourier_representation J hJ j)

theorem source_local_stopping_from_fourier_hypotheses {C C₀ v s r γ β A K D cap : ℝ}
    (hC₀ : 0 < C₀) (hK : 0 ≤ K) (hv : v < 1) (hs : 1-v ≤ s)
    (hr : 0 < r) (hβ : 0 ≤ β) (hβγ : β ≤ γ) (hA : 1/2 < A)
    (hD : 0 ≤ D) (hcap : 0 < cap) :
    ∃ Kout : ℝ,0 < Kout ∧ ∀ (I : SparseIntegerInterval) (F G : Finset ℤ)
      (H : SourceLocalStoppingHypotheses F G C v s r γ β A K) (τ : ℤ → ℕ),
      G ⊆ I.points → (F.card:ℝ) ≤ cap*I.length →
      (∀ x ∈ G,∃ j : ℕ,τ x=2^j) →
      (∀ x ∈ G,linearSourceLocalMass C₀ (τ x) (finiteIndicatorLp F 1) x ≤ D*((F.card:ℝ)/I.length)) →
      ‖∑ x ∈ G,H.B (τ x) (finiteIndicatorLp F 2) x‖/(I.length:ℝ) ≤
        Kout*(finiteSetDensity I.length F G)^(1-s/(2*(s+r)))*
          (paperLog (finiteSetDensity I.length F G))^(γ+s*(β-γ)/(s+r)) := by
  obtain ⟨Kout,hKout,hout⟩ := source_abstract_local_stopping_estimate (C:=C)
    hC₀ hK hv hs hr hβ hβγ hA hD hcap
  refine ⟨Kout,hKout,?_⟩
  intro I F G H τ hG hF hτ hadm
  exact hout I F G (sourceLocalStoppingFamily H hK hv (by linarith)) H.B τ
    hG hF hτ (fun _ => rfl) hadm

end PrimeSquares
