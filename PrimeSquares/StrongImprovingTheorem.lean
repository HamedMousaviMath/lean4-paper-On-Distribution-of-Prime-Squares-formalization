import PrimeSquares.StrongImproving
import PrimeSquares.RestrictedImproving

/-!
# Corollary 4.15: both strong improving estimates

The source high-low hypotheses and genuine uniform l2 bounds imply the
strong estimate for every p0 < p <= 2. The constant is chosen before N,
the kernels and the input. Both realizations are actual continuous linear
maps agreeing with convolution on finite inputs. No interpolation or
desired strong conclusion is an external hypothesis.
-/

open Finset
open scoped lp

namespace PrimeSquares

/-- Every real exponent in the source range has the ENNReal parameters
and finite-exponent inclusions used by the operator theorem. -/
theorem improving_exponents_exist {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    ∃ P Q : ENNReal, 1 ≤ P ∧ 1 ≤ Q ∧ P.toReal = p ∧
      Q.toReal = holderConjugate p ∧ P ≤ 2 ∧ 2 ≤ Q ∧ P ≠ ⊤ ∧ Q ≠ ⊤ := by
  refine ⟨ENNReal.ofReal p, ENNReal.ofReal (holderConjugate p), ?_, ?_, ?_, ?_, ?_, ?_,
    ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  · simpa using ENNReal.ofReal_le_ofReal hp.le
  · simpa using ENNReal.ofReal_le_ofReal (holderConjugate_one_lt hp).le
  · exact ENNReal.toReal_ofReal (by linarith)
  · exact ENNReal.toReal_ofReal (holderConjugate_pos hp).le
  · simpa using ENNReal.ofReal_le_ofReal hp2
  · simpa using ENNReal.ofReal_le_ofReal (holderConjugate_two_le hp hp2)

/-- Full abstract Corollary 4.15, equation 4.16. Positivity of A is stated
in the source; positivity of B is already in HighLowEndpointInputs. -/
theorem highLow_AB_strong_improving
    {P Q : ENNReal} [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    {v s r γ β CB a α c₀ c₁ c κ M CLo CHi CErr CTwoA CTwoB : ℝ}
    (hv : v < 1) (hsv : 1 - v ≤ s) (hr : 0 < r) (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (hCB : 0 < CB) (ha : 0 ≤ a) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : 0 < c)
    (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hp : improvingCriticalExponent s r < P.toReal) (hp2 : P.toReal ≤ 2)
    (hconj : Q.toReal = holderConjugate P.toReal)
    (hTwoA : 0 ≤ CTwoA) (hTwoB : 0 ≤ CTwoB) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (N : ℝ) (KA KB : ℤ → ℂ) (windows : ℤ → Finset ℤ), 0 < N →
        HighLowEndpointInputs KA KB windows N v s r γ β CB a α c₀ c₁ c κ M CLo CHi CErr →
        KernelL2Bound KA CTwoA → KernelL2Bound KB CTwoB → NonnegativeKernel KA →
        ∃ TA TB : lp (fun _ : ℤ => ℂ) P →L[ℂ] lp (fun _ : ℤ => ℂ) Q,
          (∀ (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ),
            finiteConvolution KA F f x = TA (finiteInputLp F f P) x) ∧
          (∀ (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ),
            finiteConvolution KB F f x = TB (finiteInputLp F f P) x) ∧
          ∀ f, ‖TA f‖ + ‖TB f‖ ≤
            D * N^(1/Q.toReal-1/P.toReal) * ‖f‖ := by
  have hs : 0 < s := by linarith
  have hp1 : 1 < P.toReal := (improvingCriticalExponent_one_lt hs hr).trans hp
  have hP : P ≠ ⊤ := by
    intro hz
    simp only [hz, ENNReal.toReal_top] at hp1
    linarith
  have hQpos : 0 < Q.toReal := by rw [hconj]; exact holderConjugate_pos hp1
  have hQ : Q ≠ ⊤ := by
    intro hz
    simp only [hz, ENNReal.toReal_top, lt_self_iff_false] at hQpos
  have hP2 : P ≤ 2 := (ENNReal.toReal_le_toReal hP (by norm_num)).mp (by simpa using hp2)
  have h2Q : 2 ≤ Q := (ENNReal.toReal_le_toReal (by norm_num) hQ).mp
    (by simpa only [ENNReal.toReal_ofNat, hconj] using holderConjugate_two_le hp1 hp2)
  have hscale : 1/Q.toReal-1/P.toReal = 1-2/P.toReal := by
    rw [hconj, holderConjugate_scaling hp1]
  by_cases htwo : P.toReal = 2
  · refine ⟨CTwoA + CTwoB + 1, by linarith, ?_⟩
    intro N KA KB windows hN H h2A h2B _
    obtain ⟨TA, TB, heA, heB, hb⟩ := kernelLp_pair_bound
      (kernelLpBound_of_l2 h2A hP2 h2Q hQ) (kernelLpBound_of_l2 h2B hP2 h2Q hQ)
    refine ⟨TA, TB, ?_, ?_, ?_⟩
    · intro F f x
      exact (kernelLp_realization_finiteInput TA heA F f x).symm
    · intro F f x
      exact (kernelLp_realization_finiteInput TB heB F f x).symm
    intro f
    rw [hscale, htwo]
    norm_num
    exact (hb f).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg f))
  have hpLT : P.toReal < 2 := lt_of_le_of_ne hp2 htwo
  let q := (improvingCriticalExponent s r + P.toReal) / 2
  have hq0 : 0 < q := by
    have := improvingCriticalExponent_one_lt hs hr
    dsimp [q]
    linarith
  have hqcrit : improvingCriticalExponent s r < q := by dsimp [q]; linarith
  have hqp : q < P.toReal := by dsimp [q]; linarith
  have hq2 : q ≤ 2 := hqp.le.trans hp2
  have hq1 : 1 < q := (improvingCriticalExponent_one_lt hs hr).trans hqcrit
  obtain ⟨A, hA, hrestricted⟩ := highLow_AB_restricted_improving hv hsv hr hβ hβγ hCB ha hc₀ hc₁ hc
    hκ0 hκ1 hqcrit hq2 hTwoA hTwoB
  obtain ⟨hgapA, hgapB⟩ := interpolation_gaps_pos hq0 hqp hpLT
  let DA := interpolationWeightConstant A CTwoA (1/q-1/P.toReal) (1/P.toReal-1/2) *
    (3 : ℝ)^(2/P.toReal)
  let DB := interpolationWeightConstant A CTwoB (1/q-1/P.toReal) (1/P.toReal-1/2) *
    (3 : ℝ)^(2/P.toReal)
  have hDA : 0 ≤ DA := mul_nonneg
    (interpolationWeightConstant_nonneg hA.le hTwoA hgapA hgapB) (by positivity)
  have hDB : 0 ≤ DB := mul_nonneg
    (interpolationWeightConstant_nonneg hA.le hTwoB hgapA hgapB) (by positivity)
  refine ⟨DA + DB + 1, by linarith, ?_⟩
  intro N KA KB windows hN H h2A h2B hKA
  have hpa : ∀ F G : Finset ℤ, ‖restrictedKernelPairing KA F G‖ ≤
      A * N^(1-2/q) * (F.card : ℝ)^(1/q) * (G.card : ℝ)^(1/q) := by
    intro F G
    have hh := (le_add_of_nonneg_right (norm_nonneg (restrictedKernelPairing KB F G))).trans
      (hrestricted N KA KB windows hN H h2A h2B F G)
    rwa [holderConjugate_scaling hq1] at hh
  have hpb : ∀ F G : Finset ℤ, ‖restrictedKernelPairing KB F G‖ ≤
      A * N^(1-2/q) * (F.card : ℝ)^(1/q) * (G.card : ℝ)^(1/q) := by
    intro F G
    have hh := (le_add_of_nonneg_left (norm_nonneg (restrictedKernelPairing KA F G))).trans
      (hrestricted N KA KB windows hN H h2A h2B F G)
    rwa [holderConjugate_scaling hq1] at hh
  have hstrongA : KernelLpBound KA P Q (DA * N^(1-2/P.toReal)) :=
    restricted_l2_strong_improving hP2 h2Q hQ hconj hp1 hN hq0 hqp hpLT
      hA.le hTwoA hKA h2A hpa
  have hstrongB : KernelLpBound KB P Q (DB * N^(1-2/P.toReal)) :=
    restricted_l2_strong_improving hP2 h2Q hQ hconj hp1 hN hq0 hqp hpLT
      hA.le hTwoB H.nonnegative h2B hpb
  obtain ⟨TA, TB, heA, heB, hb⟩ := kernelLp_pair_bound hstrongA hstrongB
  refine ⟨TA, TB, ?_, ?_, ?_⟩
  · intro F f x
    exact (kernelLp_realization_finiteInput TA heA F f x).symm
  · intro F f x
    exact (kernelLp_realization_finiteInput TB heB F f x).symm
  intro f
  rw [hscale]
  calc
    _ ≤ (DA * N^(1-2/P.toReal) + DB * N^(1-2/P.toReal)) * ‖f‖ := hb f
    _ = (DA + DB) * N^(1-2/P.toReal) * ‖f‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hN.le _)) (norm_nonneg f)

end PrimeSquares
