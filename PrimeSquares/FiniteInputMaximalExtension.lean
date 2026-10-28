import PrimeSquares.IntegerLpMeasureBridge
import PrimeSquares.SchwartzConvolutionIdentity

set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal lp Topology
namespace PrimeSquares

/-- Internal finite-input property, to be supplied by the proved concrete low
estimate; it is not an independent analytic input. -/
def FiniteInputLpMaximalBound (T : ℕ → (ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ)))
    (p : ℝ≥0∞) (K : ℝ) : Prop :=
  ∀ (A : Finset ℤ) (a : ℤ → ℂ), ∃ G : ℤ → ℝ,
    (∀ x, 0 ≤ G x) ∧ MemLp G p Measure.count ∧
      (∀ j x, ‖T j (finiteInputLp A a 2) x‖ ≤ G x) ∧
      eLpNorm G p Measure.count ≤ ENNReal.ofReal K*eLpNorm (finiteInputLp A a 2 : ℤ → ℂ) p Measure.count

/-- The same concrete countable operator assertion on the whole L2/Lp
intersection. For p<=2 on the integers, every integer lp input lies here. -/
def AllInputLpMaximalBound (T : ℕ → (ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ)))
    (p : ℝ≥0∞) (K : ℝ) : Prop :=
  ∀ f : ℓ²(ℤ,ℂ), MemLp (f : ℤ → ℂ) p Measure.count →
    ∃ G : ℤ → ℝ, (∀ x, 0 ≤ G x) ∧ MemLp G p Measure.count ∧
      (∀ j x, ‖T j f x‖ ≤ G x) ∧
      eLpNorm G p Measure.count ≤ ENNReal.ofReal K*eLpNorm (f : ℤ → ℂ) p Measure.count

theorem finiteInputLp_count_norm_le (A : Finset ℤ) (f : ℤ → ℂ) (p : ℝ≥0∞)
    :
    eLpNorm (finiteInputLp A f 2 : ℤ → ℂ) p Measure.count ≤ eLpNorm f p Measure.count := by
  apply eLpNorm_mono (by exact AEStronglyMeasurable.of_discrete)
  intro x
  rw [finiteInputLp_apply]
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (f x)

theorem finite_input_maximal_extension (T : ℕ → (ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ)))
    {p : ℝ≥0∞} (hp : 0 < p.toReal) {K : ℝ} (H : FiniteInputLpMaximalBound T p K) :
    AllInputLpMaximalBound T p K := by
  intro f hf
  let B := ENNReal.ofReal K*eLpNorm (f : ℤ → ℂ) p Measure.count
  have hB : B ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  let g : ℕ → ℤ → ℂ := fun j x => T j f x
  have hbound (I : Finset ℕ) : MemLp (finiteCoordinateMaximum I g) p Measure.count ∧
      eLpNorm (finiteCoordinateMaximum I g) p Measure.count ≤ B := by
    let v : Finset ℤ → ℓ²(ℤ,ℂ) := fun A => finiteInputLp A (f : ℤ → ℂ) 2
    have hv : Tendsto v atTop (𝓝 f) := lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) f
    have hfinite (A : Finset ℤ) : eLpNorm (finiteCoordinateMaximum I (fun j x => T j (v A) x)) p Measure.count ≤ B := by
      obtain ⟨G, hG0, hGm, hGdom, hGnorm⟩ := H A (f : ℤ → ℂ)
      have hm : AEStronglyMeasurable (finiteCoordinateMaximum I (fun j x => T j (v A) x)) Measure.count :=
        AEStronglyMeasurable.of_discrete
      have hd : ∀ᵐ x ∂Measure.count,
          ‖finiteCoordinateMaximum I (fun j x => T j (v A) x) x‖ ≤ G x := by
        exact Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (finiteCoordinateMaximum_nonneg I _ x)]
          exact finiteCoordinateMaximum_le I _ x (hG0 x) (fun j _ => hGdom j x))
      exact (eLpNorm_mono_ae hm (hd.mono (fun x hx => hx.trans (le_abs_self (G x))))).trans
        (hGnorm.trans (mul_le_mul_right (finiteInputLp_count_norm_le A (f : ℤ → ℂ) p) _))
    have hmeas : AEStronglyMeasurable (finiteCoordinateMaximum I g) Measure.count :=
      AEStronglyMeasurable.of_discrete
    have ht : ∀ᵐ x ∂Measure.count, Tendsto
        (fun A : Finset ℤ => finiteCoordinateMaximum I (fun j x => T j (v A) x) x) atTop
        (𝓝 (finiteCoordinateMaximum I g x)) := by
      apply Filter.Eventually.of_forall
      intro x
      have hc : Continuous (fun u : ℓ²(ℤ,ℂ) => finiteCoordinateMaximum I
          (fun j (u : ℓ²(ℤ,ℂ)) => T j u x) u) :=
        finiteCoordinateMaximum_continuous I _ (fun j _ =>
          ((lp.evalCLM ℂ (E := fun _ : ℤ => ℂ) (p := 2) x).continuous.comp (T j).continuous))
      exact hc.continuousAt.tendsto.comp hv
    have hn : eLpNorm (finiteCoordinateMaximum I g) p Measure.count ≤ B :=
      Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hfinite)
        (fun _ => AEStronglyMeasurable.of_discrete) hmeas ht
    exact ⟨lt_of_le_of_lt hn hB.lt_top, hn⟩
  exact uniform_finite_integer_Lp_majorant (ENNReal.toReal_pos_iff.mp hp).1.ne' g hB hbound

theorem allInputLpMaximalBound_integerLp
    (T : ℕ → (ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ))) {p : ℝ≥0∞}
    (hp : 0 < p.toReal) (hp2 : p ≤ 2) {K : ℝ} (hK : 0 ≤ K)
    (H : AllInputLpMaximalBound T p K) (f : ℓ^p(ℤ,ℂ)) :
    ∃ G : ℓ^p(ℤ,ℝ), (∀ x, 0 ≤ G x) ∧
      (∀ j x, ‖T j (lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) hp2 f) x‖ ≤ G x) ∧
      ‖G‖ ≤ K*‖f‖ := by
  let f2 : ℓ²(ℤ,ℂ) := lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) hp2 f
  have hf : MemLp (f2 : ℤ → ℂ) p Measure.count := count_memLp_of_memℓp hp (lp.memℓp f)
  obtain ⟨g, hg0, hgm, hgdom, hgnorm⟩ := H f2 hf
  let G : ℓ^p(ℤ,ℝ) := ⟨g, memℓp_of_count_memLp hp hgm⟩
  have hGnorm : eLpNorm g p Measure.count = ENNReal.ofReal ‖G‖ := eLpNorm_count_eq_lp_enorm hp G
  have hFnorm : eLpNorm (f2 : ℤ → ℂ) p Measure.count = ENNReal.ofReal ‖f‖ :=
    eLpNorm_count_eq_lp_enorm hp f
  rw [hGnorm, hFnorm, ←ENNReal.ofReal_mul hK] at hgnorm
  exact ⟨G, hg0, hgdom, (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK (lp.norm_nonneg' f))).mp hgnorm⟩

theorem allInputLpMaximalBound_maximum
    (T : ℕ → (ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ))) {p : ℝ≥0∞} {K : ℝ}
    (H : AllInputLpMaximalBound T p K) (f : ℓ²(ℤ,ℂ))
    (hf : MemLp (f : ℤ → ℂ) p Measure.count) :
    MemLp (countableCoordinateMaximum (fun j x => T j f x)) p Measure.count ∧
      eLpNorm (countableCoordinateMaximum (fun j x => T j f x)) p Measure.count ≤
        ENNReal.ofReal K*eLpNorm (f : ℤ → ℂ) p Measure.count := by
  obtain ⟨G, hG0, hGm, hGdom, hGnorm⟩ := H f hf
  have hm : AEStronglyMeasurable (countableCoordinateMaximum (fun j x => T j f x)) Measure.count :=
    AEStronglyMeasurable.of_discrete
  have hd : ∀ᵐ x ∂Measure.count,
      ‖countableCoordinateMaximum (fun j x => T j f x) x‖ ≤ G x := by
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ countableCoordinateMaximum (fun j x => T j f x) x from NNReal.coe_nonneg _)]
    change (((⨆ j : ℕ, ‖T j f x‖₊) : NNReal) : ℝ) ≤ G x
    exact_mod_cast (ciSup_le (fun j : ℕ => show ‖T j f x‖₊ ≤ ⟨G x, hG0 x⟩ from hGdom j x))
  exact ⟨hGm.mono' hm hd,
    (eLpNorm_mono_ae hm (hd.mono (fun x hx => hx.trans (le_abs_self (G x))))).trans hGnorm⟩

end PrimeSquares
