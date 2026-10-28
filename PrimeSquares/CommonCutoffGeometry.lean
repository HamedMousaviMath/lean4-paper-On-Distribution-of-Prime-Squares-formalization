import PrimeSquares.CircleAnnularCutoffKernel
import PrimeSquares.SmoothCutoffSourceLiftCompatibility
import PrimeSquares.CircleSourceCutoffProduct
import PrimeSquares.CircleSourceCutoffLiftValue
import PrimeSquares.CircleAnnularSource
import PrimeSquares.FiniteDisjointSymbolBound

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def circleWidthAnnular (N : ℕ) (hN : 1≤N) (β a : ℝ)
    (ha : 2≤a) (r : ℚ) : C(PrimeCircle,ℂ) :=
  (circleAnnularCutoff N hN β a ha).comp
    ⟨fun ξ => ξ-((r : ℝ) : PrimeCircle),continuous_id.sub continuous_const⟩

theorem circleWidthAnnular_real (N : ℕ) (hN : 1≤N) (β a : ℝ)
    (ha : 2≤a) (r : ℚ) (ξ : ℝ) :
    circleWidthAnnular N hN β a ha r (ξ : PrimeCircle)=
      ∑' n : ℤ,annularOscillatoryModel N β (ξ-(r : ℝ)+n)*
        Complex.ofReal (sourceArcCutoff (a*(ξ-(r : ℝ)+n))) := by
  change compactCircleLift (annularCutoffSymbol N hN β a)
    (annularCutoffSymbol_support N hN β ha) ((ξ : PrimeCircle)-((r : ℝ) : PrimeCircle))=_
  rw [←AddCircle.coe_sub,compactCircleLift_all_real]
  rfl

theorem common_cutoff_source_core {a : ℝ} {s : ℕ} (ha : 2*(16 : ℝ)^s≤a)
    {θ : ℝ} (hθ : sourceArcCutoff (a*θ)≠0) : sourceArcCutoffScale s θ=1 := by
  have hp : 0<a := (by positivity : 0<2*(16 : ℝ)^s).trans_le ha
  apply sourceArcCutoffScale_core
  exact (scaledSmoothCutoff_radius hp hθ).le.trans
    (one_div_le_one_div_of_le (by positivity) ha)

theorem circleAnnularSource_eq_lift (N : ℕ) (hN : 1≤N) (β : ℝ) {s : ℕ}
    (hs : 1≤s) (r : ℚ) (ξ : ℝ) (k : ℤ)
    (hk : sourceArcCutoffScale s (ξ-(r : ℝ)+k)≠0) :
    circleAnnularSource N hN β s r (ξ : PrimeCircle)=
      annularOscillatoryModel N β (ξ-(r : ℝ)+k)*
        Complex.ofReal (sourceArcCutoffScale s (ξ-(r : ℝ)+k)) := by
  rw [circleAnnularSource_real]
  apply tsum_eq_single k
  intro l hl
  have hz : sourceArcCutoffScale s (ξ-(r : ℝ)+l)=0 := by
    by_contra h
    exact hl (source_cutoff_single_lift hs r ξ l k h hk)
  rw [hz,Complex.ofReal_zero,mul_zero]

theorem circleWidthAnnular_on_source_lift (N : ℕ) (hN : 1≤N) (β a : ℝ)
    (ha : 4≤a) {s : ℕ} (hs : 1≤s) (r : ℚ) (ξ : ℝ) (k : ℤ)
    (hk : sourceArcCutoffScale s (ξ-(r : ℝ)+k)≠0) :
    circleWidthAnnular N hN β a (by linarith) r (ξ : PrimeCircle)=
      annularOscillatoryModel N β (ξ-(r : ℝ)+k)*
        Complex.ofReal (sourceArcCutoff (a*(ξ-(r : ℝ)+k))) := by
  rw [circleWidthAnnular_real]
  apply tsum_eq_single k
  intro l hl
  have hz : sourceArcCutoff (a*(ξ-(r : ℝ)+l))=0 := by
    by_contra h
    exact hl (smoothCutoff_source_lifts_unique ha hs r ξ k l hk h).symm
  rw [hz,Complex.ofReal_zero,mul_zero]

theorem common_cutoff_zero_of_source_zero {a : ℝ} {s : ℕ}
    (hs : 1≤s) (hwide : 2*(16 : ℝ)^s≤a) (r : ℚ) (ξ : ℝ)
    (hz : circleSourceCutoff s r (ξ : PrimeCircle)=0) (k : ℤ) :
    sourceArcCutoff (a*(ξ-(r : ℝ)+k))=0 := by
  by_contra h
  have hc := common_cutoff_source_core hwide h
  have hn : sourceArcCutoffScale s (ξ-(r : ℝ)+k)≠0 := by rw [hc];norm_num
  have he := circleSourceCutoff_eq_lift hs r ξ k hn
  rw [hz,hc,Complex.ofReal_one] at he
  exact zero_ne_one he

theorem circleSmoothCutoff_supported_in_source {a : ℝ} (ha : 1≤a) {s : ℕ}
    (hs : 1≤s) (hwide : 2*(16 : ℝ)^s≤a) (r : ℚ) (ξ : PrimeCircle)
    (hz : circleSourceCutoff s r ξ=0) : circleSmoothCutoff a ha r ξ=0 := by
  let x := (AddCircle.equivIco 1 (-(1/2) : ℝ) ξ : ℝ)
  have he : (x : PrimeCircle)=ξ := AddCircle.coe_equivIco
  rw [←he] at hz ⊢
  rw [circleSmoothCutoff_real]
  simp only [common_cutoff_zero_of_source_zero hs hwide r x hz,Complex.ofReal_zero,tsum_zero]

theorem circleWidthAnnular_factorization (N : ℕ) (hN : 1≤N) (β : ℝ)
    {a : ℝ} (ha : 4≤a) {s : ℕ} (hs : 1≤s) (hwide : 2*(16 : ℝ)^s≤a) (r : ℚ) :
    circleWidthAnnular N hN β a (by linarith) r=
      circleAnnularSource N hN β s r*circleSmoothCutoff a (by linarith) r := by
  ext ξ
  let x := (AddCircle.equivIco 1 (-(1/2) : ℝ) ξ : ℝ)
  have he : (x : PrimeCircle)=ξ := AddCircle.coe_equivIco
  rw [←he]
  change circleWidthAnnular N hN β a _ r (x : PrimeCircle)=
    circleAnnularSource N hN β s r (x : PrimeCircle)*circleSmoothCutoff a _ r (x : PrimeCircle)
  by_cases hz : circleSourceCutoff s r (x : PrimeCircle)=0
  · rw [circleSmoothCutoff_supported_in_source (by linarith) hs hwide r _ hz,mul_zero,
      circleWidthAnnular_real]
    simp only [common_cutoff_zero_of_source_zero hs hwide r x hz,
      Complex.ofReal_zero,mul_zero,tsum_zero]
  · obtain ⟨k,hk⟩ := circleSourceCutoff_nonzero_lift x hz
    rw [circleWidthAnnular_on_source_lift N hN β a ha hs r x k hk,
      circleAnnularSource_eq_lift N hN β hs r x k hk,
      circleSmoothCutoff_on_source_lift (by linarith) ha hs r x k hk]
    by_cases hc : sourceArcCutoff (a*(x-(r : ℝ)+k))=0
    · rw [hc,Complex.ofReal_zero,mul_zero,mul_zero]
    · rw [common_cutoff_source_core hwide hc,Complex.ofReal_one,mul_one]

theorem common_circle_cutoff_norm {a : ℝ} (ha : 4≤a) {s : ℕ}
    (hs : 1≤s) (hwide : 2*(16 : ℝ)^s≤a) (r : ℚ) (ξ : PrimeCircle) :
    ‖circleSmoothCutoff a (by linarith) r ξ‖≤1 := by
  let x := (AddCircle.equivIco 1 (-(1/2) : ℝ) ξ : ℝ)
  have he : (x : PrimeCircle)=ξ := AddCircle.coe_equivIco
  rw [←he]
  by_cases hz : circleSourceCutoff s r (x : PrimeCircle)=0
  · rw [circleSmoothCutoff_supported_in_source (by linarith) hs hwide r _ hz,norm_zero]
    norm_num
  · obtain ⟨k,hk⟩ := circleSourceCutoff_nonzero_lift x hz
    rw [circleSmoothCutoff_on_source_lift (by linarith) ha hs r x k hk,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sourceArcCutoff_nonneg _)]
    exact sourceArcCutoff_le_one _

theorem common_circle_projection_norm {a : ℝ} (ha : 4≤a) {s : ℕ} (hs : 2≤s)
    (hwide : 2*(16 : ℝ)^s≤a) (Γ : Finset ℚ)
    (hcan : ∀ r∈Γ,r∈Set.Ico (0 : ℚ) 1)
    (hden : ∀ r∈Γ,(r.den : ℝ)≤(2 : ℝ)^(s+1)) :
    ‖integerMultiplier (∑ r∈Γ,circleSmoothCutoff a (by linarith) r)‖≤1 := by
  apply integerMultiplier_opNorm_le_of_bound _ (by norm_num)
  apply finite_disjoint_symbol_bound Γ (fun r => circleSmoothCutoff a (by linarith) r)
  · intro r hr t ht hrt ξ
    rcases circleSourceCutoff_disjoint hs (hcan r hr) (hcan t ht) hrt (hden r hr) (hden t ht) ξ with h | h
    · exact Or.inl (circleSmoothCutoff_supported_in_source (by linarith) (by omega) hwide r ξ h)
    · exact Or.inr (circleSmoothCutoff_supported_in_source (by linarith) (by omega) hwide t ξ h)
  · norm_num
  · intro r _ ξ
    exact common_circle_cutoff_norm ha (by omega) hwide r ξ

end PrimeSquares
