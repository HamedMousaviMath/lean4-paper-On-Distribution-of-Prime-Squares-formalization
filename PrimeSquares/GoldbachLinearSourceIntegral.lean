import PrimeSquares.GoldbachLinearMajorCounts

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

noncomputable def goldbachLinearSourceIntegral (N ℓ : ℕ) (W γ : ℝ) : ℂ :=
  ∫ v in {v : ℝ | 2≤v ∧ v≤W ∧ (ℓ:ℝ)*v<(N:ℝ)^2},
    realFourierPhase (((ℓ:ℝ)*γ)*v)*((Real.log v)⁻¹:ℝ)

theorem goldbach_linear_source_domain_ae (N ℓ : ℕ) (hℓ : 0<ℓ) (W : ℝ) :
    {v : ℝ | 2≤v ∧ v≤W ∧ (ℓ:ℝ)*v<(N:ℝ)^2}=ᵐ[volume]
      Set.Ioc 2 (min W ((N:ℝ)^2/ℓ)) := by
  have hlR : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  filter_upwards [volume.ae_ne (2:ℝ),volume.ae_ne ((N:ℝ)^2/ℓ)] with v hv2 hvX
  apply propext
  simp only [Set.mem_Ioc,le_min_iff]
  constructor
  · rintro ⟨h2,hW,hprod⟩
    have hX : v<(N:ℝ)^2/ℓ := (lt_div_iff₀ hlR).mpr (by nlinarith)
    exact ⟨lt_of_le_of_ne h2 hv2.symm,hW,hX.le⟩
  · rintro ⟨h2,hW,hX⟩
    have hlt : v<(N:ℝ)^2/ℓ := lt_of_le_of_ne hX hvX
    exact ⟨h2.le,hW,by have hp := (lt_div_iff₀ hlR).mp hlt;nlinarith⟩

theorem goldbach_linear_source_integral (N ℓ : ℕ) (hℓ : 0<ℓ) (W γ : ℝ) :
    goldbachLinearSourceIntegral N ℓ W γ=
      goldbachLinearIntegral (min W ((N:ℝ)^2/ℓ)) ((ℓ:ℝ)*γ) :=
  setIntegral_congr_set (goldbach_linear_source_domain_ae N ℓ hℓ W)

theorem goldbach_linear_source_major_from_counts (N k q a ℓ : ℕ) [NeZero k] [NeZero q]
    (hℓ : 0<ℓ) (ha : a.Coprime k) {W B : ℝ} (hW : 2≤W)
    (hX : 2≤(N:ℝ)^2/ℓ) (hB : 0≤B) (A : ℤ) (γ : ℝ)
    (herr : ∀ b∈goldbachMajorResidues k q a,∀ y∈Set.Icc 2 ((N:ℝ)^2/ℓ),
      ‖(goldbachPrimeProgressionCount (k.lcm q) b y:ℂ)-goldbachPrimeProgressionModel (k.lcm q) y‖≤B) :
    ‖goldbachProgressionPolynomial N ℓ k a W (((A:ℝ)/q+γ:ℝ):PrimeCircle)-
      (upsilon q k (a:ℤ) (-((A:ZMod q)*(ℓ:ZMod q)))/(k.totient:ℂ))*
        goldbachLinearSourceIntegral N ℓ W γ‖≤
          1+(q:ℝ)+(q:ℝ)*(B*(1+2*Real.pi*|((ℓ:ℝ)*γ)| *min W ((N:ℝ)^2/ℓ))) := by
  have hy : 2≤min W ((N:ℝ)^2/ℓ) := le_min hW hX
  have hc : ∀ b∈goldbachMajorResidues k q a,∀ y∈Set.Icc 2 (min W ((N:ℝ)^2/ℓ)),
      ‖(goldbachPrimeProgressionCount (k.lcm q) b y:ℂ)-goldbachPrimeProgressionModel (k.lcm q) y‖≤B := by
    intro b hb y hy
    exact herr b hb y ⟨hy.1,hy.2.trans (min_le_right _ _)⟩
  have hb := goldbach_linear_major_from_counts N k q a ℓ hℓ ha hy (min_le_right _ _) hB A γ hc
  have hF : goldbachProgressionPolynomial N ℓ k a (min W ((N:ℝ)^2/ℓ))=
      goldbachProgressionPolynomial N ℓ k a W := by
    unfold goldbachProgressionPolynomial
    rw [goldbach_progression_cutoff_min N ℓ k a hℓ (by linarith)]
  rw [hF,←goldbach_linear_source_integral N ℓ hℓ W γ] at hb
  exact hb

theorem goldbach_linear_source_major_numeric (N k q a ℓ : ℕ) [NeZero k] [NeZero q]
    (hN : 1≤N) (hℓ : 0<ℓ) (ha : a.Coprime k) {W B R : ℝ}
    (hW : 2≤W) (hX : 2≤(N:ℝ)^2/ℓ) (hB : 0≤B) (hR : 1≤R) (hqR : (q:ℝ)≤R)
    (A : ℤ) (γ : ℝ) (hγ : |γ|≤R/(N:ℝ)^2)
    (herr : ∀ b∈goldbachMajorResidues k q a,∀ y∈Set.Icc 2 ((N:ℝ)^2/ℓ),
      ‖(goldbachPrimeProgressionCount (k.lcm q) b y:ℂ)-goldbachPrimeProgressionModel (k.lcm q) y‖≤B) :
    ‖goldbachProgressionPolynomial N ℓ k a W (((A:ℝ)/q+γ:ℝ):PrimeCircle)-
      (upsilon q k (a:ℤ) (-((A:ZMod q)*(ℓ:ZMod q)))/(k.totient:ℂ))*
        goldbachLinearSourceIntegral N ℓ W γ‖≤
          1+(q:ℝ)+(1+2*Real.pi)*R^2*B := by
  have hnR : (0:ℝ)<N := by exact_mod_cast hN
  have hlR : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  let Y := min W ((N:ℝ)^2/ℓ)
  have hy0 : 0≤Y := by dsimp [Y];linarith [le_min hW hX]
  have hprod : Y*(ℓ:ℝ)≤(N:ℝ)^2 := (le_div_iff₀ hlR).mp (min_le_right _ _)
  have hγN : |γ| *(N:ℝ)^2≤R := (le_div_iff₀ (sq_pos_of_pos hnR)).mp hγ
  have hγY : |((ℓ:ℝ)*γ)| *Y≤R := calc
    _=|γ| *(Y*(ℓ:ℝ)) := by rw [abs_mul,abs_of_pos hlR];ring
    _≤|γ| *(N:ℝ)^2 := mul_le_mul_of_nonneg_left hprod (abs_nonneg γ)
    _≤R := hγN
  have hfac : 1+2*Real.pi*|((ℓ:ℝ)*γ)| *Y≤(1+2*Real.pi)*R := by
    have hp := mul_le_mul_of_nonneg_left hγY (by positivity : 0≤2*Real.pi)
    nlinarith
  have hbudget : 0≤B*(1+2*Real.pi*|((ℓ:ℝ)*γ)| *Y) := by positivity
  apply (goldbach_linear_source_major_from_counts N k q a ℓ hℓ ha hW hX hB A γ herr).trans
  apply add_le_add le_rfl
  calc
    _≤R*(B*(1+2*Real.pi*|((ℓ:ℝ)*γ)| *Y)) := mul_le_mul_of_nonneg_right hqR hbudget
    _≤R*(B*((1+2*Real.pi)*R)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfac hB) (by linarith : 0≤R)
    _=(1+2*Real.pi)*R^2*B := by ring

end PrimeSquares
