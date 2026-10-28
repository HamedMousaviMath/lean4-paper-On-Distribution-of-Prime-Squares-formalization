import PrimeSquares.GoldbachCircleMajorModels

set_option autoImplicit false
open Finset Metric
namespace PrimeSquares

theorem goldbach_square_circle_major_sw (HSW : RawPrimeSiegelWalfiszInput)
    {t C : ℝ} (ht : 0<t) (hC : 0≤C) :
    ∃ K : ℝ,0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      1≤Real.log N ∧ 1≤(Real.log N)^C ∧ 2*((Real.log N)^C)^3<(N:ℝ)^2 ∧
      ∀ U : ℝ,2≤U → U≤N → ∀ θ∈GoldbachMajorArcs N ((Real.log N)^C),
        ‖goldbachPrimeSquarePolynomial U θ-goldbachSquareMajorModel N ((Real.log N)^C) U θ‖≤
          K*(N:ℝ)*(Real.log N)^(-t) := by
  obtain ⟨K,hK,N₁,hN₁,hSW⟩ := goldbach_square_major_siegel_walfisz HSW ht hC
  obtain ⟨N₂,hN₂,hgeo⟩ := goldbach_major_geometry_eventual hC
  refine ⟨K,hK,max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro N hN
  obtain ⟨hl,hR,hsep,_⟩ := hgeo N ((le_max_right _ _).trans hN)
  have hNnat : 1≤N := by omega
  refine ⟨hl,hR,hsep,?_⟩
  intro U hU hUN θ hθ
  obtain ⟨r,hr,harc⟩ := (mem_goldbachMajorArcs N (by linarith : 0≤(Real.log N)^C) θ).mp hθ
  have hqR := ((mem_sourceRationalCenters (by linarith : 0≤(Real.log N)^C) r).mp hr).2
  have hγ : |goldbachArcCoordinate r θ|≤(Real.log N)^C/(N:ℝ)^2 := by
    simpa only [goldbachArcCoordinate_abs] using harc
  have he : (((r.num:ℝ)/r.den+goldbachArcCoordinate r θ:ℝ):PrimeCircle)=θ := by
    simpa only [Rat.cast_def] using goldbachArcCoordinate_reconstruct r θ
  have hb := hSW N ((le_max_left _ _).trans hN) r.den r.den_pos hqR r.num U
    (goldbachArcCoordinate r θ) hU hUN hγ inferInstance
  rw [he] at hb
  rw [goldbachSquareMajorModel,goldbachArcModel_on_arc N hNnat hR hsep _ r hr θ harc]
  exact hb

theorem goldbach_linear_circle_major_bv (HBV : RawPrimeBombieriVinogradovInput)
    {t C δ : ℝ} (ht : 0<t) (hC : 0≤C) (hδ : 0<δ) :
    ∃ B₀ K : ℝ,0≤B₀ ∧ 0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      1≤Real.log N ∧ 1≤(Real.log N)^C ∧ 2*((Real.log N)^C)^3<(N:ℝ)^2 ∧
      ∀ B L₀ : ℝ,B₀≤B → L₀<(N:ℝ)^(2-δ) →
      ∀ V : ℕ→ℝ,(∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L₀ →
        V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) →
      (∀ i∈goldbachCoefficientIndices L₀ V,2≤(N:ℝ)^2/i.1) ∧
      ∀ a : ℕ×ℕ→ℕ,(∀ i∈goldbachCoefficientIndices L₀ V,(a i).Coprime i.2) →
      ∀ W : ℕ×ℕ→ℝ,(∀ i∈goldbachCoefficientIndices L₀ V,2≤W i) →
      ∀ θ∈GoldbachMajorArcs N ((Real.log N)^C),
      (∑ i∈goldbachCoefficientIndices L₀ V,
        ‖goldbachProgressionPolynomial N i.1 i.2 (a i) (W i) θ-
          goldbachProgressionMajorModel N i.1 i.2 (a i) ((Real.log N)^C) (W i) θ‖)≤
            K*(N:ℝ)^2*(Real.log N)^(-t) := by
  obtain ⟨B₀,K,hB₀,hK,N₁,hN₁,hBV⟩ := goldbach_linear_major_bombieri_vinogradov HBV ht hC hδ
  obtain ⟨N₂,hN₂,hgeo⟩ := goldbach_major_geometry_eventual hC
  obtain ⟨N₃,hN₃,hscale⟩ := goldbach_bv_source_eventual_threshold (L:=0) hδ (by norm_num : (4:ℝ)≤4)
  refine ⟨B₀,K,hB₀,hK,max N₁ (max N₂ N₃),hN₁.trans (le_max_left _ _),?_⟩
  intro N hN
  have hNN₁ := (le_max_left N₁ (max N₂ N₃)).trans hN
  have hNN₂ := (le_max_left N₂ N₃).trans ((le_max_right N₁ (max N₂ N₃)).trans hN)
  have hNN₃ := (le_max_right N₂ N₃).trans ((le_max_right N₁ (max N₂ N₃)).trans hN)
  obtain ⟨hl,hR,hsep,_⟩ := hgeo N hNN₂
  obtain ⟨_,_,hminScale⟩ := hscale N hNN₃
  have hNnat : 1≤N := by omega
  refine ⟨hl,hR,hsep,?_⟩
  intro B L₀ hB hL V hV
  have hX : ∀ i∈goldbachCoefficientIndices L₀ V,2≤(N:ℝ)^2/i.1 := by
    intro i hi
    obtain ⟨hℓ,hℓL,_,_⟩ := (mem_goldbachCoefficientIndices L₀ V i.1 i.2).mp hi
    have hx := (goldbach_progression_scale_logs N i.1 hNnat hℓ δ (hℓL.trans hL)).1
    linarith
  refine ⟨hX,?_⟩
  intro a ha W hW θ hθ
  obtain ⟨r,hr,harc⟩ := (mem_goldbachMajorArcs N (by linarith : 0≤(Real.log N)^C) θ).mp hθ
  have hqR := ((mem_sourceRationalCenters (by linarith : 0≤(Real.log N)^C) r).mp hr).2
  have hγ : |goldbachArcCoordinate r θ|≤(Real.log N)^C/(N:ℝ)^2 := by
    simpa only [goldbachArcCoordinate_abs] using harc
  have he : (((r.num:ℝ)/r.den+goldbachArcCoordinate r θ:ℝ):PrimeCircle)=θ := by
    simpa only [Rat.cast_def] using goldbachArcCoordinate_reconstruct r θ
  have hb := hBV N hNN₁ B L₀ hB hL V hV r.den hqR a ha W hW r.num (goldbachArcCoordinate r θ) hγ
  have hsum : (∑ i∈goldbachCoefficientIndices L₀ V,
      ‖goldbachProgressionPolynomial N i.1 i.2 (a i) (W i) θ-
        goldbachProgressionMajorModel N i.1 i.2 (a i) ((Real.log N)^C) (W i) θ‖)=
      ∑ i∈goldbachCoefficientIndices L₀ V,
        ‖goldbachLinearMajorError N i.1 i.2 r.den (a i) r.num (W i) (goldbachArcCoordinate r θ)‖ := by
    apply sum_congr rfl
    intro i _
    rw [goldbachProgressionMajorModel,goldbachArcModel_on_arc N hNnat hR hsep _ r hr θ harc]
    unfold goldbachLinearMajorError
    rw [he]
  rw [hsum]
  exact hb

end PrimeSquares
