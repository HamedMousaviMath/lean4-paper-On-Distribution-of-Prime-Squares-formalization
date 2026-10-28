import PrimeSquares.FullSquareRealCircleModel
import PrimeSquares.FullSquareAnnularWeylBounds
import PrimeSquares.CircleFundamentalBounds
import PrimeSquares.PeriodizedMajorArcError

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def fullSquareCircleError (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) : C(PrimeCircle,ℂ) :=
  annularWeightedSquareAverageSymbol N (fun _ => 1)-
    varyingIndexAnnularBlock Γ N hN 1 rationalFullSquareGauss

noncomputable def fullSquareApproxBudget (E : ℝ) (N : ℕ) (R : ℝ) : ℝ :=
  4*E*Real.sqrt R/(N : ℝ)+6*quadraticIntegralConstant/Real.sqrt R+
    12*E/Real.sqrt (N : ℝ)+5*fullSquareRealTailBudget R

theorem fullSquareRealTailBudget_nonneg {R : ℝ} (hR : 1 ≤ R) : 0 ≤ fullSquareRealTailBudget R := by
  have hl := Real.log_nonneg hR
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold fullSquareRealTailBudget
  positivity

theorem fullSquareFiniteError_major {N : ℕ} (hN : 2 ≤ N) (Γ : Finset ℚ)
    {R ξ δ : ℝ} (hR : 1 ≤ R) (hΓ : ∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ, (r.den : ℝ) ≤ R) {s : ℚ} (hs : s ∈ Γ)
    (hsep : 2*R^3 < (N : ℝ)^2) (hcore : 2*R^4 ≤ (N : ℝ)^2)
    (harc : |ξ-(s : ℝ)| ≤ R/((s.den : ℝ)*(N : ℝ)^2))
    (hmain : ‖annularWeightedSquareAverageSymbol N (fun _ => 1) (ξ : PrimeCircle)-
      rationalFullSquareGauss s*annularOscillatoryModel N 1 (ξ-(s : ℝ))‖ ≤ δ) :
    ‖annularWeightedSquareAverageSymbol N (fun _ => 1) (ξ : PrimeCircle)-fullSquareFiniteModel Γ N ξ‖ ≤
      δ+fullSquareRealTailBudget R := by
  classical
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R := by linarith
  have hcut := rationalMajorArc_cutoff_core (by omega : 1 ≤ N) (hd s hs) hcore harc
  have hterm : fullSquareRationalModelTerm N s ξ =
      rationalFullSquareGauss s*annularOscillatoryModel N 1 (ξ-(s : ℝ)) := by
    rw [fullSquareRationalModelTerm, hcut, Complex.ofReal_one, mul_one]
  have hsum : fullSquareRationalModelTerm N s ξ+fullSquareFiniteModel (Γ.erase s) N ξ =
      fullSquareFiniteModel Γ N ξ := add_sum_erase Γ (fun r => fullSquareRationalModelTerm N r ξ) hs
  have hout : ∀ r ∈ Γ.erase s, R/((r.den : ℝ)*(N : ℝ)^2) ≤ |ξ-(r : ℝ)| := by
    intro r hr
    obtain ⟨hne, hrΓ⟩ := mem_erase.mp hr
    exact (rationalMajorArc_other_outside hRp hNp hsep (hd s hs) (hd r hrΓ) hne harc).le
  have htail := fullSquareFiniteModel_outside hN (Γ.erase s) hR
    (fun r hr => hΓ r (mem_erase.mp hr).2) (fun r hr => hd r (mem_erase.mp hr).2) hout
  have he : annularWeightedSquareAverageSymbol N (fun _ => 1) (ξ : PrimeCircle)-fullSquareFiniteModel Γ N ξ =
      (annularWeightedSquareAverageSymbol N (fun _ => 1) (ξ : PrimeCircle)-
        rationalFullSquareGauss s*annularOscillatoryModel N 1 (ξ-(s : ℝ)))-
        fullSquareFiniteModel (Γ.erase s) N ξ := by rw [←hsum, hterm]; ring
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hmain htail)

theorem fullSquareCircleError_major {N : ℕ} (hN : 2 ≤ N) (Γ : Finset ℚ)
    {R ξ δ : ℝ} (hR : 1 ≤ R) (hΓ : ∀ r ∈ Γ, r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ, (r.den : ℝ) ≤ R) {s : ℚ} (hs : s ∈ Γ)
    (hsep : 2*R^3 < (N : ℝ)^2) (hcore : 2*R^4 ≤ (N : ℝ)^2)
    (harc : |ξ-(s : ℝ)| ≤ R/((s.den : ℝ)*(N : ℝ)^2))
    (hmain : ‖annularWeightedSquareAverageSymbol N (fun _ => 1) (ξ : PrimeCircle)-
      rationalFullSquareGauss s*annularOscillatoryModel N 1 (ξ-(s : ℝ))‖ ≤ δ) :
    ‖fullSquareCircleError Γ N (by omega) (ξ : PrimeCircle)‖ ≤ δ+5*fullSquareRealTailBudget R := by
  classical
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hξrange := majorArc_representative_range hNp hR hsep (hΓ s hs) harc
  have hzero : (0 : ℤ) ∈ fivePeriodShifts := by decide
  have hsum : fullSquareFiniteModel Γ N ξ+
      (∑ k ∈ fivePeriodShifts.erase 0, fullSquareFiniteModel Γ N (ξ+(k : ℝ))) =
      varyingIndexAnnularBlock Γ N (by omega) 1 rationalFullSquareGauss (ξ : PrimeCircle) := by
    rw [fullSquareCircleModel_five Γ N (by omega) hΓ hξrange]
    simpa only [Int.cast_zero, add_zero] using
      add_sum_erase fivePeriodShifts (fun k : ℤ => fullSquareFiniteModel Γ N (ξ+(k : ℝ))) hzero
  have htail : ‖∑ k ∈ fivePeriodShifts.erase 0, fullSquareFiniteModel Γ N (ξ+(k : ℝ))‖ ≤
      4*fullSquareRealTailBudget R := by
    calc
      _ ≤ ∑ k ∈ fivePeriodShifts.erase 0, ‖fullSquareFiniteModel Γ N (ξ+(k : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ fivePeriodShifts.erase 0, fullSquareRealTailBudget R := by
        apply sum_le_sum
        intro k hk
        have hk0 : k ≠ 0 := (mem_erase.mp hk).1
        exact fullSquareFiniteModel_outside hN Γ hR hΓ hd (fun r hr =>
          (canonicalLift_other_outside hNp hR hsep (hΓ s hs) (hΓ r hr) (hd s hs) (hd r hr)
            harc (Or.inr hk0)).le)
      _ = _ := by
        have hc : (fivePeriodShifts.erase 0).card = 4 := by decide
        simp only [sum_const, nsmul_eq_mul, hc, Nat.cast_ofNat]
  have hfinite := fullSquareFiniteError_major hN Γ hR hΓ hd hs hsep hcore harc hmain
  change ‖annularWeightedSquareAverageSymbol N (fun _ => 1) (ξ : PrimeCircle)-
      varyingIndexAnnularBlock Γ N (by omega) 1 rationalFullSquareGauss (ξ : PrimeCircle)‖ ≤ _
  rw [←hsum, ←sub_sub]
  exact ((norm_sub_le _ _).trans (add_le_add hfinite htail)).trans_eq (by ring)

theorem fullSquareCircleError_bound {E R : ℝ} (hE : 0 ≤ E)
    (HE : RawQuadraticWeylApproximationInput E) {M : ℕ} (hM : 1 ≤ M) (hR : 1 ≤ R)
    (hNR : 32*R ≤ ((2*M : ℕ) : ℝ))
    (hsep : 2*R^3 < ((2*M : ℕ) : ℝ)^2) (hcore : 2*R^4 ≤ ((2*M : ℕ) : ℝ)^2)
    (θ : PrimeCircle) :
    ‖fullSquareCircleError (sourceRationalCenters R) (2*M) (by omega) θ‖ ≤
      fullSquareApproxBudget E (2*M) R := by
  have hN : 2 ≤ 2*M := by omega
  have hRp : 0 < R := by linarith
  have hindex := fun r hr => (mem_sourceRationalCenters hRp.le r).mp hr
  apply circleBound_from_fundamental_interval
  intro ξ hξ
  by_cases harc : ∃ s ∈ sourceRationalCenters R, ∃ k : ℤ,
      |ξ+(k : ℝ)-(s : ℝ)| ≤ R/((s.den : ℝ)*((2*M : ℕ) : ℝ)^2)
  · obtain ⟨s, hs, k, hk⟩ := harc
    have hmain := quadratic_weyl_annular_major hE HE hM hRp.le hNR (hindex s hs).2 hk
    have h := fullSquareCircleError_major hN _ hR (fun r hr => (hindex r hr).1)
      (fun r hr => (hindex r hr).2) hs hsep hcore hk hmain
    rw [primeCircle_coe_integer_shift] at h
    have hC := quadraticIntegralConstant_one_le
    unfold fullSquareApproxBudget
    have hfirst : 0 ≤ 6*quadraticIntegralConstant/Real.sqrt R := by positivity
    have hsecond : 0 ≤ 12*E/Real.sqrt ((2*M : ℕ) : ℝ) := by positivity
    linarith
  · have hout : OutsideSourceMajorArcs (2*M) R ξ := by
      intro s hs k
      by_contra hn
      exact harc ⟨s, hs, k, (lt_of_not_ge hn).le⟩
    have hann := quadratic_weyl_annular_outside hE HE hM hRp hout
    have hcircle := fullSquareCircleModel_outside hN hR
      (show ξ ∈ Set.Icc (-1 : ℝ) 2 by constructor <;> linarith [hξ.1, hξ.2]) hout
    have h := (norm_sub_le _ _).trans (add_le_add hann hcircle)
    change ‖annularWeightedSquareAverageSymbol (2*M) (fun _ => 1) (ξ : PrimeCircle)-
      varyingIndexAnnularBlock _ (2*M) _ 1 rationalFullSquareGauss (ξ : PrimeCircle)‖ ≤ _
    unfold fullSquareApproxBudget
    have hpos : 0 ≤ 4*E*Real.sqrt R/((2*M : ℕ) : ℝ) := by positivity
    linarith

end PrimeSquares
