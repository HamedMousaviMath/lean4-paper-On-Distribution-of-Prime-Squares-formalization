import PrimeSquares.IWPageModelMaximum
import PrimeSquares.IWPrimeApproximationMaximum

set_option autoImplicit false
open scoped lp Classical
namespace PrimeSquares

noncomputable def iwPrimeLowOperator {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (Γ : Finset ℚ) (N : ℕ) (hN : 1≤N) (a : ℝ) (ha : 2≤a)
    (E₀ : Option PageZeroDatum) (Q : ℝ) : ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ) :=
  integerMultiplier (pageIWLowSymbol Γ N hN a ha E₀ (sourcePageDatum D N Q))

noncomputable def iwPrimeHighOperator {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (Γ : Finset ℚ) (N : ℕ) (hN : 1≤N) (a : ℝ) (ha : 2≤a)
    (E₀ : Option PageZeroDatum) (Q : ℝ) : ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ) :=
  annularWeightedSquareAverage (P := 2) (by norm_num) N ArithmeticFunction.vonMangoldt-
    iwPrimeLowOperator D Γ N hN a ha E₀ Q

theorem iwPrime_decomposition {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (Γ : Finset ℚ) (N : ℕ) (hN : 1≤N) (a : ℝ) (ha : 2≤a)
    (E₀ : Option PageZeroDatum) (Q : ℝ) :
    annularWeightedSquareAverage (P := 2) (by norm_num) N ArithmeticFunction.vonMangoldt=
      iwPrimeLowOperator D Γ N hN a ha E₀ Q+iwPrimeHighOperator D Γ N hN a ha E₀ Q := by
  unfold iwPrimeHighOperator
  abel

theorem iwPrimeHigh_error_model {c : ℝ} (D : PagePrimeSquareDistributionInputs c)
    (Γ : Finset ℚ) (N : ℕ) (hN : 1≤N) (a : ℝ) (ha : 2≤a)
    (E₀ : Option PageZeroDatum) (Q : ℝ) :
    iwPrimeHighOperator D Γ N hN a ha E₀ Q=selectedPrimeError D N hN Q+
      integerMultiplier
        (circleMajorArcModel (sourceRationalCenters (sourceMajorArcScale N Q)) N hN
          (sourceInducedCharacter (optionPageConductor 1 (sourcePageDatum D N Q))
            (optionPageCharacter 1 (sourcePageDatum D N Q)))
          (sourceExceptionalSelector (optionPageConductor 1 (sourcePageDatum D N Q))
            (sourcePageDatum D N Q).isSome) (optionPageBeta (sourcePageDatum D N Q))-
          pageIWLowSymbol Γ N hN a ha E₀ (sourcePageDatum D N Q)) := by
  unfold iwPrimeHighOperator iwPrimeLowOperator
  rw [circleModel_operator_decomposition (sourceRationalCenters (sourceMajorArcScale N Q)) N hN
    (sourceInducedCharacter (optionPageConductor 1 (sourcePageDatum D N Q))
      (optionPageCharacter 1 (sourcePageDatum D N Q)))
    (sourceExceptionalSelector (optionPageConductor 1 (sourcePageDatum D N Q))
      (sourcePageDatum D N Q).isSome) (optionPageBeta (sourcePageDatum D N Q)),integerMultiplier_sub]
  change (integerMultiplier _+selectedPrimeError D N hN Q)-integerMultiplier _=
    selectedPrimeError D N hN Q+(integerMultiplier _-integerMultiplier _)
  abel

/-- The actual von Mangoldt annular high maximum, including all prime powers,
with Q^(-1/4) rate. Independent raw analytic inputs remain explicit. -/
theorem iw_prime_high_maximum {Cb c : ℝ} (hCb : 0≤Cb) (HB : SmoothCircleBourgainInput Cb)
    (hc : 0<c) (HP : RawPageUniquenessInput c) (D : PagePrimeSquareDistributionInputs c) :
    ∃ δ K : ℝ,0<δ ∧ 0<K ∧ ∀ (C : ℝ) (hC : 2≤C) (_hCe : Real.exp 1≤C)
      (HT : RawTaoArcConstructionInput C) (r k Q M : ℕ) (hr : 2≤r) (_hk : 4≤k)
      (_hQ : 2^k≤Q) (hM : 2≤M),
      Real.exp (25*((Real.log (Q : ℝ))^2+(r : ℝ)*Real.log (iwDenominatorBound C k Q)))≤M →
      Real.log (Q : ℝ)≤δ*Real.sqrt (Real.log (M : ℝ)) →
      ∃ d : TaoArcConstructionData C (iwRho k) k Q,
        IWGood r k d.S (iwWidth C r k Q) ∧
        (∀ t∈iwFrequencySet d.S k,(t.den : ℝ)≤ iwDenominatorBound C k Q) ∧
        ∃ E₀ : Option PageZeroDatum,
          (∀ F,E₀=some F → F.conductor≤Q ∧ F.conductor∣d.period) ∧
          ∀ f : ℓ²(ℤ,ℂ),∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
            (∀ j x,‖iwPrimeHighOperator D (iwFrequencySet d.S k) ((2 : ℕ)^j*M)
              (by have h := dyadic_annular_scale_lower hM j;omega) (iwCutoffScale C r k Q)
              (by have h := iwCutoffScale_four_le hC hr k Q;linarith) E₀ Q f x‖≤g x) ∧
            ‖g‖≤K*(Q : ℝ)^(-(1/4 : ℝ))*‖f‖ := by
  obtain ⟨δ,KE,hδ,hKE,hRaw,hError⟩ := iw_prime_approximation_maximum D
  obtain ⟨KM,hKM,hModel⟩ := iw_page_model_maximum hCb HB hc HP
  refine ⟨δ,KM+KE,hδ,add_pos hKM hKE,?_⟩
  intro C hC hCe HT r k Q M hr hk hQ hM hstart hcut
  have h16 : 16≤2^k := by
    calc
      16 = 2^4 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hQ2 : (2 : ℝ)≤Q := by exact_mod_cast (show 2≤Q by omega)
  have hQ1 : (1 : ℝ)≤Q := by linarith
  have hM2 : (2 : ℝ)≤M := by exact_mod_cast hM
  obtain ⟨d,hGood,hden⟩ := quantitative_iw_construction_good hC HT hr hk hQ
  have hbudget := iw_starting_budget_of_source_scale hC hCe hr hk (show 1≤Q by omega) hM hstart
  let E := fun j => sourcePageDatum D ((2 : ℕ)^j*M) Q
  let R := fun j => sourceMajorArcScale (((2 : ℕ)^j*M : ℕ) : ℝ) Q
  have hR : ∀ j,(Q : ℝ)≤R j := fun j => sourceMajorArcScale_cutoff_le hQ1 _
  have hE : ∀ j F,E j=some F → (F.conductor : ℝ)≤R j ∧ 1-(c/2)/Real.log (R j)<F.beta := by
    intro j F hF
    have hp : (1 : ℕ)≤2^j := one_le_pow₀ (by norm_num)
    have hMN : (M : ℝ)≤(((2 : ℕ)^j*M : ℕ) : ℝ) := by
      exact_mod_cast (show M≤(2 : ℕ)^j*M by simpa only [one_mul] using Nat.mul_le_mul_right M hp)
    exact (sourcePageDatum_spec D _ Q (hRaw Q M hQ2 hM2 hcut _ hMN)).1 F hF
  obtain ⟨E₀,h₀,hselected,hmodel⟩ := hModel C hC r k Q M hr hk hQ hM d hbudget E R hR hE
  refine ⟨d,hGood,hden,E₀,?_,?_⟩
  · intro F hF
    have hs : F.conductor≤Q := by exact_mod_cast (h₀ F hF).1
    exact ⟨hs,iw_period_divisible_small d F.conductor_two hs⟩
  · intro f
    obtain ⟨gm,hgm,htm,hnm⟩ := hmodel f
    obtain ⟨ge,hge,hte,hne⟩ := hError Q hQ2 M hM hcut f
    have hQpow : (Q : ℝ)^(-(1/2 : ℝ))≤(Q : ℝ)^(-(1/4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
    have hne' : ‖ge‖≤KE*(Q : ℝ)^(-(1/4 : ℝ))*‖f‖ :=
      hne.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQpow hKE.le) (norm_nonneg _))
    refine ⟨gm+ge,fun x => add_nonneg (hgm x) (hge x),?_,?_⟩
    · intro j x
      rw [iwPrimeHigh_error_model,_root_.add_apply,lp.coeFn_add,Pi.add_apply]
      change _≤gm x+ge x
      exact (norm_add_le _ _).trans ((add_le_add (hte j x) (htm j x)).trans_eq (add_comm _ _))
    · exact ((norm_add_le gm ge).trans (add_le_add hnm hne')).trans_eq (by ring)

end PrimeSquares
