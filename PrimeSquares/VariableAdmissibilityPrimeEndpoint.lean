import PrimeSquares.VariableAdmissibilityPairings
import PrimeSquares.PrimeStoppingLocalEndpoint

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem primeStopping_local_endpoint_with_constant {c δ CS cstar B₀ : ℝ}
    (D : PagePrimeSquareDistributionInputs c) (H419 : Proposition419Bounds D δ) (hδ : 0 < δ)
    (hCS : 1 ≤ CS) (hB₀ : 1 ≤ B₀) (HS : OrdinarySquareStoppingInput CS) (hstar : 4*Real.sqrt 3/9 < cstar) :
    ∃ K : ℝ, 0 < K ∧ ∀ (I : SparseIntegerInterval) (F G H : Finset ℤ) (τ : ℤ → ℕ),
      F ⊆ I.five.points → H ⊆ I.five.points → G ⊆ I.points → G ⊆ H →
      F.Nonempty → H.Nonempty →
      (∀ x ∈ G, ((2 : ℕ)^(τ x)*2)^2 ≤ I.length) →
      (∀ x ∈ G, sourceLocalMass ((2 : ℕ)^(τ x)*2) (finiteIndicatorLp F 1) x ≤
        B₀*((F.card : ℝ)/I.length)) →
      ‖∑ x ∈ G, annularDyadicValue (τ x) F x‖/(5*(I.length : ℝ)) ≤
        K*(finiteSetDensity (5*(I.length : ℝ)) F H)^(2/3 : ℝ)*
          paperPhi cstar (1/2) (finiteSetDensity (5*(I.length : ℝ)) F H) := by
  have hcstar : 0 < cstar := (by positivity : (0 : ℝ) < 4*Real.sqrt 3/9).trans hstar
  obtain ⟨c₁, hc₁, hcoeff⟩ := exists_primeSquare_high_coefficient hstar
  obtain ⟨B, CB, hB, hCB, hbalance⟩ := exists_localPrime_balance (by linarith) hcoeff
  obtain ⟨C₀, hC₀, hstart⟩ := primeStoppingStart_bounds hδ hB
  obtain ⟨KS, hKS, hSquare⟩ := ordinaryStopping_endpoint_with_constant hCS hB₀ HS
  obtain ⟨KL, hKL, hLarge⟩ := primeLargeStopping_pairing_with_constant D H419 hδ hc₁ hB₀
  obtain ⟨CP, hCP, hPower⟩ := paperLog_rpow_le_paperPhi (by norm_num : (0 : ℝ) < 1/2)
    hcstar (10/3)
  let KSmall := C₀*KS*CP
  let K := KSmall+KL*CB
  have hKSmall : 0 < KSmall := by dsimp [KSmall]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro I F G H τ hF hH hG hGH hFn hHn hscale hadm
  let L := 5*(I.length : ℝ)
  let d := finiteSetDensity L F H
  have hI : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨hd, hd1⟩ := finiteSetDensity_five_bounds I F H hF hH hFn hHn
  obtain ⟨k, hQ, hQlog, hscalar⟩ := hbalance d hd hd1
  let Q := (2 : ℝ)^k
  let N₀ := primeStoppingStart δ Q
  obtain ⟨hN₀, hcut, hlogN₀⟩ := hstart (paperLog d) Q (paperLog_two_le d) hQ hQlog
  let Gs := G.filter (fun x => (((2 : ℕ)^(τ x)*2 : ℕ) : ℝ) ≤ N₀)
  let Gl := G.filter (fun x => ¬ (((2 : ℕ)^(τ x)*2 : ℕ) : ℝ) ≤ N₀)
  have hGs : Gs ⊆ G := filter_subset _ _
  have hGl : Gl ⊆ G := filter_subset _ _
  have hSmallSquare := hSquare I F Gs H τ hF hH (hGs.trans hG) (hGs.trans hGH) hFn hHn
    (fun x hx => hscale x (hGs hx)) (fun x hx => hadm x (hGs hx))
  have hSmallDom := primeSmallStopping_square_domination F Gs τ N₀
    (fun x hx => (mem_filter.mp hx).2)
  have hlogN₀0 : 0 ≤ Real.log N₀ := Real.log_nonneg (by linarith)
  have hpLog := paperLog_pos d
  have hdPow : 0 ≤ d^(2/3 : ℝ) := Real.rpow_nonneg hd.le _
  have hSmall : ‖∑ x ∈ Gs, annularDyadicValue (τ x) F x‖/L ≤
      KSmall*d^(2/3 : ℝ)*paperPhi cstar (1/2) d := by
    calc
      _ ≤ Real.log N₀ * (‖∑ x ∈ Gs, ordinaryDyadicValue (τ x) F x‖/L) := by
        simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hSmallDom hL.le
      _ ≤ (C₀*(paperLog d)^2) * (KS*d^(2/3 : ℝ)*(paperLog d)^(4/3 : ℝ)) :=
        mul_le_mul hlogN₀ hSmallSquare (div_nonneg (norm_nonneg _) hL.le)
          (mul_nonneg hC₀.le (sq_nonneg _))
      _ = C₀*KS*d^(2/3 : ℝ)*(paperLog d)^(10/3 : ℝ) := by
        rw [show (10/3 : ℝ)=2+4/3 by norm_num, Real.rpow_add hpLog, Real.rpow_two]
        ring
      _ ≤ C₀*KS*d^(2/3 : ℝ)*(CP*paperPhi cstar (1/2) d) :=
        mul_le_mul_of_nonneg_left (hPower d) (by positivity)
      _ = _ := by dsimp [KSmall]; ring
  have hLargePrime := hLarge I F Gl H τ k N₀ (hGl.trans hGH) hQ hN₀ hcut
    (fun x hx => (lt_of_not_ge (mem_filter.mp hx).2).le) (fun x hx => hadm x (hGl hx))
  have hBig : ‖∑ x ∈ Gl, annularDyadicValue (τ x) F x‖/L ≤
      (KL*CB)*d^(2/3 : ℝ)*paperPhi cstar (1/2) d :=
    hLargePrime.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscalar hKL.le)
  have hsplit : (∑ x ∈ G, annularDyadicValue (τ x) F x) =
      (∑ x ∈ Gs, annularDyadicValue (τ x) F x) + ∑ x ∈ Gl, annularDyadicValue (τ x) F x := by
    exact (sum_filter_add_sum_filter_not G _ _).symm
  calc
    _ ≤ (‖∑ x ∈ Gs, annularDyadicValue (τ x) F x‖ +
        ‖∑ x ∈ Gl, annularDyadicValue (τ x) F x‖)/L := by
      rw [hsplit]
      exact div_le_div_of_nonneg_right (norm_add_le _ _) hL.le
    _ = ‖∑ x ∈ Gs, annularDyadicValue (τ x) F x‖/L +
        ‖∑ x ∈ Gl, annularDyadicValue (τ x) F x‖/L := add_div _ _ _
    _ ≤ KSmall*d^(2/3 : ℝ)*paperPhi cstar (1/2) d +
        (KL*CB)*d^(2/3 : ℝ)*paperPhi cstar (1/2) d := add_le_add hSmall hBig
    _ = _ := by dsimp [K]; ring


end PrimeSquares
