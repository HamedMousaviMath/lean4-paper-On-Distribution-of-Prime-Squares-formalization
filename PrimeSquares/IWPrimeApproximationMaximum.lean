import PrimeSquares.SelectedPrimeErrorBounds
import PrimeSquares.SelectedPrimeHighBounds
import PrimeSquares.DecayingMaximalTail
import PrimeSquares.DyadicLogarithmicBudget

set_option autoImplicit false
open scoped lp
namespace PrimeSquares

/-- The approximation maximum is obtained from the already proved raw-data
approximation theorem; the paper's IW or restricted estimates are not inputs. -/
theorem iw_prime_approximation_maximum {c : ℝ} (D : PagePrimeSquareDistributionInputs c) :
    ∃ δ K : ℝ,0<δ ∧ 0<K ∧
      (∀ Q X : ℝ,2≤Q → 2≤X → Real.log Q≤δ*Real.sqrt (Real.log X) →
        ∀ N : ℕ,X≤(N : ℝ) → SourcePageRawAdmissible D N Q) ∧
      ∀ Q : ℝ,2≤Q → ∀ (M : ℕ) (hM : 2≤M),
        Real.log Q≤δ*Real.sqrt (Real.log (M : ℝ)) → ∀ f : ℓ²(ℤ,ℂ),
        ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
          (∀ j x,‖selectedPrimeError D ((2 : ℕ)^j*M)
            (by have h := dyadic_annular_scale_lower hM j;omega) Q f x‖≤g x) ∧
          ‖g‖≤K*Q^(-(1/2 : ℝ))*‖f‖ := by
  obtain ⟨δE,hδE,hError⟩ := selectedPrimeError_all_exponents D
  obtain ⟨δR,hδR,hRaw⟩ := selectedPage_raw_source_range D
  obtain ⟨KE,hKE,hErr⟩ := hError 2 (by norm_num)
  let δ := min δE δR
  let K := 2*KE*(Real.log 2)^(-(2 : ℝ))
  have hlog2 : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hK : 0<K := by dsimp [K];positivity
  have hδ : 0<δ := lt_min hδE hδR
  have hRaw' : ∀ Q X : ℝ,2≤Q → 2≤X → Real.log Q≤δ*Real.sqrt (Real.log X) →
      ∀ N : ℕ,X≤(N : ℝ) → SourcePageRawAdmissible D N Q := by
    intro Q X hQ hX hcut N hN
    exact hRaw Q X hQ hX (hcut.trans
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _))) N hN
  refine ⟨δ,K,hδ,hK,hRaw',?_⟩
  intro Q hQ M hM hcut f
  let T := fun j => selectedPrimeError D ((2 : ℕ)^j*M)
    (by have h := dyadic_annular_scale_lower hM j;omega) Q
  let B := KE*Q^(-(1/2 : ℝ))*(Real.log 2)^(-(2 : ℝ))
  have hB : 0≤B := by dsimp [B];positivity
  have hdecay (j : ℕ) : ‖T j‖≤B*((j : ℝ)+1)^(-(2 : ℝ)) := by
    have hM1 : (1 : ℝ)≤M := by exact_mod_cast (show 1≤M by omega)
    have hM2 : (2 : ℝ)≤M := by exact_mod_cast hM
    have hp : (1 : ℕ)≤2^j := one_le_pow₀ (by norm_num)
    have hMN : (M : ℝ)≤(((2 : ℕ)^j*M : ℕ) : ℝ) := by
      exact_mod_cast (show M≤(2 : ℕ)^j*M by simpa only [one_mul] using Nat.mul_le_mul_right M hp)
    have hlogM := Real.sqrt_le_sqrt (Real.log_le_log (by linarith : (0 : ℝ)<M) hMN)
    have hcutN : Real.log Q≤δE*Real.sqrt (Real.log (((2 : ℕ)^j*M : ℕ) : ℝ)) :=
      (hcut.trans (mul_le_mul_of_nonneg_left hlogM hδ.le)).trans
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
    have hraw := hRaw' Q M hQ hM2 hcut ((2 : ℕ)^j*M) hMN
    have h := hErr ((2 : ℕ)^j*M) (dyadic_annular_scale_lower hM j) Q hQ hcutN hraw
      (by have h := dyadic_annular_scale_lower hM j;omega)
    have hNmono : (((2 : ℕ)^j : ℕ) : ℝ)≤(((2 : ℕ)^j*M : ℕ) : ℝ) := by
      exact_mod_cast (show (2 : ℕ)^j≤(2 : ℕ)^j*M by
        simpa only [mul_one] using Nat.mul_le_mul_left ((2 : ℕ)^j) (show 1≤M by omega))
    have hlog : 1+Real.log (((2 : ℕ)^j : ℕ) : ℝ)≤1+Real.log (((2 : ℕ)^j*M : ℕ) : ℝ) := by
      have hl := Real.log_le_log (by positivity : (0 : ℝ)<(((2 : ℕ)^j : ℕ) : ℝ)) hNmono
      linarith
    have hpos : 0<1+Real.log (((2 : ℕ)^j : ℕ) : ℝ) := by
      have h1 : (1 : ℝ)≤(((2 : ℕ)^j : ℕ) : ℝ) := by exact_mod_cast hp
      linarith [Real.log_nonneg h1]
    have hb := (Real.rpow_le_rpow_of_nonpos hpos hlog (by norm_num : -(2 : ℝ)≤0)).trans
      (dyadic_log_inverse_power (by norm_num : (0 : ℝ)≤2) j)
    exact h.trans (by
      dsimp [B]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb
        (show 0≤KE*Q^(-(1/2 : ℝ)) by positivity))
  obtain ⟨g,hg,ht,hn⟩ := decaying_operator_maximal_tail_majorant hB (by norm_num : (2 : ℝ)≤2)
    0 T (by simpa only [zero_add] using hdecay) f
  refine ⟨g,hg,by simpa only [zero_add] using ht,?_⟩
  exact hn.trans_eq (by simp only [Nat.cast_zero,zero_add,Real.one_rpow,mul_one];dsimp [B,K];ring)

end PrimeSquares
