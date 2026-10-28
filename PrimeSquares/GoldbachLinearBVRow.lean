import PrimeSquares.GoldbachLinearSourceIntegral

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachLinearMajorModel (N ℓ k q a : ℕ) [NeZero q]
    (A : ℤ) (W γ : ℝ) : ℂ :=
  (upsilon q k (a:ℤ) (-((A:ZMod q)*(ℓ:ZMod q)))/(k.totient:ℂ))*
    goldbachLinearSourceIntegral N ℓ W γ

noncomputable def goldbachLinearMajorError (N ℓ k q a : ℕ) [NeZero q]
    (A : ℤ) (W γ : ℝ) : ℂ :=
  goldbachProgressionPolynomial N ℓ k a W (((A:ℝ)/q+γ:ℝ):PrimeCircle)-
    goldbachLinearMajorModel N ℓ k q a A W γ

theorem goldbach_linear_error_sum_unweighted (N ℓ q : ℕ) [NeZero q]
    (hN : 1≤N) (hℓ : 0<ℓ) (K : Finset ℕ) (hK : ∀ k∈K,0<k)
    (a : ℕ→ℕ) (ha : ∀ k∈K,(a k).Coprime k)
    (W : ℕ→ℝ) {R H : ℝ} (hW : ∀ k∈K,2≤W k) (hX : 2≤(N:ℝ)^2/ℓ) (hR : 1≤R) (hqR : (q:ℝ)≤R)
    (hH : 0≤H) (hlevel : ∀ k∈K,(k.lcm q:ℝ)≤H) (E : ℕ→ℝ) (hE : ∀ h,0≤E h)
    (hcounts : ∀ h b : ℕ,0<h → (h:ℝ)≤H → b.Coprime h → ∀ y∈Set.Icc 2 ((N:ℝ)^2/ℓ),
      ‖(goldbachPrimeProgressionCount h b y:ℂ)-goldbachPrimeProgressionModel h y‖≤E h)
    (A : ℤ) (γ : ℝ) (hγ : |γ|≤R/(N:ℝ)^2) :
    (∑ k∈K,‖goldbachLinearMajorError N ℓ k q (a k) A (W k) γ‖)≤
      (1+(q:ℝ))*(K.card:ℝ)+(1+2*Real.pi)*R^3*(∑ h∈Icc 1 ⌊H⌋₊,E h) := by
  classical
  have hmap : ∀ k∈K,k.lcm q∈Icc 1 ⌊H⌋₊ := by
    intro k hk
    have hh : 0<k.lcm q := Nat.lcm_pos (hK k hk) (NeZero.pos q)
    exact mem_Icc.mpr ⟨hh,(Nat.le_floor_iff hH).mpr (hlevel k hk)⟩
  have herr : ∀ k∈K,‖goldbachLinearMajorError N ℓ k q (a k) A (W k) γ‖≤
      1+(q:ℝ)+(1+2*Real.pi)*R^2*E (k.lcm q) := by
    intro k hk
    let : NeZero k := ⟨by have hp:=hK k hk;omega⟩
    apply goldbach_linear_source_major_numeric N k q (a k) ℓ hN hℓ (ha k hk)
      (hW k hk) hX (hE _) hR hqR A γ hγ
    intro b hb y hy
    exact hcounts (k.lcm q) b (Nat.lcm_pos (hK k hk) (NeZero.pos q)) (hlevel k hk)
      ((mem_goldbachMajorResidues k q (a k) b).mp hb).2.2 y hy
  have hsum : 0≤∑ h∈Icc 1 ⌊H⌋₊,E h := sum_nonneg (fun h _ => hE h)
  have hc : 0≤(1+2*Real.pi)*R^2 := by positivity
  calc
    _≤∑ k∈K,(1+(q:ℝ)+(1+2*Real.pi)*R^2*E (k.lcm q)) := sum_le_sum herr
    _=(1+(q:ℝ))*(K.card:ℝ)+(1+2*Real.pi)*R^2*(∑ k∈K,E (k.lcm q)) := by
      rw [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum]
      ring
    _≤(1+(q:ℝ))*(K.card:ℝ)+(1+2*Real.pi)*R^2*((q:ℝ)*(∑ h∈Icc 1 ⌊H⌋₊,E h)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (goldbach_lcm_unweighted_sum K q ⌊H⌋₊ E hmap (fun h _ => hE h)) hc)
    _≤(1+(q:ℝ))*(K.card:ℝ)+(1+2*Real.pi)*R^2*(R*(∑ h∈Icc 1 ⌊H⌋₊,E h)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqR hsum) hc)
    _=(1+(q:ℝ))*(K.card:ℝ)+(1+2*Real.pi)*R^3*(∑ h∈Icc 1 ⌊H⌋₊,E h) := by ring

/-- Actual BV row approximation. The level and constants are chosen before
the major denominator, prime cutoffs, residues and coefficients. -/
theorem goldbach_linear_major_bv_row (HBV : RawPrimeBombieriVinogradovInput)
    {T : ℝ} (hT : 0<T) :
    ∃ L M X₀ : ℝ,0≤L ∧ 0<M ∧ 4≤X₀ ∧
      ∀ (q : ℕ) [NeZero q] (N ℓ : ℕ),1≤N → 0<ℓ → X₀≤(N:ℝ)^2/ℓ →
      ∀ (K : Finset ℕ), (∀ k∈K,0<k) →
      ∀ (a : ℕ→ℕ),(∀ k∈K,(a k).Coprime k) →
      ∀ W : ℕ→ℝ,(∀ k∈K,2≤W k) →
      ∀ R : ℝ,1≤R → (q:ℝ)≤R →
      (∀ k∈K,(k.lcm q:ℝ)≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log ((N:ℝ)^2/ℓ))^(-L)) →
      ∀ (A : ℤ) (γ : ℝ),|γ|≤R/(N:ℝ)^2 →
      (∑ k∈K,‖goldbachLinearMajorError N ℓ k q (a k) A (W k) γ‖)≤
        (1+(q:ℝ))*(K.card:ℝ)+(1+2*Real.pi)*R^3*
          (M*((N:ℝ)^2/ℓ)*(Real.log ((N:ℝ)^2/ℓ))^(-T)) := by
  obtain ⟨L,M,X₀,hL,hM,hX₀,hBV⟩ := HBV T hT
  refine ⟨L,M,X₀,hL,hM,hX₀,?_⟩
  intro q _ N ℓ hN hℓ hX K hK a ha W hW R hR hqR hlevel A γ hγ
  obtain ⟨E,hE,hcounts,hBVsum⟩ := hBV ((N:ℝ)^2/ℓ) hX
  have hh : 0≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log ((N:ℝ)^2/ℓ))^(-L) := by
    have hl : 0≤Real.log ((N:ℝ)^2/ℓ) := Real.log_nonneg (by linarith)
    positivity
  have he := goldbach_linear_error_sum_unweighted N ℓ q hN hℓ K hK a ha W hW
    (by linarith) hR hqR hh hlevel E hE
    (fun h b hp hb hc y hy => hcounts h b hp hb hc y hy.1 hy.2) A γ hγ
  exact he.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hBVsum (by positivity)))

end PrimeSquares
