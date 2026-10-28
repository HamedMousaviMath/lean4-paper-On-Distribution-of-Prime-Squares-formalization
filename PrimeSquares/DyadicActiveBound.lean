import PrimeSquares.HighBroadSupport
import PrimeSquares.CanonicalRationalCenters

open Finset
namespace PrimeSquares

theorem dyadicActive_card (Γ : Finset ℚ) (ξ : ℝ) (s : ℕ)
    (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) (hlog : ∀ r ∈ Γ,Nat.log2 r.den=s) :
    (activeRationalCenters Γ ξ).card ≤ 4 := by
  classical
  by_cases hs : 2 ≤ s
  · have hc : (activeRationalCenters Γ ξ).card ≤ 1 := by
      apply card_le_one.mpr
      intro r hr t ht
      obtain ⟨hrΓ,har⟩ := mem_filter.mp hr
      obtain ⟨htΓ,hat⟩ := mem_filter.mp ht
      have hrd : (r.den : ℝ) ≤ (2 : ℝ)^(s+1) := by
        have hn : r.den ≤ (2 : ℕ)^(s+1) := by simpa only [hlog r hrΓ] using (Nat.lt_log2_self (n := r.den)).le
        exact_mod_cast hn
      have htd : (t.den : ℝ) ≤ (2 : ℝ)^(s+1) := by
        have hn : t.den ≤ (2 : ℕ)^(s+1) := by simpa only [hlog t htΓ] using (Nat.lt_log2_self (n := t.den)).le
        exact_mod_cast hn
      rw [hlog r hrΓ] at har
      rw [hlog t htΓ] at hat
      exact sourceArcCutoffScale_unique hs hrd htd har hat
    omega
  · have hsub : activeRationalCenters Γ ξ ⊆
        (activeRationalCenters Γ ξ).filter (fun r => ¬2 ≤ Nat.log2 r.den) := by
      intro r hr
      refine mem_filter.mpr ⟨hr,?_⟩
      rw [hlog r (mem_filter.mp hr).1]
      exact hs
    exact (card_le_card hsub).trans (activeRationalCenters_small_card Γ ξ hΓ)

end PrimeSquares
