import PrimeSquares.RationalCollarBlockEnergy

open Finset
namespace PrimeSquares

noncomputable def rationalCollarBlock (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (Q : ℝ)
    (β : ℚ → ℝ) (c : ℚ → ℂ) : C(PrimeCircle,ℂ) :=
  ∑ r ∈ Γ,c r • circleAnnularCollar N hN (β r) (r.den : ℝ) Q (Nat.log2 r.den) (r : ℝ)

theorem rationalCollarBlock_real_window (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N) (Q : ℝ)
    (β : ℚ → ℝ) (c : ℚ → ℂ) (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    {ξ : ℝ} (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) :
    rationalCollarBlock Γ N hN Q β c (ξ : PrimeCircle)=
      (∑ r ∈ Γ,c r*annularCollarSymbol N hN (β r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ-1-(r : ℝ)))+
      (∑ r ∈ Γ,c r*annularCollarSymbol N hN (β r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ-(r : ℝ)))+
      (∑ r ∈ Γ,c r*annularCollarSymbol N hN (β r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ+1-(r : ℝ))) := by
  classical
  simp only [rationalCollarBlock,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  calc
    _ = ∑ r ∈ Γ,(c r*annularCollarSymbol N hN (β r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ-1-(r : ℝ))+
        c r*annularCollarSymbol N hN (β r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ-(r : ℝ))+
        c r*annularCollarSymbol N hN (β r) (r.den : ℝ) Q (Nat.log2 r.den) (ξ+1-(r : ℝ))) := by
      apply sum_congr rfl
      intro r hr
      have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast (hΓ r hr).1
      have hr1 : (r : ℝ) < 1 := by exact_mod_cast (hΓ r hr).2
      rw [circleAnnularCollar_window N hN (β r) (r.den : ℝ) Q (Nat.log2 r.den) (r : ℝ) ξ ⟨by linarith [hξ.1],by linarith [hξ.2]⟩]
      have h1 : ξ-(r : ℝ)-1=ξ-1-(r : ℝ) := by ring
      have h3 : ξ-(r : ℝ)+1=ξ+1-(r : ℝ) := by ring
      simp only [compactPeriodWindow,h1,h3,mul_add]
    _ = _ := by rw [sum_add_distrib,sum_add_distrib]

end PrimeSquares
