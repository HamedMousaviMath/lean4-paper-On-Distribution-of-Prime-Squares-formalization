import PrimeSquares.WeightedAnnularBlockBounds
import PrimeSquares.InitialScaleMaximalCompletion

open Finset
open scoped lp
namespace PrimeSquares

theorem annularLargeStart_budgets {M : ℕ} (hM : 2 ≤ M) (s : ℕ) :
    (16 : ℝ)^s ≤ ((((2 : ℕ)^(2*s+3)*M : ℕ) : ℝ)^2) ∧
      16*((2 : ℝ)^(s+1))^2 ≤ ((((2 : ℕ)^(2*s+3)*M : ℕ) : ℝ)^2) := by
  have hS : (2 : ℕ)^(4*s+6) ≤ ((2 : ℕ)^(2*s+3)*M)^2 := by
    calc
      _ = ((2 : ℕ)^(2*s+3))^2 := by rw [←pow_mul];congr 1;omega
      _ ≤ _ := pow_le_pow_left₀ (Nat.zero_le _) (by
        have hp : 0 < (2 : ℕ)^(2*s+3) := by positivity
        nlinarith) 2
  constructor
  · have h : (16 : ℕ)^s ≤ ((2 : ℕ)^(2*s+3)*M)^2 := by
      rw [show (16 : ℕ)=2^4 by norm_num,←pow_mul]
      exact (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (by omega : 4*s ≤ 4*s+6)).trans hS
    exact_mod_cast h
  · have he : (16 : ℕ)*((2 : ℕ)^(s+1))^2=(2 : ℕ)^(2*s+6) := by
      rw [show (16 : ℕ)=2^4 by norm_num,←pow_mul,←pow_add]
      congr 1;omega
    have h : (16 : ℕ)*((2 : ℕ)^(s+1))^2 ≤ ((2 : ℕ)^(2*s+3)*M)^2 := by
      rw [he]
      exact (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (by omega : 2*s+6 ≤ 4*s+6)).trans hS
    exact_mod_cast h

theorem weightedAnnular_allStartingScales {C : ℝ} (hC : 0 ≤ C)
    (hB : SmoothCircleBourgainInput C)
    {M s : ℕ} (hM : 2 ≤ M) (hs : 2 ≤ s) (Γ : Finset ℚ)
    (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (c : ℚ → ℂ) {A : ℝ} (hA : 0 ≤ A) (hb : ∀ r ∈ Γ,‖c r‖ ≤ A)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier (weightedAnnularSourceBlock Γ ((2 : ℕ)^j*M)
        (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (A*((3/2 : ℝ)*(2*(s : ℝ)+3)+(1/2)*C*circleFrequencyLogFactor Γ+
        annularProjectionErrorL2Constant))*‖f‖ := by
  let n : ℕ := 2*s+3
  let M' : ℕ := (2 : ℕ)^n*M
  have hM' : 2 ≤ M' := dyadic_annular_scale_lower hM n
  obtain ⟨hw,hscl⟩ := annularLargeStart_budgets hM s
  obtain ⟨u,hu,ht,hn⟩ := largeStart_weightedAnnular_maximum hC hB hM' hs Γ hc hd hw hscl
    (fun j => β (n+j)) (fun j => hβ0 (n+j)) (fun j => hβ1 (n+j)) c hA hb f
  let T := fun j => integerMultiplier (weightedAnnularSourceBlock Γ ((2 : ℕ)^j*M)
    (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) c)
  have hT : ∀ j ∈ range n,‖T j‖ ≤ (3/2 : ℝ)*A := by
    intro j _
    exact weightedAnnularSourceBlock_operator_bound (dyadic_annular_scale_lower hM j)
      hs Γ hc hd (hβ1 j) c hA hb
  have htail : ∀ j x,‖T (n+j) f x‖ ≤ u x := by
    intro j x
    dsimp [T]
    simpa only [M',←dyadic_annular_scale_shift] using ht j x
  obtain ⟨g,hg,htg,hng⟩ := initialScale_maximal_completion T n hT f u hu htail hn
  refine ⟨g,hg,htg,?_⟩
  exact hng.trans_eq (by dsimp [n];push_cast;ring)

end PrimeSquares
