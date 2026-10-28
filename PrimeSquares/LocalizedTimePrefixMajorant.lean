import PrimeSquares.LocalizedIntervalEnergy
import PrimeSquares.TimePrefixRademacherMenshov
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem localized_time_prefix_majorant (h a : ℕ) (m : ℕ → ℕ → C(PrimeCircle,ℂ))
    (p : ℕ → C(PrimeCircle,ℂ)) (hp : ∀ i j,i ≠ j → ∀ θ,p i θ=0 ∨ p j θ=0)
    (f : ℓ²(ℤ,ℂ)) (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2)
    {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ t k b x,‖integerMultiplier (intervalCircleSymbol b (2^k) (m t)) f x‖ ≤ G k b x)
    (hI : ∀ k b,‖G k b‖^2 ≤ B^2*‖integerMultiplier (intervalCircleSymbol b (2^k) p) f‖^2) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ t K,K ≤ 2^h → ∀ x,‖integerMultiplier (intervalCircleSymbol a K (m t)) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (h+1 : ℝ)*B*Real.sqrt (intervalRealBudget a (2^h)
        (fun i => ‖integerMultiplier (p i) f‖^2)) := by
  obtain ⟨g,hg,ht,hn⟩ := time_prefix_rademacherMenshov h a
    (fun t i x => integerMultiplier (m t i) f x) G
    (fun i => ‖integerMultiplier (p i) f‖^2) (fun i => sq_nonneg _) hB
    (fun t k b x => by
      rw [←intervalL2Sum_apply,←integerMultiplier_interval]
      exact hG t k b x)
    (fun k b => by simpa only [localized_interval_input_energy b (2^k) p hp f] using hI k b)
  refine ⟨g,hg,?_,hn⟩
  intro t K hK x
  rw [integerMultiplier_interval,intervalL2Sum_apply]
  exact ht t K hK x
end PrimeSquares
