import PrimeSquares.LocalizedTimePrefixMajorant
import PrimeSquares.CircleEnergyMaximalWitness
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem localized_circle_square_maximum (m : ℕ → C(PrimeCircle,ℂ)) (p : C(PrimeCircle,ℂ))
    (hm : ∀ t,m t=m t*p) {B : ℝ} (hB : 0 ≤ B)
    (hE : ∀ J : Finset ℕ,∀ θ : PrimeCircle,(∑ t ∈ J,‖m t θ‖^2) ≤ B^2) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ t x,‖integerMultiplier (m t) f x‖ ≤ g x) ∧
      ‖g‖ ≤ B*‖integerMultiplier p f‖ := by
  obtain ⟨g,_,hg,ht,hn⟩ := circle_energy_maximal_witness m hB hE (integerMultiplier p f)
  refine ⟨g,hg,?_,hn⟩
  intro t x
  rw [integerMultiplier_localized (m t) p (hm t) f]
  exact ht t x
end PrimeSquares
