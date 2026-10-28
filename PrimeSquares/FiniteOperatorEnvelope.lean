import PrimeSquares.CircleMultipliers

open Finset
open scoped lp
namespace PrimeSquares

noncomputable def magnitudeL2 (f : ℓ²(ℤ, ℂ)) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨fun x => ‖f x‖, f.2.norm⟩

theorem magnitudeL2_norm (f : ℓ²(ℤ, ℂ)) : ‖magnitudeL2 f‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
  simp [magnitudeL2]

noncomputable def finiteOperatorEnvelope {ι : Type*} (S : Finset ι)
    (T : ι → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ)) (f : ℓ²(ℤ, ℂ)) : lp (fun _ : ℤ => ℝ) 2 :=
  ∑ i ∈ S, magnitudeL2 (T i f)

theorem finiteOperatorEnvelope_nonneg {ι : Type*} (S : Finset ι)
    (T : ι → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ)) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    0 ≤ finiteOperatorEnvelope S T f x := by
  change 0 ≤ (∑ i ∈ S, magnitudeL2 (T i f)) x
  rw [lp.coeFn_sum,Finset.sum_apply]
  exact sum_nonneg (fun i _ => norm_nonneg (T i f x))

theorem finiteOperatorEnvelope_dominates {ι : Type*} (S : Finset ι)
    (T : ι → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ)) (f : ℓ²(ℤ, ℂ)) {i : ι} (hi : i ∈ S) (x : ℤ) :
    ‖T i f x‖ ≤ finiteOperatorEnvelope S T f x := by
  change ‖T i f x‖ ≤ (∑ j ∈ S, magnitudeL2 (T j f)) x
  rw [lp.coeFn_sum,Finset.sum_apply]
  exact single_le_sum (fun j _ => norm_nonneg (T j f x)) hi

end PrimeSquares
