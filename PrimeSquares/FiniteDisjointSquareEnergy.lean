import PrimeSquares.L2SquareEnergy

open Finset
namespace PrimeSquares

theorem norm_sum_square_single_support {ι : Type*} (S : Finset ι) (f : ι → ℂ)
    (hs : ∀ i ∈ S,∀ j ∈ S,f i ≠ 0 → f j ≠ 0 → i=j) :
    ‖∑ i ∈ S,f i‖^2=∑ i ∈ S,‖f i‖^2 := by
  classical
  by_cases h : ∃ i ∈ S,f i ≠ 0
  · obtain ⟨i,hi,hfi⟩ := h
    have hz : ∀ j ∈ S,j ≠ i → f j=0 := by
      intro j hj hji
      by_contra hfj
      exact hji (hs j hj i hi hfj hfi)
    have he : (∑ j ∈ S,f j)=f i := sum_eq_single i hz (fun hn => False.elim (hn hi))
    have he' : (∑ j ∈ S,‖f j‖^2)=‖f i‖^2 :=
      sum_eq_single i (fun j hj hji => by rw [hz j hj hji,norm_zero,zero_pow (by norm_num : 2 ≠ 0)])
        (fun hn => False.elim (hn hi))
    rw [he,he']
  · have hz : ∀ i ∈ S,f i=0 := by simpa only [not_exists,not_and,not_not] using h
    have he : (∑ i ∈ S,f i)=0 := sum_eq_zero hz
    rw [he,norm_zero,zero_pow (by norm_num : 2 ≠ 0)]
    symm
    apply sum_eq_zero
    intro i hi
    rw [hz i hi,norm_zero,zero_pow (by norm_num : 2 ≠ 0)]

theorem finite_disjoint_square_energy {ι : Type*} (I : Finset ι) (J : Finset ℕ) (F : ℕ → ι → ℂ)
    (hF : ∀ n ∈ J,∀ i ∈ I,∀ k ∈ I,F n i ≠ 0 → F n k ≠ 0 → i=k) :
    (∑ n ∈ J,‖∑ i ∈ I,F n i‖^2)=∑ i ∈ I,∑ n ∈ J,‖F n i‖^2 := by
  calc
    _ = ∑ n ∈ J,∑ i ∈ I,‖F n i‖^2 :=
      sum_congr rfl (fun n hn => norm_sum_square_single_support I (F n) (hF n hn))
    _ = _ := sum_comm

end PrimeSquares
