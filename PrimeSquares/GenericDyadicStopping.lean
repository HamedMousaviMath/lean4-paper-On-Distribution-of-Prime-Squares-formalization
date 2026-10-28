import PrimeSquares.GenericDyadicKernels

set_option autoImplicit false
open Finset
open scoped NNReal
namespace PrimeSquares

def linearDyadicIndices (L : ℕ) : Finset ℕ := (Finset.range L).filter (fun j => (2:ℕ)^j ≤ L)

theorem mem_linearDyadicIndices (L j : ℕ) : j ∈ linearDyadicIndices L ↔ (2:ℕ)^j ≤ L := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hj : j < (2:ℕ)^j := Nat.lt_two_pow_self
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hj.trans_le h),h⟩

noncomputable def genericDyadicMaximum {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (J : Finset ℕ) (F : Finset ℤ) (x : ℤ) : ℝ≥0 := J.sup (fun j => ‖positiveDyadicValue T j F x‖₊)

theorem genericDyadicMaximum_attained {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    {J : Finset ℕ} (hJ : J.Nonempty) (F : Finset ℤ) (x : ℤ) :
    ∃ j ∈ J,genericDyadicMaximum T J F x=‖positiveDyadicValue T j F x‖₊ :=
  Finset.exists_mem_eq_sup J hJ _

noncomputable def genericLocalMaxPairing {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (I : SparseIntegerInterval) (F G : Finset ℤ) : ℝ :=
  ∑ x ∈ G ∩ I.points,(genericDyadicMaximum T (linearDyadicIndices I.length)
    (F ∩ (I.oddDilate m).points) x:ℝ)

noncomputable def genericRemainingIndices (I : SparseIntegerInterval) (m : ℕ)
    (F : Finset ℤ) (x : ℤ) : Finset ℕ := (linearDyadicIndices I.length).filter (fun j =>
      ∀ A ∈ primeStoppingChildren I (F ∩ (I.oddDilate m).points),x ∈ A.points → A.length < (2:ℕ)^j)

theorem genericRemainingIndices_subset (I : SparseIntegerInterval) (m : ℕ) (F : Finset ℤ) (x : ℤ) :
    genericRemainingIndices I m F x ⊆ linearDyadicIndices I.length := Finset.filter_subset _ _

theorem genericRemainingScale_admissible (I : SparseIntegerInterval) (m : ℕ)
    (F : Finset ℤ) (C : ℝ) {x : ℤ} (hx : x ∈ I.points) {j : ℕ}
    (hj : j ∈ genericRemainingIndices I m F x) :
    linearSourceLocalMass C ((2:ℕ)^j) (finiteIndicatorLp (F ∩ (I.oddDilate m).points) 1) x ≤
      (320*max 1 C)*(((F ∩ (I.oddDilate m).points).card:ℝ)/I.length) := by
  apply linearStopping_remaining_radius I (F ∩ (I.oddDilate m).points) C
    (one_le_pow₀ (by norm_num)) hx
  exact (Finset.mem_filter.mp hj).2

theorem genericRemainingScale_pointwise {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (hC : C ≤ (m:ℝ)) (I : SparseIntegerInterval) (F : Finset ℤ) (x : ℤ) :
    genericDyadicMaximum T (linearDyadicIndices I.length) (F ∩ (I.oddDilate m).points) x ≤
      genericDyadicMaximum T (genericRemainingIndices I m F x) (F ∩ (I.oddDilate m).points) x+
        ∑ A ∈ primeStoppingChildren I (F ∩ (I.oddDilate m).points),
          if x ∈ A.points then genericDyadicMaximum T (linearDyadicIndices A.length)
            (F ∩ (A.oddDilate m).points) x else 0 := by
  unfold genericDyadicMaximum
  apply Finset.sup_le
  intro j hj
  by_cases hr : j ∈ genericRemainingIndices I m F x
  · exact (Finset.le_sup (f:=fun j => ‖positiveDyadicValue T j (F ∩ (I.oddDilate m).points) x‖₊) hr).trans
      (le_add_of_nonneg_right (by positivity))
  · have hnorem : ¬∀ A ∈ primeStoppingChildren I (F ∩ (I.oddDilate m).points),
        x ∈ A.points → A.length < (2:ℕ)^j := by
      intro hh
      exact hr (Finset.mem_filter.mpr ⟨hj,hh⟩)
    push Not at hnorem
    obtain ⟨A,hA,hxA,hN⟩ := hnorem
    have hAI := (primeStoppingChildren_geometry hA).1
    have hv := positiveDyadicValue_restrict_twice T hAI m j hC hN F hxA
    have hja := (mem_linearDyadicIndices A.length j).mpr hN
    have hmax := Finset.le_sup (f:=fun j => ‖positiveDyadicValue T j (F ∩ (A.oddDilate m).points) x‖₊) hja
    have hsingle := Finset.single_le_sum (s:=primeStoppingChildren I (F ∩ (I.oddDilate m).points))
      (f:=fun B => if x ∈ B.points then (linearDyadicIndices B.length).sup
        (fun j => ‖positiveDyadicValue T j (F ∩ (B.oddDilate m).points) x‖₊) else 0)
      (fun _ _ => by positivity) hA
    rw [ite_eq_left hxA] at hsingle
    rw [hv]
    exact (hmax.trans hsingle).trans (le_add_of_nonneg_left (by positivity))

theorem genericRemainingScale_pairing {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (hC : C ≤ (m:ℝ)) (I : SparseIntegerInterval) (F G : Finset ℤ) :
    genericLocalMaxPairing T m I F G ≤
      (∑ x ∈ G ∩ I.points,(genericDyadicMaximum T (genericRemainingIndices I m F x)
        (F ∩ (I.oddDilate m).points) x:ℝ))+
      ∑ A ∈ primeStoppingChildren I (F ∩ (I.oddDilate m).points),genericLocalMaxPairing T m A F G := by
  have h := Finset.sum_le_sum (fun x (_hx : x ∈ G ∩ I.points) =>
    show (genericDyadicMaximum T (linearDyadicIndices I.length) (F ∩ (I.oddDilate m).points) x:ℝ) ≤ _ from
      NNReal.coe_le_coe.mpr (genericRemainingScale_pointwise T m hC I F x))
  simp only [NNReal.coe_add,NNReal.coe_sum,apply_ite,NNReal.coe_zero] at h
  rw [Finset.sum_add_distrib,Finset.sum_comm] at h
  exact h.trans_eq (congrArg ((∑ x ∈ G ∩ I.points,
    (genericDyadicMaximum T (genericRemainingIndices I m F x) (F ∩ (I.oddDilate m).points) x:ℝ))+·)
      (Finset.sum_congr rfl (fun A hA => finiteSum_interval_mask I A
        (primeStoppingChildren_geometry hA).1 G _)))

end PrimeSquares
