import PrimeSquares.NearOneLayerAbsorption
import PrimeSquares.HighLowOperators

open Finset
namespace PrimeSquares

noncomputable def functionLayerIndex (u : ℝ) : ℕ :=
  if h : 1≤u then Classical.choose (exists_nat_pow_near h (by norm_num : (1 : ℝ)<2)) else 0

theorem functionLayerIndex_spec {u : ℝ} (hu : 1≤u) :
    (2 : ℝ)^(functionLayerIndex u)≤u ∧ u<(2 : ℝ)^(functionLayerIndex u+1) := by
  simp only [functionLayerIndex,dite_eq_left hu]
  exact Classical.choose_spec (exists_nat_pow_near hu (by norm_num : (1 : ℝ)<2))

noncomputable def functionLayer (F : Finset ℤ) (u : ℤ → ℝ) (j : ℕ) : Finset ℤ :=
  F.filter (fun x => 1<u x ∧ functionLayerIndex (u x)=j)

noncomputable def functionLayerIndices (F : Finset ℤ) (u : ℤ → ℝ) : Finset ℕ :=
  F.image (fun x => functionLayerIndex (u x))

theorem functionLayer_mem {F : Finset ℤ} {u : ℤ → ℝ} {j : ℕ} {x : ℤ} :
    x∈functionLayer F u j ↔ x∈F ∧ 1<u x ∧ functionLayerIndex (u x)=j := by
  classical
  simp only [functionLayer,mem_filter]

theorem functionLayer_disjoint (F : Finset ℤ) (u : ℤ → ℝ) {i j : ℕ} (hij : i≠j) :
    Disjoint (functionLayer F u i) (functionLayer F u j) := by
  rw [disjoint_left]
  intro x hi hj
  exact hij ((functionLayer_mem.mp hi).2.2.symm.trans (functionLayer_mem.mp hj).2.2)

theorem functionLayer_nonempty_index {F : Finset ℤ} {u : ℤ → ℝ} {j : ℕ} {x : ℤ}
    (hx : x∈functionLayer F u j) : j∈functionLayerIndices F u := by
  classical
  exact mem_image.mpr ⟨x,(functionLayer_mem.mp hx).1,(functionLayer_mem.mp hx).2.2⟩

theorem functionLayer_bounds {F : Finset ℤ} {u : ℤ → ℝ} {j : ℕ} {x : ℤ}
    (hx : x∈functionLayer F u j) : (2 : ℝ)^j≤u x ∧ u x<(2 : ℝ)^(j+1) := by
  obtain ⟨_,hu,hj⟩ := functionLayer_mem.mp hx
  simpa only [hj] using functionLayerIndex_spec hu.le

theorem functionLayer_partition_cost (F : Finset ℤ) (u : ℤ → ℝ) (b : ℕ → ℝ) :
    (∑ j∈functionLayerIndices F u,(functionLayer F u j).card*b j)=
      ∑ x∈F,if 1<u x then b (functionLayerIndex (u x)) else 0 := by
  classical
  calc
    _ = ∑ j∈functionLayerIndices F u,∑ x∈F,
        if 1<u x ∧ functionLayerIndex (u x)=j then b j else 0 := by
      apply sum_congr rfl
      intro j hj
      rw [←sum_filter]
      simp only [functionLayer,sum_const,nsmul_eq_mul]
    _ = ∑ x∈F,∑ j∈functionLayerIndices F u,
        if 1<u x ∧ functionLayerIndex (u x)=j then b j else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro x hx
      by_cases hu : 1<u x
      · simp only [hu,true_and,ite_true]
        have hm : functionLayerIndex (u x)∈functionLayerIndices F u := mem_image.mpr ⟨x,hx,rfl⟩
        simp [eq_comm,hm]
      · simp [hu]

theorem functionLayer_majorization (F : Finset ℤ) (f : ℤ → ℂ)
    (hf : ∀ x,x∉F → f x=0) {K level : ℝ} (hK : 0<K) (hlevel : 0<level) (x : ℤ) :
    ‖f x‖≤level/K+∑ j∈functionLayerIndices F (fun y => K*‖f y‖/level),
      ((2 : ℝ)^(j+1)*level/K)*(if x∈functionLayer F (fun y => K*‖f y‖/level) j then 1 else 0) := by
  classical
  let u := fun y => K*‖f y‖/level
  by_cases hu : 1<u x
  · have hx : x∈F := by
      by_contra hn
      have hf0 := hf x hn
      norm_num [u,hf0] at hu
    let j := functionLayerIndex (u x)
    have hj : j∈functionLayerIndices F u := mem_image.mpr ⟨x,hx,rfl⟩
    have hmem : x∈functionLayer F u j := functionLayer_mem.mpr ⟨hx,hu,rfl⟩
    have hbound : ‖f x‖≤(2 : ℝ)^(j+1)*level/K := by
      have h := (functionLayerIndex_spec hu.le).2.le
      change K*‖f x‖/level≤(2 : ℝ)^(j+1) at h
      have h' := (div_le_iff₀ hlevel).mp h
      exact (le_div_iff₀ hK).mpr (by nlinarith)
    have hsum := single_le_sum (s := functionLayerIndices F u)
      (f := fun j => ((2 : ℝ)^(j+1)*level/K)*(if x∈functionLayer F u j then 1 else 0))
      (fun j _ => by split_ifs <;> positivity) hj
    rw [ite_eq_left hmem,mul_one] at hsum
    have hs : 0≤level/K := by positivity
    exact hbound.trans (by linarith)
  · have hsmall : ‖f x‖≤level/K := by
      have h : K*‖f x‖/level≤1 := le_of_not_gt hu
      exact (le_div_iff₀ hK).mpr (by have h' := (div_le_iff₀ hlevel).mp h;nlinarith)
    exact hsmall.trans (le_add_of_nonneg_right (sum_nonneg (fun j _ => by split_ifs <;> positivity)))

end PrimeSquares
