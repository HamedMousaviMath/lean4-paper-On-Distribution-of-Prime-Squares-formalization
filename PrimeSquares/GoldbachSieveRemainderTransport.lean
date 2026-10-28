import PrimeSquares.GoldbachUpperSieveSequence

set_option autoImplicit false
open Finset
open scoped SchwartzMap
namespace PrimeSquares

theorem goldbach_pred_square_sum_bound (N : ℕ) (T : Finset ℕ)
    (hT : ∀ n∈T,0<n ∧ n<N^2) (f : ℕ→ℂ) :
    (∑ n∈T,‖f (n-1)‖^2)≤∑ n∈range (N^2),‖f n‖^2 := by
  classical
  have he : (∑ n∈T,‖f (n-1)‖^2)=(∑ m∈T.image (fun n=>n-1),‖f m‖^2) := by
    symm
    apply sum_image
    intro n hn m hm hnm
    change n-1=m-1 at hnm
    have := (hT n hn).1
    have := (hT m hm).1
    omega
  rw [he]
  apply sum_le_sum_of_subset_of_nonneg
  · intro m hm
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hm
    exact mem_range.mpr (lt_of_le_of_lt (Nat.sub_le n 1) (hT n hn).2)
  · intro m _ _
    exact sq_nonneg _

theorem goldbach_pred_full_square_sum_bound (N : ℕ) (f : ℕ→ℂ) :
    (∑ n∈range (N^2),‖f (n-1)‖^2)≤2*(∑ n∈range (N^2),‖f n‖^2) := by
  classical
  by_cases hN : N=0
  · subst N
    simp
  · have hN0 : 0<N^2 := Nat.pow_pos (Nat.pos_of_ne_zero hN)
    have hsplit := sum_filter_add_sum_filter_not (range (N^2)) (fun n : ℕ=>0<n) (fun n=>‖f (n-1)‖^2)
    have hzero : (range (N^2)).filter (fun n : ℕ=>¬0<n)={0} := by
      ext n
      simp only [mem_filter,mem_range,mem_singleton]
      omega
    rw [hzero,sum_singleton,Nat.zero_sub] at hsplit
    have hshift := goldbach_pred_square_sum_bound N ((range (N^2)).filter (fun n : ℕ=>0<n))
      (fun n hn=>⟨(mem_filter.mp hn).2,mem_range.mp (mem_filter.mp hn).1⟩) f
    have hfirst : ‖f 0‖^2≤∑ n∈range (N^2),‖f n‖^2 :=
      single_le_sum (fun n _=>sq_nonneg ‖f n‖) (mem_range.mpr hN0)
    rw [←hsplit]
    linarith

theorem goldbach_sieve_remainders_selected
    (HSW : RawPrimeSiegelWalfiszInput) (HBV : RawPrimeBombieriVinogradovInput)
    (D : UniformRenGhoshInputs) (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x| →ψ x=0) {A δ : ℝ} (hA : 0<A) (hδ : 0<δ) :
    ∃ B₀ C K : ℝ,0≤B₀ ∧ 0<C ∧ 0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      ∀ B L : ℝ,B₀≤B →L<(N:ℝ)^(2-δ) →∀ V : ℕ→ℝ,
      (∀ ℓ : ℕ,0<ℓ →(ℓ:ℝ)<L →V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) →
      ∀ I : Finset (ℕ×ℕ),I⊆goldbachCoefficientIndices L V →
      ∀ a : ℕ×ℕ→ℕ,(∀ i∈I,(a i).Coprime i.2) →
      ∀ d : ℕ×ℕ→ℂ,(∀ i∈I,‖d i‖≤1) →
      (∑ n∈range (N^2),‖∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n‖^2)≤
        K*(N:ℝ)^4*(Real.log N)^(-A) ∧
      (∑ n∈range (N^2),‖∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) (n-1)‖^2)≤
        (2*K)*(N:ℝ)^4*(Real.log N)^(-A) ∧
      ∀ T : Finset ℕ,(∀ n∈T,0<n ∧ n<N^2) →
        (∑ n∈T,‖∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) (n-1)‖^2)≤
          K*(N:ℝ)^4*(Real.log N)^(-A) := by
  classical
  obtain ⟨B₀,C,K,hB₀,hC,hK,N₀,hN₀,hCircle⟩ := goldbach_circle_method_complete HSW HBV D ψ hψ hsψ hA hδ
  refine ⟨B₀,C,K,hB₀,hC,hK,N₀,hN₀,?_⟩
  intro N hN B L hB hL V hV I hI a ha d hd
  let a' := fun i : ℕ×ℕ=>if i∈I then a i else 1
  let d' := fun i : ℕ×ℕ=>if i∈I then d i else 0
  have ha' : ∀ i∈goldbachCoefficientIndices L V,(a' i).Coprime i.2 := by
    intro i _
    by_cases hi : i∈I
    · simpa only [a',ite_eq_left hi] using ha i hi
    · simp [a',hi]
  have hd' : ∀ i∈goldbachCoefficientIndices L V,‖d' i‖≤1 := by
    intro i _
    by_cases hi : i∈I
    · simpa only [d',ite_eq_left hi] using hd i hi
    · simp only [d',ite_eq_right hi,norm_zero,zero_le_one]
  have he (n : ℕ) : (∑ i∈goldbachCoefficientIndices L V,d' i*
      goldbachFullRemainder ψ N i.1 i.2 (a' i) ((Real.log N)^C) n)=
      ∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n := by
    calc
      _=∑ i∈I,d' i*goldbachFullRemainder ψ N i.1 i.2 (a' i) ((Real.log N)^C) n := by
        symm
        apply sum_subset hI
        intro i _ hi
        simp only [d',ite_eq_right hi,zero_mul]
      _=_ := by
        apply sum_congr rfl
        intro i hi
        simp only [a',d',ite_eq_left hi]
  have hFull := hCircle N hN B L hB hL V hV a' ha' d' hd'
  have hSelected : (∑ n∈range (N^2),‖∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n‖^2)≤
      K*(N:ℝ)^4*(Real.log N)^(-A) := by simpa only [he] using hFull
  refine ⟨hSelected,?_,?_⟩
  · calc
      _≤2*(∑ n∈range (N^2),‖∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n‖^2) :=
        goldbach_pred_full_square_sum_bound N _
      _≤2*(K*(N:ℝ)^4*(Real.log N)^(-A)) := mul_le_mul_of_nonneg_left hSelected (by norm_num)
      _=_ := by ring
  intro T hT
  exact (goldbach_pred_square_sum_bound N T hT
    (fun n=>∑ i∈I,d i*goldbachFullRemainder ψ N i.1 i.2 (a i) ((Real.log N)^C) n)).trans hSelected

end PrimeSquares
