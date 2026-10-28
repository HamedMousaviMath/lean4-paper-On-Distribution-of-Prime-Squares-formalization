import PrimeSquares.FiniteSignedMaximalInterface
import PrimeSquares.BinaryDepthLogarithm
import PrimeSquares.IntervalComplexSum
import PrimeSquares.IWTransitionScale
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

noncomputable def finiteBooleanSign (b : Bool) : ℂ := if b then 1 else -1

theorem finiteBooleanSign_norm (b : Bool) : ‖finiteBooleanSign b‖ = 1 := by
  cases b <;> norm_num [finiteBooleanSign]

theorem finiteBooleanSign_not (b : Bool) : finiteBooleanSign (!b) = -finiteBooleanSign b := by
  cases b <;> norm_num [finiteBooleanSign]

theorem finiteBooleanSign_self (b : Bool) : finiteBooleanSign b * finiteBooleanSign b = 1 := by
  cases b <;> norm_num [finiteBooleanSign]

noncomputable def finiteBooleanFlip {n : ℕ} (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun σ := Function.update σ i (!σ i)
  invFun σ := Function.update σ i (!σ i)
  left_inv σ := by
    funext j
    by_cases h : j=i
    · subst j; simp
    · simp [h]
  right_inv σ := by
    funext j
    by_cases h : j=i
    · subst j; simp
    · simp [h]

theorem finiteBooleanSign_orthogonality {n : ℕ} (i j : Fin n) :
    (∑ σ : Fin n→Bool,finiteBooleanSign (σ i)*finiteBooleanSign (σ j)) =
      if i=j then (Fintype.card (Fin n→Bool) : ℂ) else 0 := by
  classical
  by_cases hij : i=j
  · subst j; simp [finiteBooleanSign_self]
  · simp only [hij,ite_false]
    have hflip : ∀ σ : Fin n→Bool,
        finiteBooleanSign (finiteBooleanFlip i σ i)*finiteBooleanSign (finiteBooleanFlip i σ j)=
          -(finiteBooleanSign (σ i)*finiteBooleanSign (σ j)) := by
      intro σ
      simp [finiteBooleanFlip,Ne.symm hij,finiteBooleanSign_not]
    have he := (finiteBooleanFlip i).sum_comp
      (fun σ : Fin n→Bool => finiteBooleanSign (σ i)*finiteBooleanSign (σ j))
    simp_rw [hflip,Finset.sum_neg_distrib] at he
    have hz : (2 : ℂ)*(∑ σ : Fin n→Bool,finiteBooleanSign (σ i)*finiteBooleanSign (σ j))=0 := by
      linear_combination -he
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem finiteBooleanSign_reconstruction {n : ℕ} (v : Fin n→ℂ) (i : Fin n) :
    (∑ σ : Fin n→Bool,finiteBooleanSign (σ i)*(∑ j,finiteBooleanSign (σ j)*v j))=
      (Fintype.card (Fin n→Bool) : ℂ)*v i := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [←mul_assoc,←Finset.sum_mul,finiteBooleanSign_orthogonality]
  simp

noncomputable def finiteSignAverage {n : ℕ} (v : Fin n→ℂ) : ℝ :=
  (Fintype.card (Fin n→Bool) : ℝ)⁻¹*
    ∑ σ : Fin n→Bool,‖∑ j,finiteBooleanSign (σ j)*v j‖

theorem finiteSignAverage_nonneg {n : ℕ} (v : Fin n→ℂ) : 0≤finiteSignAverage v := by
  unfold finiteSignAverage
  positivity

theorem finiteSignAverage_dominates {n : ℕ} (v : Fin n→ℂ) (i : Fin n) :
    ‖v i‖≤finiteSignAverage v := by
  classical
  have hcard : (0 : ℝ)<Fintype.card (Fin n→Bool) := by exact_mod_cast Fintype.card_pos
  have hn := norm_sum_le (s:=Finset.univ)
    (f:=fun σ : Fin n→Bool => finiteBooleanSign (σ i)*(∑ j,finiteBooleanSign (σ j)*v j))
  rw [finiteBooleanSign_reconstruction,norm_mul] at hn
  simp only [Complex.norm_natCast,norm_mul,finiteBooleanSign_norm,one_mul] at hn
  unfold finiteSignAverage
  exact (le_inv_mul_iff₀ hcard).mpr hn


theorem finiteSignAverage_Lp {n : ℕ} (u : Fin n→ℤ→ℂ) {p : ENNReal} (hp : 1≤p)
    (B : ENNReal)
    (hu : ∀ σ : Fin n→Bool,
      MemLp (fun x => ∑ j,finiteBooleanSign (σ j)*u j x) p Measure.count ∧
      eLpNorm (fun x => ∑ j,finiteBooleanSign (σ j)*u j x) p Measure.count≤B) :
    MemLp (fun x => finiteSignAverage (fun j => u j x)) p Measure.count ∧
      eLpNorm (fun x => finiteSignAverage (fun j => u j x)) p Measure.count≤B := by
  classical
  let c : ℝ := (Fintype.card (Fin n→Bool) : ℝ)⁻¹
  let F : (Fin n→Bool)→ℤ→ℝ := fun σ x => ‖∑ j,finiteBooleanSign (σ j)*u j x‖
  have hF : ∀ σ,MemLp (F σ) p Measure.count := fun σ => (hu σ).1.norm
  have hSum : MemLp (fun x => ∑ σ,F σ x) p Measure.count :=
    memLp_finsetSum univ (fun σ _ => hF σ)
  refine ⟨hSum.const_mul c,?_⟩
  change eLpNorm (c • (fun x => ∑ σ,F σ x)) p Measure.count≤B
  rw [eLpNorm_const_smul]
  have hc : 0<c := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  rw [Real.enorm_eq_ofReal hc.le]
  have hb : eLpNorm (fun x => ∑ σ,F σ x) p Measure.count≤∑ _σ : Fin n→Bool,B := by
    calc
      _ ≤ ∑ σ,eLpNorm (F σ) p Measure.count := by
        have hefun : (fun x => ∑ σ,F σ x)=∑ σ,F σ := by
          funext x
          exact (Finset.sum_apply x univ F).symm
        rw [hefun]
        exact eLpNorm_sum_le hp
      _ ≤ _ := sum_le_sum fun σ _ => by
        dsimp [F]
        rw [eLpNorm_norm _ (hu σ).1.aestronglyMeasurable]
        exact (hu σ).2
  calc
    _ ≤ ENNReal.ofReal c*(∑ _σ : Fin n→Bool,B) := mul_le_mul_right hb _
    _ = B := by
      dsimp [c]
      rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast Fintype.card_pos),
        ENNReal.ofReal_natCast,sum_const,card_univ,nsmul_eq_mul,←mul_assoc,
        ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp),one_mul]

theorem signed_block_partition (f w : ℕ→ℂ) (L : ℕ) (hL : 0<L) (M : ℕ) :
    (∑ b∈range M,w b*intervalComplexSum (b*L) L f)=
      ∑ j∈range (M*L),w (j/L)*f j := by
  induction M with
  | zero => simp [intervalComplexSum]
  | succ M ih =>
    rw [sum_range_succ,ih,Nat.succ_mul,sum_range_add]
    congr 1
    rw [intervalComplexSum,mul_sum]
    apply sum_congr rfl
    intro r hr
    have hrL := mem_range.mp hr
    have hd : (M*L+r)/L=M := by
      rw [Nat.mul_comm M L,Nat.mul_add_div hL,Nat.div_eq_of_lt hrL,Nat.add_zero]
    rw [hd]

noncomputable def signedPaddedSequence (u : ℕ→ℤ→ℂ) (J : ℕ) (j : ℕ) (x : ℤ) : ℂ :=
  if j<J then u j x else 0

noncomputable def signedBlockFamily (u : ℕ→ℤ→ℂ) (J M L : ℕ) (b : Fin M) (x : ℤ) : ℂ :=
  intervalComplexSum (b.val*L) L (fun j => signedPaddedSequence u J j x)

noncomputable def finiteBooleanSignLift {M : ℕ} (σ : Fin M→Bool) (j : ℕ) : ℂ :=
  if hj : j<M then finiteBooleanSign (σ ⟨j,hj⟩) else 0

theorem finiteBooleanSignLift_norm {M : ℕ} (σ : Fin M→Bool) (j : ℕ) :
    ‖finiteBooleanSignLift σ j‖≤1 := by
  unfold finiteBooleanSignLift
  split
  · rw [finiteBooleanSign_norm]
  · simp

theorem signedBlockFamily_sum (u : ℕ→ℤ→ℂ) (J M L : ℕ) (hL : 0<L) (hJM : J≤M)
    (σ : Fin M→Bool) (x : ℤ) :
    (∑ b,finiteBooleanSign (σ b)*signedBlockFamily u J M L b x)=
      signedSequenceSum u J (fun j => finiteBooleanSignLift σ (j/L)) x := by
  classical
  have he : (∑ b,finiteBooleanSign (σ b)*signedBlockFamily u J M L b x)=
      ∑ b∈range M,finiteBooleanSignLift σ b*
        intervalComplexSum (b*L) L (fun j => signedPaddedSequence u J j x) := by
    rw [←Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro b _
    simp [signedBlockFamily,finiteBooleanSignLift,b.isLt]
  rw [he,signed_block_partition _ _ L hL M]
  have hcap : J≤M*L := hJM.trans (Nat.le_mul_of_pos_right M hL)
  unfold signedSequenceSum
  rw [←sum_range_add_sum_Ico _ hcap]
  have hz : (∑ j∈Ico J (M*L),finiteBooleanSignLift σ (j/L)*signedPaddedSequence u J j x)=0 := by
    apply sum_eq_zero
    intro j hj
    simp [signedPaddedSequence,not_lt.mpr (mem_Ico.mp hj).1]
  rw [hz,add_zero]
  apply sum_congr rfl
  intro j hj
  simp [signedPaddedSequence,mem_range.mp hj]


theorem signed_binary_strict_prefix_bound (H M : ℕ) (f : ℕ→ℂ) (g : ℕ→ℝ)
    (hg0 : ∀ k,0≤g k)
    (hg : ∀ k b,k≤H → b*2^k+2^k≤M → ‖intervalComplexSum (b*2^k) (2^k) f‖≤g k) :
    ∀ h≤H,∀ b m,b*2^h+2^h≤M → m<2^h →
      ‖intervalComplexSum (b*2^h) m f‖≤∑ k∈range h,g k := by
  intro h
  induction h with
  | zero =>
    intro _ b m _ hm
    have hm0 : m=0 := by simpa using hm
    subst m
    simp [intervalComplexSum_zero]
  | succ h ih =>
    intro hh b m hcap hm
    have hp : 2^(h+1)=2^h+2^h := by rw [pow_succ];omega
    have hl : b*2^(h+1)=(b*2)*2^h := by rw [pow_succ];ring
    have hr : (b*2+1)*2^h=b*2^(h+1)+2^h := by rw [pow_succ];ring
    have hcl : (b*2)*2^h+2^h≤M := by omega
    have hcr : (b*2+1)*2^h+2^h≤M := by omega
    by_cases hsmall : m<2^h
    · rw [hl]
      exact (ih (by omega) (b*2) m hcl hsmall).trans
        (by rw [sum_range_succ];exact le_add_of_nonneg_right (hg0 h))
    · have hrem : m-2^h<2^h := by omega
      have hmrepr : m=2^h+(m-2^h) := by omega
      conv_lhs => rw [hmrepr]
      rw [intervalComplexSum_add]
      have hright : b*2^(h+1)+2^h=(b*2+1)*2^h := hr.symm
      calc
        _ ≤ ‖intervalComplexSum (b*2^(h+1)) (2^h) f‖+
            ‖intervalComplexSum (b*2^(h+1)+2^h) (m-2^h) f‖ := norm_add_le _ _
        _ ≤ g h+∑ k∈range h,g k := by
          rw [hright,hl]
          exact add_le_add (hg h (b*2) (by omega) hcl)
            (ih (by omega) (b*2+1) (m-2^h) hcr hrem)
        _ = _ := by rw [sum_range_succ];ring

theorem signed_binary_prefix_bound (H : ℕ) (f : ℕ→ℂ) (g : ℕ→ℝ)
    (hg0 : ∀ k,0≤g k)
    (hg : ∀ k b,k≤H → b*2^k+2^k≤2^H → ‖intervalComplexSum (b*2^k) (2^k) f‖≤g k)
    {m : ℕ} (hm : m≤2^H) :
    ‖intervalComplexSum 0 m f‖≤∑ k∈range (H+1),g k := by
  by_cases hstrict : m<2^H
  · have hb := signed_binary_strict_prefix_bound H (2^H) f g hg0 hg H le_rfl 0 m
      (by simp) hstrict
    simp only [zero_mul] at hb
    exact hb.trans (by rw [sum_range_succ];exact le_add_of_nonneg_right (hg0 H))
  · have he : m=2^H := by omega
    subst m
    have hb := hg H 0 le_rfl (by simp)
    simp only [zero_mul] at hb
    exact hb.trans (by rw [sum_range_succ];exact le_add_of_nonneg_left (sum_nonneg fun k _ => hg0 k))


theorem finite_signed_maximal_binary (J : ℕ) (u : ℕ→ℤ→ℂ) {p : ENNReal} (hp : 1≤p)
    (B : ENNReal)
    (hu : ∀ σ : ℕ→ℂ,(∀ j∈range J,‖σ j‖≤1) →
      MemLp (signedSequenceSum u J σ) p Measure.count ∧
      eLpNorm (signedSequenceSum u J σ) p Measure.count≤B) :
    MemLp (finitePartialSumMaximum u J) p Measure.count ∧
      eLpNorm (finitePartialSumMaximum u J) p Measure.count≤
        ENNReal.ofReal (finiteBinaryDepth J+1 : ℝ)*B := by
  classical
  let H := finiteBinaryDepth J
  let M := 2^H
  have hJM : J≤M := finiteBinaryDepth_capacity J
  let g : ℕ→ℤ→ℝ := fun k x => finiteSignAverage (fun b : Fin M =>
    signedBlockFamily u J M (2^k) b x)
  have hg0 : ∀ k x,0≤g k x := fun k x => finiteSignAverage_nonneg _
  have hgLp : ∀ k,MemLp (g k) p Measure.count ∧ eLpNorm (g k) p Measure.count≤B := by
    intro k
    apply finiteSignAverage_Lp _ hp B
    intro σ
    have he : (fun x => ∑ b,finiteBooleanSign (σ b)*signedBlockFamily u J M (2^k) b x)=
        signedSequenceSum u J (fun j => finiteBooleanSignLift σ (j/(2^k))) := by
      funext x
      exact signedBlockFamily_sum u J M (2^k) (pow_pos (by norm_num) _) hJM σ x
    rw [he]
    exact hu _ (fun j _ => finiteBooleanSignLift_norm _ _)
  have hblock : ∀ x k b,k≤H → b*2^k+2^k≤M →
      ‖intervalComplexSum (b*2^k) (2^k) (fun j => signedPaddedSequence u J j x)‖≤g k x := by
    intro x k b _ hcap
    have hbmul : b≤b*2^k := Nat.le_mul_of_pos_right b (pow_pos (by norm_num) _)
    have hb : b<M := by have hp : 0<2^k := pow_pos (by norm_num) _;omega
    exact finiteSignAverage_dominates
      (fun b : Fin M => signedBlockFamily u J M (2^k) b x) ⟨b,hb⟩
  have hpoint : ∀ x,finitePartialSumMaximum u J x≤∑ k∈range (H+1),g k x := by
    intro x
    apply partialSups_le
    intro m hm
    have he : intervalComplexSum 0 m (fun j => signedPaddedSequence u J j x)=
        ∑ j∈range m,u j x := by
      unfold intervalComplexSum
      apply sum_congr rfl
      intro j hj
      simp [signedPaddedSequence,(mem_range.mp hj).trans_le hm]
    rw [←he]
    exact signed_binary_prefix_bound H _ (fun k => g k x) (fun k => hg0 k x)
      (hblock x) (hm.trans hJM)
  have hG : MemLp (fun x => ∑ k∈range (H+1),g k x) p Measure.count :=
    memLp_finsetSum _ (fun k _ => (hgLp k).1)
  have hmeas : AEStronglyMeasurable (finitePartialSumMaximum u J) Measure.count :=
    (measurable_of_countable _).aestronglyMeasurable
  have hnorm : ∀ x,‖finitePartialSumMaximum u J x‖≤∑ k∈range (H+1),g k x := by
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (finitePartialSumMaximum_nonneg _ _ _)]
    exact hpoint x
  refine ⟨hG.of_le hmeas (Filter.Eventually.of_forall fun x =>
    (hnorm x).trans (le_abs_self _)),?_⟩
  calc
    _ ≤ eLpNorm (fun x => ∑ k∈range (H+1),g k x) p Measure.count :=
      eLpNorm_mono_real hmeas hnorm
    _ ≤ ∑ k∈range (H+1),eLpNorm (g k) p Measure.count := by
      have hefun : (fun x => ∑ k∈range (H+1),g k x)=∑ k∈range (H+1),g k := by
        funext x
        exact (Finset.sum_apply x (range (H+1)) g).symm
      rw [hefun]
      exact eLpNorm_sum_le hp
    _ ≤ ∑ _k∈range (H+1),B := sum_le_sum fun k _ => (hgLp k).2
    _ = _ := by simp [H,ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one]

theorem finite_signed_binary_log_bound (J : ℕ) :
    (finiteBinaryDepth J+1 : ℝ)≤6*Real.log (2+(J : ℝ)) := by
  by_cases hJ : J=0
  · subst J
    simp only [finiteBinaryDepth_zero,Nat.cast_zero,zero_add,add_zero]
    linarith [real_log_two_half_le]
  · have hJp : (0 : ℝ)<J := by exact_mod_cast Nat.pos_of_ne_zero hJ
    have hhalf : (1/2 : ℝ)≤Real.log (2+(J : ℝ)) :=
      real_log_two_half_le.trans (Real.log_le_log (by norm_num) (le_add_of_nonneg_right (Nat.cast_nonneg J)))
    have hlog : Real.log (J : ℝ)≤Real.log (2+(J : ℝ)) :=
      Real.log_le_log hJp (by linarith)
    have hnat := Real.log2_le_logb J
    unfold Real.logb at hnat
    have hnat' := (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ)<2))).mp hnat
    have hdepth := finiteBinaryDepth_factor_le J
    have hmul : (Nat.log2 J : ℝ)*(1/2)≤(Nat.log2 J : ℝ)*Real.log 2 :=
      mul_le_mul_of_nonneg_left real_log_two_half_le (Nat.cast_nonneg _)
    linarith

/-- A proved general finite signed-sum maximal theorem; no analytic input.
The binary proof works for every exponent p>=1, and hence for the input's
stated 1<=p<=2 range. The numerical constant 6 is deliberately nonsharp. -/
theorem rawFiniteSignedMaximalInput_proved : RawFiniteSignedMaximalInput 6 := by
  intro p hp _ J u B hu
  have hp' : (1 : ENNReal)≤ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  obtain ⟨hm,hb⟩ := finite_signed_maximal_binary J u hp' B hu
  refine ⟨hm,hb.trans ?_⟩
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (finite_signed_binary_log_bound J)) B

end PrimeSquares
