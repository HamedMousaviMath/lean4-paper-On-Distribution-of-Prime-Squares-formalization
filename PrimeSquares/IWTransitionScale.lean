import PrimeSquares.IWNarrowWidth

set_option autoImplicit false
namespace PrimeSquares

noncomputable def iwTransitionIndex (δ : ℝ) : ℕ := ⌈(-Real.log δ)/(2*Real.log 2)⌉₊
noncomputable def iwTransitionScale (δ : ℝ) : ℕ := (2 : ℕ)^(iwTransitionIndex δ)

theorem real_log_two_half_le : (1/2 : ℝ)≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<1/2)
  rw [one_div,Real.log_inv] at h
  linarith

theorem iwTransitionIndex_bounds {δ : ℝ} (hδ0 : 0<δ) (hδ1 : δ≤1) :
    (-Real.log δ)/(2*Real.log 2)≤(iwTransitionIndex δ : ℝ) ∧
      (iwTransitionIndex δ : ℝ)<(-Real.log δ)/(2*Real.log 2)+1 := by
  have hnon : 0≤(-Real.log δ)/(2*Real.log 2) := by
    have hl : Real.log δ≤0 := Real.log_nonpos hδ0.le hδ1
    have h2 : 0< Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    exact div_nonneg (neg_nonneg.mpr hl) (mul_nonneg (by norm_num) h2.le)
  exact ⟨Nat.le_ceil _,Nat.ceil_lt_add_one hnon⟩

theorem iwTransitionScale_squared_bounds {δ : ℝ} (hδ0 : 0<δ) (hδ1 : δ≤1) :
    1≤(iwTransitionScale δ : ℝ)^2*δ ∧ (iwTransitionScale δ : ℝ)^2*δ<4 := by
  have h2 : 0< Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hd : 0<2*Real.log (2 : ℝ) := by positivity
  obtain ⟨hlo,hhi⟩ := iwTransitionIndex_bounds hδ0 hδ1
  have hl := (div_le_iff₀ hd).mp hlo
  have hh := mul_lt_mul_of_pos_right hhi hd
  rw [add_mul,div_mul_cancel₀ _ hd.ne',one_mul] at hh
  let Y : ℝ := (iwTransitionScale δ : ℝ)^2*δ
  have hY : 0< Y := by dsimp [Y,iwTransitionScale];positivity
  have he : Real.log Y=2*(iwTransitionIndex δ : ℝ)*Real.log 2+Real.log δ := by
    dsimp [Y,iwTransitionScale]
    rw [Real.log_mul (by positivity : (((2 : ℕ)^(iwTransitionIndex δ) : ℕ) : ℝ)^2≠0) hδ0.ne',Real.log_pow]
    rw [Nat.cast_pow,Real.log_pow]
    push_cast
    ring
  have h4 : Real.log (4 : ℝ)=2*Real.log 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  constructor
  · apply (Real.log_le_log_iff (by norm_num : (0 : ℝ)<1) hY).mp
    rw [Real.log_one,he]
    nlinarith
  · apply (Real.log_lt_log_iff hY (by norm_num : (0 : ℝ)<4)).mp
    rw [he,h4]
    nlinarith

theorem iwTransitionScale_sqrt_bounds {δ : ℝ} (hδ0 : 0<δ) (hδ1 : δ≤1) :
    1≤(iwTransitionScale δ : ℝ)*Real.sqrt δ ∧
      (iwTransitionScale δ : ℝ)*Real.sqrt δ<2 := by
  obtain ⟨hl,hh⟩ := iwTransitionScale_squared_bounds hδ0 hδ1
  have hs := Real.sq_sqrt hδ0.le
  have hn : 0≤(iwTransitionScale δ : ℝ) := Nat.cast_nonneg _
  have hr := Real.sqrt_nonneg δ
  constructor <;> nlinarith [mul_nonneg hn hr,sq_nonneg ((iwTransitionScale δ : ℝ)*Real.sqrt δ-1)]

end PrimeSquares
