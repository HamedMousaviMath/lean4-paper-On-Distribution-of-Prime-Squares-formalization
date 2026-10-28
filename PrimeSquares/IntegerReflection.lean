import PrimeSquares.FiniteComplexInputs

/-!
# Reflection of integer sequences and finite sets

Spatial reflection is an involutive isometry on every `lp` space used in the
paper, including `p = ∞`. It preserves cardinalities and reverses interval
endpoints. No analytic square-average theorem is used here.
-/

open scoped lp

namespace PrimeSquares

def reflectSequence {E : Type*} (f : ℤ → E) : ℤ → E := fun x => f (-x)

@[simp]
theorem reflectSequence_apply {E : Type*} (f : ℤ → E) (x : ℤ) :
    reflectSequence f x = f (-x) := rfl

@[simp]
theorem reflectSequence_involutive {E : Type*} (f : ℤ → E) :
    reflectSequence (reflectSequence f) = f := by
  funext x
  simp [reflectSequence]

theorem memLp_reflectSequence {E : Type*} [NormedAddCommGroup E]
    {p : ENNReal} {f : ℤ → E} (hf : Memℓp f p) :
    Memℓp (reflectSequence f) p := by
  rcases p.trichotomy with rfl | rfl | hp
  · apply memℓp_zero
    refine (hf.finite_dsupport.image (fun x : ℤ => -x)).subset ?_
    intro x hx
    exact ⟨-x, hx, neg_neg x⟩
  · apply memℓp_infty
    obtain ⟨B, hB⟩ := hf.bddAbove
    exact ⟨B, by rintro _ ⟨x, rfl⟩; exact hB ⟨-x, rfl⟩⟩
  · exact memℓp_gen ((Equiv.neg ℤ).summable_iff.mpr (hf.summable hp))

noncomputable def reflectLp {E : Type*} [NormedAddCommGroup E]
    {p : ENNReal} (f : ℓ^p(ℤ, E)) : ℓ^p(ℤ, E) :=
  ⟨reflectSequence f, memLp_reflectSequence (lp.memℓp f)⟩

@[simp]
theorem reflectLp_apply {E : Type*} [NormedAddCommGroup E]
    {p : ENNReal} (f : ℓ^p(ℤ, E)) (x : ℤ) : reflectLp f x = f (-x) := rfl

@[simp]
theorem reflectLp_involutive {E : Type*} [NormedAddCommGroup E]
    {p : ENNReal} (f : ℓ^p(ℤ, E)) : reflectLp (reflectLp f) = f := by
  apply lp.ext
  funext x
  simp

@[simp]
theorem reflectLp_norm {E : Type*} [NormedAddCommGroup E]
    {p : ENNReal} [Fact (1 ≤ p)] (f : ℓ^p(ℤ, E)) : ‖reflectLp f‖ = ‖f‖ := by
  rcases p.trichotomy with rfl | rfl | hp
  · have h : (1 : ENNReal) ≤ 0 := Fact.out
    norm_num at h
  · simp only [lp.norm_eq_ciSup, reflectLp_apply]
    exact (Equiv.neg ℤ).iSup_comp (g := fun x : ℤ => ‖f x‖)
  · rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    congr 1
    exact (Equiv.neg ℤ).tsum_eq (fun x => ‖f x‖ ^ p.toReal)

noncomputable def integerReflection {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (p : ENNReal) [Fact (1 ≤ p)] :
    ℓ^p(ℤ, E) ≃ₗᵢ[𝕜] ℓ^p(ℤ, E) where
  toFun := reflectLp
  invFun := reflectLp
  left_inv := reflectLp_involutive
  right_inv := reflectLp_involutive
  map_add' f g := by apply lp.ext; rfl
  map_smul' c f := by apply lp.ext; rfl
  norm_map' := reflectLp_norm

@[simp]
theorem integerReflection_apply {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (p : ENNReal) [Fact (1 ≤ p)]
    (f : ℓ^p(ℤ, E)) (x : ℤ) : integerReflection (𝕜 := 𝕜) p f x = f (-x) := rfl

def reflectedFinset (F : Finset ℤ) : Finset ℤ := F.image (fun x => -x)

@[simp]
theorem mem_reflectedFinset (F : Finset ℤ) (x : ℤ) :
    x ∈ reflectedFinset F ↔ -x ∈ F := by
  simp only [reflectedFinset, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨-x, hx, neg_neg x⟩

@[simp]
theorem reflectedFinset_involutive (F : Finset ℤ) :
    reflectedFinset (reflectedFinset F) = F := by
  ext x
  simp

@[simp]
theorem reflectedFinset_card (F : Finset ℤ) :
    (reflectedFinset F).card = F.card :=
  Finset.card_image_of_injective F neg_injective

@[simp]
theorem reflectedFinset_Icc (a b : ℤ) :
    reflectedFinset (Finset.Icc a b) = Finset.Icc (-b) (-a) := by
  ext x
  simp only [mem_reflectedFinset, Finset.mem_Icc]
  omega

@[simp]
theorem reflectLp_finiteIndicator (F : Finset ℤ) (p : ENNReal) :
    reflectLp (finiteIndicatorLp F p) = finiteIndicatorLp (reflectedFinset F) p := by
  apply lp.ext
  funext x
  simp [finiteIndicatorLp, finiteIndicator]

theorem reflectLp_finiteInput (F : Finset ℤ) (f : ℤ → ℂ) (p : ENNReal) :
    reflectLp (finiteInputLp F f p) =
      finiteInputLp (reflectedFinset F) (reflectSequence f) p := by
  apply lp.ext
  funext x
  simp only [reflectLp_apply, finiteInputLp_apply, mem_reflectedFinset,
    reflectSequence_apply]

end PrimeSquares
