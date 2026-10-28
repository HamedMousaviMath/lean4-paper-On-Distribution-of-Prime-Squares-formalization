import PrimeSquares.RawPageUniqueness

namespace PrimeSquares

noncomputable def optionPageConductor (fallback : ℕ) (D : Option PageZeroDatum) : ℕ :=
  match D with | none => fallback | some E => E.conductor

noncomputable def optionPageCharacter (fallback : ℕ) (D : Option PageZeroDatum) :
    DirichletCharacter ℂ (optionPageConductor fallback D) :=
  match D with | none => 1 | some E => E.character

noncomputable def optionPageBeta (D : Option PageZeroDatum) : ℝ :=
  match D with | none => 1 | some E => E.beta

theorem optionPageBeta_nonneg (D : Option PageZeroDatum) : 0 ≤ optionPageBeta D := by
  cases D with
  | none => norm_num [optionPageBeta]
  | some E => exact E.beta_pos.le

theorem optionPageBeta_le_one (D : Option PageZeroDatum) : optionPageBeta D ≤ 1 := by
  cases D with
  | none => exact le_refl _
  | some E => exact E.beta_lt_one.le

def PageClassOccupied (E : ℕ → Option PageZeroDatum) (i : ℕ) : Prop :=
  ∃ D : PageZeroDatum,(∃ j,E j=some D) ∧ Nat.log2 D.conductor=i

noncomputable def pageClassRepresentative (E : ℕ → Option PageZeroDatum) (i : ℕ) : Option PageZeroDatum := by
  classical
  exact if h : PageClassOccupied E i then some (Classical.choose h) else none

theorem pageClassRepresentative_bin (E : ℕ → Option PageZeroDatum) (i : ℕ) (D : PageZeroDatum)
    (h : pageClassRepresentative E i=some D) : Nat.log2 D.conductor=i := by
  classical
  by_cases hoc : PageClassOccupied E i
  · have he : Classical.choose hoc=D := Option.some.inj (by simpa only [pageClassRepresentative,dite_eq_left hoc] using h)
    rw [←he]
    exact (Classical.choose_spec hoc).2
  · simp only [pageClassRepresentative,dite_eq_right hoc] at h
    cases h

theorem pageClassRepresentative_eq {c : ℝ} (hc : 0<c) (hPage : RawPageUniquenessInput c)
    (E : ℕ → Option PageZeroDatum)
    (hE : ∀ j D,E j=some D → PageConductorEligible c D)
    (j : ℕ) (D : PageZeroDatum) (hj : E j=some D) :
    pageClassRepresentative E (Nat.log2 D.conductor)=some D := by
  classical
  have hoc : PageClassOccupied E (Nat.log2 D.conductor) := ⟨D,⟨j,hj⟩,rfl⟩
  obtain ⟨⟨j',hj'⟩,hb⟩ := Classical.choose_spec hoc
  have heq := page_dyadic_uniqueness hc hPage (Classical.choose hoc) D
    (hE j' _ hj') (hE j D hj) hb
  simp only [pageClassRepresentative,dite_eq_left hoc,heq]

noncomputable def pageClassConductor (E : ℕ → Option PageZeroDatum) (i : ℕ) : ℕ :=
  optionPageConductor (2^i) (pageClassRepresentative E i)

noncomputable def pageClassCharacter (E : ℕ → Option PageZeroDatum) (i : ℕ) :
    DirichletCharacter ℂ (pageClassConductor E i) :=
  optionPageCharacter (2^i) (pageClassRepresentative E i)

theorem pageClassConductor_lower (E : ℕ → Option PageZeroDatum) (i : ℕ) :
    2^i ≤ pageClassConductor E i := by
  cases h : pageClassRepresentative E i with
  | none => simp only [pageClassConductor,h,optionPageConductor,le_refl]
  | some D =>
    have hb := pageClassRepresentative_bin E i D h
    have hq : D.conductor ≠ 0 := by have h := D.conductor_two;omega
    have hlo := ((Nat.log2_eq_iff hq).mp hb).1
    simpa only [pageClassConductor,h,optionPageConductor] using hlo

theorem pageClassCharacter_quadratic (E : ℕ → Option PageZeroDatum) (i : ℕ) :
    (pageClassCharacter E i).IsQuadratic := by
  change (optionPageCharacter (2^i) (pageClassRepresentative E i)).IsQuadratic
  cases h : pageClassRepresentative E i with
  | none =>
    change (1 : DirichletCharacter ℂ (2^i)).IsQuadratic
    exact MulChar.isQuadratic_iff_sq_eq_one.mpr (by simp)
  | some D => exact D.quadratic

theorem pageSourceRegion_family_eligible {c : ℝ} (hc : 0<c) (R : ℕ → ℝ)
    (E : ℕ → Option PageZeroDatum)
    (hE : ∀ j D,E j=some D → (D.conductor : ℝ) ≤ R j ∧ 1-(c/2)/Real.log (R j)<D.beta) :
    ∀ j D,E j=some D → PageConductorEligible c D := by
  intro j D hj
  exact page_source_region_eligible hc D (hE j D hj).1 (hE j D hj).2

end PrimeSquares
