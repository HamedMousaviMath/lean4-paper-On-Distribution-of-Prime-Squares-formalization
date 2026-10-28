import PrimeSquares.GoldbachQuantitativeExceptionalSet

set_option autoImplicit false
open Finset Filter
namespace PrimeSquares

noncomputable def goldbachAdmissibleBelow (X : ℝ) : Finset ℕ :=
  (range (Nat.ceil X)).filter (fun n=>n%24=12)

noncomputable def goldbachSourceExceptionalSet (X : ℝ) : Finset ℕ :=
  goldbachExceptionalSet (goldbachAdmissibleBelow X)

theorem goldbach_good_representation_iff (n : ℕ) :
    (goldbachGoodRepresentations n).Nonempty ↔
      ∃ a b p : ℕ,a.Coprime b ∧ p.Prime ∧ (a^2+b^2+1).Prime ∧
        a^2+b^2+p^2+1=n := by
  classical
  constructor
  · rintro ⟨r,hr⟩
    obtain ⟨hr,hprim⟩ := mem_filter.mp hr
    obtain ⟨hrp,p,hp,he⟩ := mem_goldbachRepresentations.mp hr
    obtain ⟨a,b,hab,hc⟩ := hprim
    have hr2 := hrp.two_le
    have heq : a^2+b^2+1=r := by omega
    refine ⟨a,b,p,hc,hp,by simpa only [heq] using hrp,?_⟩
    nlinarith only [he,heq]
  · rintro ⟨a,b,p,hc,hp,hr,he⟩
    refine ⟨a^2+b^2+1,mem_filter.mpr ⟨?_,?_⟩⟩
    · apply mem_goldbachRepresentations.mpr
      exact ⟨hr,p,hp,by nlinarith only [he]⟩
    · exact ⟨a,b,by omega,hc⟩

theorem goldbach_source_exceptional_membership (X : ℝ) (n : ℕ) :
    n∈goldbachSourceExceptionalSet X ↔
      0<n ∧ (n:ℝ)<X ∧ n%24=12 ∧
        ¬∃ a b p : ℕ,a.Coprime b ∧ p.Prime ∧ (a^2+b^2+1).Prime ∧
          a^2+b^2+p^2+1=n := by
  classical
  simp only [goldbachSourceExceptionalSet,goldbachExceptionalSet,goldbachAdmissibleBelow,
    mem_filter,mem_range,Nat.lt_ceil]
  have hn : n%24=12→0<n := by omega
  rw [←goldbach_good_representation_iff]
  simp only [Finset.card_eq_zero,Finset.not_nonempty_iff_eq_empty]
  tauto

theorem goldbach_ceiling_square_geometry (X : ℝ) (hX : 4≤X) :
    let N := Nat.ceil (Real.sqrt X)
    X≤(N:ℝ)^2 ∧ (N:ℝ)^2≤4*X ∧
      0<Real.log (N:ℝ) ∧ Real.log X/2≤Real.log (N:ℝ) := by
  have hX0 : 0≤X := by linarith
  have hs0 := Real.sqrt_nonneg X
  have hs2 := Real.sq_sqrt hX0
  have hs : 2≤Real.sqrt X := by nlinarith only [hs0,hs2,hX]
  have hceil := Nat.le_ceil (Real.sqrt X)
  have hceilU := Nat.ceil_lt_add_one hs0
  have hNpos : (1:ℝ)<Nat.ceil (Real.sqrt X) := by linarith
  refine ⟨?_,?_,Real.log_pos hNpos,?_⟩
  · nlinarith only [hceil,hs2,hs0]
  · nlinarith only [hceilU,hs2,hs0,hs,show (0:ℝ)≤Nat.ceil (Real.sqrt X) by positivity]
  · have hh := Real.log_le_log (by linarith : 0<Real.sqrt X) hceil
    simpa only [Real.log_sqrt hX0] using hh

theorem goldbach_real_cutoff_from_square_bound (A D : ℝ) (hA : 0<A) (hD : 0<D)
    (hbound : ∀ᶠ N : ℕ in atTop,
      ((goldbachExceptionalSet (goldbachAdmissibleNumbers N)).card:ℝ)≤
        D*(N:ℝ)^2*(Real.log N)^(-A)) :
    ∀ᶠ X : ℝ in atTop,((goldbachSourceExceptionalSet X).card:ℝ)≤
      (4*D*(2:ℝ)^A)*X*(Real.log X)^(-A) := by
  classical
  have hNlim : Tendsto (fun X : ℝ=>Nat.ceil (Real.sqrt X)) atTop atTop :=
    tendsto_nat_ceil_atTop.comp Real.tendsto_sqrt_atTop
  filter_upwards [hNlim.eventually hbound,eventually_ge_atTop (4:ℝ)] with X hBound hX
  let N := Nat.ceil (Real.sqrt X)
  obtain ⟨hXN,hNX,hlogN,hlogs⟩ := goldbach_ceiling_square_geometry X hX
  have hsub : goldbachSourceExceptionalSet X⊆goldbachExceptionalSet (goldbachAdmissibleNumbers N) := by
    intro n hn
    obtain ⟨hna,hbad⟩ := mem_filter.mp hn
    obtain ⟨hnX,hn24⟩ := mem_filter.mp hna
    have hnXR : (n:ℝ)<X := Nat.lt_ceil.mp (mem_range.mp hnX)
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_range.mpr ?_,hn24⟩,hbad⟩
    exact_mod_cast hnXR.trans_le hXN
  have hL : 0<Real.log X := Real.log_pos (by linarith : 1<X)
  have hpow := Real.rpow_le_rpow_of_nonpos (by linarith : 0<Real.log X/2) hlogs (by linarith : -A≤0)
  have hscale : (Real.log X/2)^(-A)=(2:ℝ)^A*(Real.log X)^(-A) := by
    rw [Real.div_rpow hL.le (by norm_num) (-A),Real.rpow_neg (by norm_num : (0:ℝ)≤2),div_inv_eq_mul]
    ring
  calc
    _≤((goldbachExceptionalSet (goldbachAdmissibleNumbers N)).card:ℝ) := by exact_mod_cast card_le_card hsub
    _≤D*(N:ℝ)^2*(Real.log N)^(-A) := hBound
    _≤D*(4*X)*(Real.log X/2)^(-A) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hNX hD.le) hpow
        (Real.rpow_nonneg hlogN.le _) (by positivity)
    _=_ := by rw [hscale];ring

/-- The manuscript's full quantitative exceptional-set conclusion, at every
large real cutoff X, conditional only on independent general classical inputs. -/
theorem goldbach_headline_theorem (H : GoldbachSection11Inputs)
    (Htwo : PrimitiveTwoSquaresCriterion) (ψ : SchwartzMap ℝ ℝ) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x|→ψ x=0) (A : ℝ) (hA : 0<A) :
    ∃ D : ℝ,0<D ∧ ∀ᶠ X : ℝ in atTop,
      ((goldbachSourceExceptionalSet X).card:ℝ)≤D*X*(Real.log X)^(-A) := by
  obtain ⟨D,hD,hBound⟩ := goldbach_quantitative_exceptional_set_squares H Htwo ψ hψ hsψ A hA
  exact ⟨4*D*(2:ℝ)^A,by positivity,goldbach_real_cutoff_from_square_bound A D hA hD hBound⟩

end PrimeSquares
