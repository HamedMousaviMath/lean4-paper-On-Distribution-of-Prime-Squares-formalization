import PrimeSquares.GoldbachTruncationSets

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachTruncatedBadValues (n : ℕ) (z : ℝ) : Finset ℕ :=
  (goldbachTruncatedBad n z).image (fun r => r-1)

theorem goldbachTruncatedBadValues_card (n : ℕ) (z : ℝ) :
    (goldbachTruncatedBadValues n z).card=(goldbachTruncatedBad n z).card := by
  classical
  apply card_image_iff.mpr
  intro r hr t ht he
  change r-1=t-1 at he
  have hr' := (mem_goldbachRepresentations.mp (mem_filter.mp (mem_filter.mp hr).1).1).1.two_le
  have ht' := (mem_goldbachRepresentations.mp (mem_filter.mp (mem_filter.mp ht).1).1).1.two_le
  omega

/-- The signed truncation error is nonnegative and at most the explicit divisor envelope. -/
theorem goldbach_truncation_exact_error (H : PrimitiveTwoSquaresCriterion)
    {N n : ℕ} (hn : 12<n) (hres : n%24=12) (hsize : n≤N^2)
    {z : ℝ} (hz : 1≤z) (hlarge : (N:ℝ)^2<z^4) :
    ∃ e : ℕ,e≤(n-1).primeFactors.card ∧
      (goldbachSiftedValues n z).card=
        (goldbachGoodRepresentations n).card+(goldbachTruncatedBadValues n z).card+e := by
  classical
  let S := goldbachSifted n z
  let G := goldbachGoodRepresentations n
  let T := goldbachTruncatedBad n z
  have hGS : G⊆S := goldbach_good_subset_sifted H hn hres z
  have hTS : T⊆S := goldbachTruncatedBad_subset_sifted
  have hUS : G∪T⊆S := union_subset hGS hTS
  have hdisj : Disjoint G T := disjoint_left.mpr (fun r hr ht => goldbachTruncatedBad_not_good H ht hr)
  have hX : S\(G∪T)⊆goldbachDivisorExceptions n := by
    intro r hr
    obtain ⟨hrS,hrU⟩ := mem_sdiff.mp hr
    by_contra hE
    have hrT := goldbach_sifted_bad_factorization H (by omega : 2≤n) hsize hz hlarge hrS
      (fun hrG => hrU (mem_union_left _ hrG)) hE
    exact hrU (mem_union_right _ hrT)
  refine ⟨(S\(G∪T)).card,(card_le_card hX).trans (goldbachDivisorExceptions_card n),?_⟩
  rw [goldbachSiftedValues_card,goldbachTruncatedBadValues_card]
  have hh := card_sdiff_add_card_eq_card hUS
  rw [card_union_of_disjoint hdisj] at hh
  dsimp [S,G,T] at hh ⊢
  omega

theorem goldbach_truncation_scale {N : ℕ} (hN : 2≤N) {α : ℝ} (hα1 : 1<α) (hα2 : α<2) :
    1≤(N:ℝ)^(1/α) ∧ (N:ℝ)^2<((N:ℝ)^(1/α))^4 := by
  have hNR : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hα0 : 0<α := by linarith
  refine ⟨Real.one_le_rpow hNR.le (by positivity),?_⟩
  calc
    (N:ℝ)^2=(N:ℝ)^(2:ℝ) := by norm_num
    _<(N:ℝ)^(4/α) := Real.rpow_lt_rpow_of_exponent_lt hNR ((lt_div_iff₀ hα0).mpr (by linarith))
    _=((N:ℝ)^(1/α))^4 := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : (0:ℝ)≤N)]
      congr 1
      ring

/-- The full printed asymptotic equality, with an explicit bounded error witness. -/
theorem goldbach_truncationT (H : PrimitiveTwoSquaresCriterion) {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ N n : ℕ,2≤N → 12<n → n%24=12 → n≤N^2 →
      ∀ α : ℝ,1<α → α<2 → ∃ e : ℕ,(e:ℝ)≤K*(N:ℝ)^ε ∧
        (goldbachSiftedValues n ((N:ℝ)^(1/α))).card=
          (goldbachGoodRepresentations n).card+
          (goldbachTruncatedBadValues n ((N:ℝ)^(1/α))).card+e := by
  obtain ⟨K,hK,herr⟩ := goldbach_prime_divisor_power_error hε
  refine ⟨K,hK,?_⟩
  intro N n hN hn hres hsize α hα1 hα2
  obtain ⟨hz,hlarge⟩ := goldbach_truncation_scale hN hα1 hα2
  obtain ⟨e,he,hcount⟩ := goldbach_truncation_exact_error H hn hres hsize hz hlarge
  exact ⟨e,(show (e:ℝ)≤((n-1).primeFactors.card:ℝ) by exact_mod_cast he).trans
    (herr N n (by omega) (by omega) (by omega)),hcount⟩

end PrimeSquares
