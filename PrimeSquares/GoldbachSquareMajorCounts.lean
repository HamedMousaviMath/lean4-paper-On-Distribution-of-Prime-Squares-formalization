import PrimeSquares.GoldbachPrimePhaseErrors
import PrimeSquares.SquareMajorArcAssembly

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_prime_positive_symbol (U x : ℝ) :
    finiteSquareSymbol (goldbachPrimeCutoff U) 1 (fun _ => 1) ((-x:ℝ):PrimeCircle)=
      goldbachPrimeSquarePolynomial U (x:PrimeCircle) := by
  rw [finiteSquareSymbol_apply]
  simp only [Complex.ofReal_one,one_mul]
  change (∑ n∈goldbachPrimeCutoff U,negativeFourierCharacter ((n:ℤ)^2) ((-x:ℝ):PrimeCircle))=_
  simp only [goldbachPrimeSquarePolynomial,ContinuousMap.sum_apply]
  apply sum_congr rfl
  intro n _
  rw [←quadraticOscillation_nat,goldbach_positive_quadratic_character]

theorem goldbach_prime_residue_cutoff (q : ℕ) [NeZero q] (r : ZMod q) (U : ℝ) :
    goldbachPrimeProgressionCutoff q r.val U=
      (goldbachPrimeCutoff U).filter (fun n : ℕ => (n:ZMod q)=r) := by
  classical
  ext n
  simp only [goldbachPrimeProgressionCutoff,mem_filter]
  have he : n%q=r.val%q ↔ (n:ZMod q)=r := by
    rw [Nat.mod_eq_of_lt (ZMod.val_lt r)]
    simpa only [ZMod.val_natCast] using (ZMod.val_injective q).eq_iff (a:=(n:ZMod q)) (b:=r)
  rw [he]

theorem goldbach_square_prime_residue_sum (q : ℕ) [NeZero q] (r : ZMod q) (U γ : ℝ) :
    squareResidueSum (goldbachPrimeCutoff U) q r (fun _ => 1) ((-γ:ℝ):PrimeCircle)=
      ∑ n∈goldbachPrimeProgressionCutoff q r.val U,quadraticOscillation (-γ) n := by
  rw [goldbach_prime_residue_cutoff]
  simp only [squareResidueSum,Complex.ofReal_one,one_mul,quadraticOscillation_nat]

theorem goldbach_prime_nonunit_card (q : ℕ) [NeZero q] (U : ℝ) :
    ((goldbachPrimeCutoff U).filter (fun n => ¬n.Coprime q)).card≤q := by
  classical
  have hs : (goldbachPrimeCutoff U).filter (fun n => ¬n.Coprime q)⊆Icc 1 q := by
    intro n hn
    have hp : n.Prime := (mem_filter.mp (mem_filter.mp hn).1).2
    have hd : n∣q := by
      by_contra hd
      exact (mem_filter.mp hn).2 (hp.coprime_iff_not_dvd.mpr hd)
    exact mem_Icc.mpr ⟨hp.one_lt.le,Nat.le_of_dvd (NeZero.pos q) hd⟩
  simpa only [Nat.card_Icc,Nat.add_sub_cancel] using card_le_card hs

theorem goldbach_prime_nonunit_symbol (q : ℕ) [NeZero q] (U : ℝ) (θ : PrimeCircle) :
    ‖finiteSquareSymbol ((goldbachPrimeCutoff U).filter (fun n => ¬n.Coprime q))
      1 (fun _ => 1) θ‖≤q := by
  have h := finiteSquareSymbol_norm_le_mass
    ((goldbachPrimeCutoff U).filter (fun n => ¬n.Coprime q)) (by norm_num : (0:ℝ)≤1)
    (fun _ => 1) (fun _ _ => by norm_num) θ
  simp only [sum_const,nsmul_eq_mul,mul_one,one_mul] at h
  exact h.trans (by exact_mod_cast goldbach_prime_nonunit_card q U)

/-- The exact source square major-arc model follows from ordinary reduced
prime-count discrepancies; no weighted square estimate is an assumption. -/
theorem goldbach_square_major_from_counts (q : ℕ) [NeZero q] (a : ℤ)
    {U B : ℝ} (hU : 2≤U) (hB : 0≤B) (γ : ℝ)
    (herr : ∀ u : (ZMod q)ˣ,∀ t∈Set.Icc 2 U,
      ‖(goldbachPrimeProgressionCount q (u:ZMod q).val t:ℂ)-goldbachPrimeProgressionModel q t‖≤B) :
    ‖goldbachPrimeSquarePolynomial U (((a:ℝ)/q+γ:ℝ):PrimeCircle)-
      principalSquareSum q (-(a:ZMod q))*goldbachSquareIntegral U γ‖≤
        (q:ℝ)+(q.totient:ℝ)*(B*(1+4*Real.pi*|γ| *U^2)) := by
  have h := finiteSquareSymbol_majorArc_error_norm (goldbachPrimeCutoff U) 1 (fun _ => 1)
    q (1:DirichletCharacter ℂ q) (-a) (goldbachSquareIntegral U γ) 0 ((-γ:ℝ):PrimeCircle)
  have he : ((((-a:ℤ):ℝ)/q:ℝ):PrimeCircle)+((-γ:ℝ):PrimeCircle)=
      ((-((a:ℝ)/q+γ):ℝ):PrimeCircle) := by
    rw [←AddCircle.coe_add]
    congr 1
    push_cast
    ring
  rw [he,goldbach_prime_positive_symbol] at h
  simp only [Int.cast_neg,mul_zero,sub_zero] at h
  apply h.trans
  apply add_le_add (goldbach_prime_nonunit_symbol q U _)
  calc
    _≤∑ _u : (ZMod q)ˣ,B*(1+4*Real.pi*|γ| *U^2) := by
      apply sum_le_sum
      intro u _
      simpa only [squareResidueModelError,Complex.ofReal_one,one_mul,mul_zero,sub_zero,
        goldbach_square_prime_residue_sum] using goldbach_prime_quadratic_count_error
          q (u:ZMod q).val hU hB γ (herr u)
    _=(q.totient:ℝ)*(B*(1+4*Real.pi*|γ| *U^2)) := by
      simp only [sum_const,card_univ,ZMod.card_units_eq_totient,nsmul_eq_mul]

end PrimeSquares
