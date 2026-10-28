import PrimeSquares.GoldbachLinearResidueFibres

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachClosedLinearSum (k a ℓ : ℕ) (W ξ : ℝ) : ℂ :=
  ∑ n∈goldbachPrimeProgressionCutoff k a W,realFourierPhase (ξ*((ℓ*n:ℕ):ℝ))

noncomputable def goldbachGoodLinearSum (k q a ℓ : ℕ) (W ξ : ℝ) : ℂ :=
  ∑ n∈goldbachGoodLinearCutoff k q a W,realFourierPhase (ξ*((ℓ*n:ℕ):ℝ))

theorem goldbach_good_linear_model_error (k q a ℓ : ℕ) [NeZero k] [NeZero q]
    (ha : a.Coprime k) {W B : ℝ} (hW : 2≤W) (hB : 0≤B) (A : ℤ) (γ : ℝ)
    (herr : ∀ b∈goldbachMajorResidues k q a,∀ y∈Set.Icc 2 W,
      ‖(goldbachPrimeProgressionCount (k.lcm q) b y:ℂ)-goldbachPrimeProgressionModel (k.lcm q) y‖≤B) :
    ‖goldbachGoodLinearSum k q a ℓ W ((A:ℝ)/q+γ)-
      (upsilon q k (a:ℤ) (-((A:ZMod q)*(ℓ:ZMod q)))/(k.totient:ℂ))*
        goldbachLinearIntegral W ((ℓ:ℝ)*γ)‖≤
          (q:ℝ)*(B*(1+2*Real.pi*|((ℓ:ℝ)*γ)| *W)) := by
  classical
  let α : ZMod q := (A:ZMod q)*(ℓ:ZMod q)
  let J := goldbachLinearIntegral W ((ℓ:ℝ)*γ)
  have hm : (∑ b∈goldbachMajorResidues k q a,ZMod.stdAddChar (α*(b:ZMod q))*
      (((k.lcm q).totient:ℂ)⁻¹*J))=
      (upsilon q k (a:ℤ) (-α)/(k.totient:ℂ))*J := by
    calc
      _=(((k.lcm q).totient:ℂ)⁻¹*(∑ b∈goldbachMajorResidues k q a,
        ZMod.stdAddChar (α*(b:ZMod q))))*J := by
          rw [mul_sum,sum_mul]
          apply sum_congr rfl
          intro b _
          ring
      _=_ := by rw [goldbach_major_upsilon_identity k q a ha α]
  have he : goldbachGoodLinearSum k q a ℓ W ((A:ℝ)/q+γ)-
      (upsilon q k (a:ℤ) (-α)/(k.totient:ℂ))*J=
      ∑ b∈goldbachMajorResidues k q a,ZMod.stdAddChar (α*(b:ZMod q))*
        ((∑ n∈goldbachPrimeProgressionCutoff (k.lcm q) b W,
          realFourierPhase (((ℓ:ℝ)*γ)*(n:ℝ)))-((k.lcm q).totient:ℂ)⁻¹*J) := by
    rw [←hm,goldbachGoodLinearSum,goldbach_good_linear_residue_grouping k q a ℓ (by linarith) A γ]
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro b _
    dsimp only [α]
    ring
  change ‖goldbachGoodLinearSum k q a ℓ W ((A:ℝ)/q+γ)-
    (upsilon q k (a:ℤ) (-α)/(k.totient:ℂ))*J‖≤_
  rw [he]
  have hbudget : 0≤B*(1+2*Real.pi*|((ℓ:ℝ)*γ)| *W) := by positivity
  calc
    _≤∑ b∈goldbachMajorResidues k q a,‖ZMod.stdAddChar (α*(b:ZMod q))*
      ((∑ n∈goldbachPrimeProgressionCutoff (k.lcm q) b W,
        realFourierPhase (((ℓ:ℝ)*γ)*(n:ℝ)))-((k.lcm q).totient:ℂ)⁻¹*J)‖ := norm_sum_le _ _
    _≤∑ _b∈goldbachMajorResidues k q a,B*(1+2*Real.pi*|((ℓ:ℝ)*γ)| *W) := by
      apply sum_le_sum
      intro b hb
      rw [norm_mul,norm_stdAddChar,one_mul]
      exact goldbach_prime_linear_count_error (k.lcm q) b hW hB ((ℓ:ℝ)*γ) (herr b hb)
    _=((goldbachMajorResidues k q a).card:ℝ)*(B*(1+2*Real.pi*|((ℓ:ℝ)*γ)| *W)) := by
      rw [sum_const,nsmul_eq_mul]
    _≤_ := mul_le_mul_of_nonneg_right (by exact_mod_cast goldbach_major_residues_card k q a) hbudget

theorem goldbach_linear_nonunit_card (k q a : ℕ) (ha : a.Coprime k) {W : ℝ} (hW : 0≤W)
    (hq : 0<q) :
    ((goldbachPrimeProgressionCutoff k a W).filter (fun n => ¬n.Coprime (k.lcm q))).card≤q := by
  classical
  have hs : (goldbachPrimeProgressionCutoff k a W).filter (fun n => ¬n.Coprime (k.lcm q))⊆Icc 1 q := by
    intro n hn
    obtain ⟨hp,_,hres⟩ := (mem_goldbachPrimeProgressionCutoff hW).mp (mem_filter.mp hn).1
    have hnK : n.Coprime k := by
      change n.gcd k=1
      exact (show Nat.ModEq k n a from hres).gcd_eq.trans ha
    have hnq : ¬n.Coprime q := by
      intro hc
      exact (mem_filter.mp hn).2
        (Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul k q) (hnK.mul_right hc))
    have hd : n∣q := by
      by_contra hd
      exact hnq (hp.coprime_iff_not_dvd.mpr hd)
    exact mem_Icc.mpr ⟨hp.one_lt.le,Nat.le_of_dvd hq hd⟩
  simpa only [Nat.card_Icc,Nat.add_sub_cancel] using card_le_card hs

theorem goldbach_linear_nonunit_error (k q a ℓ : ℕ) (ha : a.Coprime k)
    {W : ℝ} (hW : 0≤W) (hq : 0<q) (ξ : ℝ) :
    ‖goldbachClosedLinearSum k a ℓ W ξ-goldbachGoodLinearSum k q a ℓ W ξ‖≤q := by
  classical
  have hs : goldbachClosedLinearSum k a ℓ W ξ=
      goldbachGoodLinearSum k q a ℓ W ξ+
      ∑ n∈(goldbachPrimeProgressionCutoff k a W).filter (fun n => ¬n.Coprime (k.lcm q)),
        realFourierPhase (ξ*((ℓ*n:ℕ):ℝ)) := by
    exact (sum_filter_add_sum_filter_not (goldbachPrimeProgressionCutoff k a W)
      (fun n => n.Coprime (k.lcm q)) _).symm
  rw [hs,add_sub_cancel_left]
  calc
    _≤∑ n∈(goldbachPrimeProgressionCutoff k a W).filter (fun n => ¬n.Coprime (k.lcm q)),
      ‖realFourierPhase (ξ*((ℓ*n:ℕ):ℝ))‖ := norm_sum_le _ _
    _=(((goldbachPrimeProgressionCutoff k a W).filter (fun n => ¬n.Coprime (k.lcm q))).card:ℝ) := by
      simp only [realFourierPhase_norm,sum_const,nsmul_eq_mul,mul_one]
    _≤_ := by exact_mod_cast goldbach_linear_nonunit_card k q a ha hW hq

theorem goldbach_closed_linear_fourier (k a ℓ : ℕ) (W ξ : ℝ) :
    goldbachClosedLinearSum k a ℓ W ξ=
      ∑ n∈goldbachPrimeProgressionCutoff k a W,fourier ((ℓ*n:ℕ):ℤ) (ξ:PrimeCircle) := by
  simp only [goldbachClosedLinearSum,goldbach_positive_linear_character]

theorem goldbach_linear_major_from_counts (N k q a ℓ : ℕ) [NeZero k] [NeZero q]
    (hℓ : 0<ℓ) (ha : a.Coprime k) {W B : ℝ} (hW : 2≤W)
    (hWX : W≤(N:ℝ)^2/ℓ) (hB : 0≤B) (A : ℤ) (γ : ℝ)
    (herr : ∀ b∈goldbachMajorResidues k q a,∀ y∈Set.Icc 2 W,
      ‖(goldbachPrimeProgressionCount (k.lcm q) b y:ℂ)-goldbachPrimeProgressionModel (k.lcm q) y‖≤B) :
    ‖goldbachProgressionPolynomial N ℓ k a W (((A:ℝ)/q+γ:ℝ):PrimeCircle)-
      (upsilon q k (a:ℤ) (-((A:ZMod q)*(ℓ:ZMod q)))/(k.totient:ℂ))*
        goldbachLinearIntegral W ((ℓ:ℝ)*γ)‖≤
          1+(q:ℝ)+(q:ℝ)*(B*(1+2*Real.pi*|((ℓ:ℝ)*γ)| *W)) := by
  let ξ := (A:ℝ)/q+γ
  let F := goldbachProgressionPolynomial N ℓ k a W (ξ:PrimeCircle)
  let C := goldbachClosedLinearSum k a ℓ W ξ
  let G := goldbachGoodLinearSum k q a ℓ W ξ
  let M := (upsilon q k (a:ℤ) (-((A:ZMod q)*(ℓ:ZMod q)))/(k.totient:ℂ))*
    goldbachLinearIntegral W ((ℓ:ℝ)*γ)
  have hFC : ‖F-C‖≤1 := by
    dsimp only [F,C]
    rw [norm_sub_rev,goldbach_closed_linear_fourier]
    exact goldbach_progression_endpoint_error N ℓ k a hℓ (by linarith) hWX (ξ:PrimeCircle)
  have hCG : ‖C-G‖≤q := goldbach_linear_nonunit_error k q a ℓ ha (by linarith) (NeZero.pos q) ξ
  have hGM := goldbach_good_linear_model_error k q a ℓ ha hW hB A γ herr
  change ‖F-M‖≤_
  have he : F-M=(F-C)+(C-G)+(G-M) := by ring
  rw [he]
  exact (norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add hFC hCG)) hGM)

end PrimeSquares
