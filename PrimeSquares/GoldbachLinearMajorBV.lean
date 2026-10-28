import PrimeSquares.GoldbachMajorFiniteErrorAbsorption

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_bv_aggregate_log_product {l : ℝ} (hl : 0<l) (C T : ℝ) :
    (l^C)^3*l^(-T)*l=l^(3*C-T+1) := by
  have he : (l^C)^3*l^(-T)=l^(3*C-T) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hl.le,←Real.rpow_add hl]
    congr 1
    ring
  rw [he,Real.rpow_add hl,Real.rpow_one]

/-- Complete source progression-error supremum bound from ordinary BV.
Every individual progression cutoff may vary independently. -/
theorem goldbach_linear_major_bombieri_vinogradov (HBV : RawPrimeBombieriVinogradovInput)
    {t C δ : ℝ} (ht : 0<t) (hC : 0≤C) (hδ : 0<δ) :
    ∃ B₀ K : ℝ,0≤B₀ ∧ 0<K ∧ ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      ∀ B L₀ : ℝ,B₀≤B → L₀<(N:ℝ)^(2-δ) →
      ∀ V : ℕ→ℝ,(∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L₀ →
        V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) →
      ∀ (q : ℕ) [NeZero q],(q:ℝ)≤(Real.log N)^C →
      ∀ a : ℕ×ℕ→ℕ,(∀ i∈goldbachCoefficientIndices L₀ V,(a i).Coprime i.2) →
      ∀ W : ℕ×ℕ→ℝ,(∀ i∈goldbachCoefficientIndices L₀ V,2≤W i) →
      ∀ (A : ℤ) (γ : ℝ),|γ|≤(Real.log N)^C/(N:ℝ)^2 →
      (∑ i∈goldbachCoefficientIndices L₀ V,
        ‖goldbachLinearMajorError N i.1 i.2 q (a i) A (W i) γ‖)≤
          K*(N:ℝ)^2*(Real.log N)^(-t) := by
  let T := t+3*C+2
  have hT : 0<T := by dsimp [T];linarith
  obtain ⟨Lb,M,X₀,hLb,hM,hX₀,hrows⟩ := goldbach_linear_major_bv_row HBV hT
  obtain ⟨N₁,hN₁,hparams⟩ := goldbach_bv_source_eventual_threshold (L:=Lb) hδ hX₀
  obtain ⟨N₂,hN₂,hfinite⟩ := goldbach_source_finite_error_absorbed hδ C t
  let B₀ := C+Lb+1
  let K := 1+3*(1+2*Real.pi)*M*δ^(-T)
  have hB₀ : 0≤B₀ := by dsimp [B₀];linarith
  have hK : 0<K := by dsimp [K];positivity
  refine ⟨B₀,K,hB₀,hK,max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro N hN B L₀ hB hL V hV q _ hqR a ha W hW A γ hγ
  have hNN₁ := (le_max_left N₁ N₂).trans hN
  have hNN₂ := (le_max_right N₁ N₂).trans hN
  obtain ⟨hlog,hbig,hstart⟩ := hparams N hNN₁
  obtain ⟨_,hfiniteN⟩ := hfinite N hNN₂
  have hNnat : 1≤N := by omega
  have hnR : (0:ℝ)<N := by exact_mod_cast hNnat
  have hlR : 0<Real.log N := by linarith
  have hR : 1≤(Real.log N)^C := Real.one_le_rpow hlog hC
  have hB0 : 0≤B := hB₀.trans hB
  have hpow : (N:ℝ)^(2-δ)≤(N:ℝ)^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hNnat : (1:ℝ)≤N) (by linarith : 2-δ≤(2:ℝ))
  let I := goldbachCoefficientIndices L₀ V
  let R := (Real.log N)^C
  have hrow (ℓ : ℕ) (hℓ : ℓ∈I.image Prod.fst) :
      (∑ k∈goldbachModuliAt I ℓ,‖goldbachLinearMajorError N ℓ k q (a (ℓ,k)) A (W (ℓ,k)) γ‖)≤
        (1+(q:ℝ))*((goldbachModuliAt I ℓ).card:ℝ)+
          (1+2*Real.pi)*R^3*(M*((N:ℝ)^2/ℓ)*(δ^(-T)*(Real.log N)^(-T))) := by
    obtain ⟨hℓpos,hℓL,_⟩ := goldbach_source_row_cutoffs L₀ V ℓ hℓ
    obtain ⟨hscale,_,hloglower,hlogupper⟩ := goldbach_progression_scale_logs N ℓ hNnat hℓpos δ (hℓL.trans hL)
    have hx : X₀≤(N:ℝ)^2/ℓ := hstart.trans hscale.le
    have hlogX : 0<Real.log ((N:ℝ)^2/ℓ) := Real.log_pos (by linarith)
    have hVR : V ℓ*R≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log ((N:ℝ)^2/ℓ))^(-Lb) :=
      goldbach_bv_log_level hlog hlogX hlogupper hLb hB hbig (hV ℓ hℓpos hℓL)
    have hKpos : ∀ k∈goldbachModuliAt I ℓ,0<k := by
      intro k hk
      exact ((mem_goldbachCoefficientIndices L₀ V ℓ k).mp ((mem_goldbachModuliAt I ℓ k).mp hk)).2.2.1
    have hlevel : ∀ k∈goldbachModuliAt I ℓ,
        (k.lcm q:ℝ)≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log ((N:ℝ)^2/ℓ))^(-Lb) := by
      intro k hk
      have hki := (mem_goldbachModuliAt I ℓ k).mp hk
      have hkV := ((mem_goldbachCoefficientIndices L₀ V ℓ k).mp hki).2.2.2
      exact goldbach_lcm_bv_level k q (hKpos k hk) (NeZero.pos q) hkV hqR hVR
    have hr := hrows q N ℓ hNnat hℓpos hx (goldbachModuliAt I ℓ) hKpos
      (fun k => a (ℓ,k)) (fun k hk => ha (ℓ,k) ((mem_goldbachModuliAt I ℓ k).mp hk))
      (fun k => W (ℓ,k)) (fun k hk => hW (ℓ,k) ((mem_goldbachModuliAt I ℓ k).mp hk))
      R hR hqR hlevel A γ hγ
    have hsave := goldbach_bv_log_saving hlR hδ hT.le hloglower
    have hs := mul_le_mul_of_nonneg_left hsave (by positivity : 0≤M*((N:ℝ)^2/ℓ))
    exact hr.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by positivity)))
  have hcard : (∑ ℓ∈I.image Prod.fst,((goldbachModuliAt I ℓ).card:ℝ))=(I.card:ℝ) := by
    have h := goldbach_index_row_sum I (fun _ => (1:ℝ))
    simpa only [sum_const,nsmul_eq_mul,mul_one] using h.symm
  have hscales : (∑ ℓ∈I.image Prod.fst,(N:ℝ)^2/ℓ)≤3*(N:ℝ)^2*Real.log N :=
    goldbach_source_row_scale_sum N hlog L₀ V (hL.le.trans hpow)
  have hfiniteBound : (1+(q:ℝ))*(I.card:ℝ)≤(N:ℝ)^2*(Real.log N)^(-t) := by
    have hb := hfiniteN L₀ B V hB0 hL hV
    have hfac : 1+(q:ℝ)≤2*R := by dsimp only [R];linarith
    exact (mul_le_mul_of_nonneg_right hfac (Nat.cast_nonneg _)).trans hb
  have hexp : 3*C-T+1= -t-1 := by dsimp [T];ring
  have hlogprod : R^3*(Real.log N)^(-T)*Real.log N=(Real.log N)^(-t-1) := by
    rw [goldbach_bv_aggregate_log_product hlR C T,hexp]
  have hsave : (Real.log N)^(-t-1)≤(Real.log N)^(-t) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by linarith)
  have hanalytic : (1+2*Real.pi)*R^3*M*δ^(-T)*(Real.log N)^(-T)*
      (∑ ℓ∈I.image Prod.fst,(N:ℝ)^2/ℓ)≤
        (3*(1+2*Real.pi)*M*δ^(-T))*(N:ℝ)^2*(Real.log N)^(-t) := by
    calc
      _≤(1+2*Real.pi)*R^3*M*δ^(-T)*(Real.log N)^(-T)*(3*(N:ℝ)^2*Real.log N) :=
        mul_le_mul_of_nonneg_left hscales (by dsimp only [R];positivity)
      _=(3*(1+2*Real.pi)*M*δ^(-T))*(N:ℝ)^2*(R^3*(Real.log N)^(-T)*Real.log N) := by ring
      _=(3*(1+2*Real.pi)*M*δ^(-T))*(N:ℝ)^2*(Real.log N)^(-t-1) := by rw [hlogprod]
      _≤_ := mul_le_mul_of_nonneg_left hsave (by positivity)
  change (∑ i∈I,‖goldbachLinearMajorError N i.1 i.2 q (a i) A (W i) γ‖)≤_
  rw [goldbach_index_row_sum I]
  calc
    _≤∑ ℓ∈I.image Prod.fst,((1+(q:ℝ))*((goldbachModuliAt I ℓ).card:ℝ)+
      (1+2*Real.pi)*R^3*(M*((N:ℝ)^2/ℓ)*(δ^(-T)*(Real.log N)^(-T)))) := sum_le_sum hrow
    _=(1+(q:ℝ))*(I.card:ℝ)+
        (1+2*Real.pi)*R^3*M*δ^(-T)*(Real.log N)^(-T)*
          (∑ ℓ∈I.image Prod.fst,(N:ℝ)^2/ℓ) := by
      rw [sum_add_distrib,←mul_sum,hcard,mul_sum]
      congr 1
      apply sum_congr rfl
      intro ℓ _
      ring
    _≤(N:ℝ)^2*(Real.log N)^(-t)+
        (3*(1+2*Real.pi)*M*δ^(-T))*(N:ℝ)^2*(Real.log N)^(-t) :=
      add_le_add hfiniteBound hanalytic
    _=K*(N:ℝ)^2*(Real.log N)^(-t) := by dsimp [K];ring

end PrimeSquares
