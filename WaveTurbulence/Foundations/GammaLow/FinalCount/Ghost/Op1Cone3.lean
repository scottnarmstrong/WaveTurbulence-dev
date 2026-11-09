/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Op1Cone2
/-! **L6E2, part 3: `prop94_vine_all_gamma_cone`** — M1-R2 Theorem 6.1 (e) at an Operation-1 creation step.

An Op-1 removal with `ΔF = 0` (`Step1.VineCut γ M`) that is the creation step `s(P)` of `k ≤ 2` NC critical pairs (the
later ghosts are joints of the removed object, `κ = 0`, critical label `Rg`, and the joint gap lies in the creation
cone: `JointCone`) has L6-STEP1's Step-1 deviation (`Step1.prop94_vine_all_gamma`) with the extra factor
`3·5^d · L^{-5ηk}`. One cone covers both joints (common gap `±r`), so `k = 2` costs nothing more (NOTES §6 (e)).
* `prop94_vine_final_cone` (single vine), `prop94_hyper_final_cone` (hyper object), `prop94_vine_double_cone` (two double
  bonds): the deviations with the count constant times `coneX d L η` (copies of L6-STEP1's `prop94_vine_final`,
  `prop94_hyper_final`, `prop94_vine_double_full` with the cone counts of `Op1Cone2`);
* **`prop94_vine_all_cone`**, **`prop94_vine_all_gamma_cone`**: the form for L6's item I. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount

variable {d : ℕ}

theorem coneX_le_transfer (d : ℕ) {L η : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η) (hd : 3 ≤ d) (k : ℕ) (hk : k ≤ 2) :
    coneX d L η ≤ 3 * 5 ^ d * L ^ (-5 * η * (k : ℝ)) := by
  have h1 := coneX_le d hL hη hd
  have h2 := rpow_le_transfer hL hη k hk
  calc coneX d L η ≤ 3 * 5 ^ d * L ^ (-12 * η) := h1
    _ ≤ 3 * 5 ^ d * L ^ (-5 * η * (k : ℝ)) := by gcongr

theorem crit_theta {L γ η R : ℝ} (hL : 1 ≤ L) (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hη1 : 200 * η ≤ γ)
    (hη2 : 200 * η ≤ 1 - γ) (hcrit : Crit L γ η R) : 1 ≤ L ^ (-6 * η) * (2 * R * L) :=
  theta_rho_ge_one hL hγ.1 hγ.2 hη hη1 hη2 hcrit

theorem two_R_L {L R : ℝ} (hL : 0 < L) (hRl : L⁻¹ ≤ R) : 1 ≤ 2 * R * L := by
  have := mul_le_mul_of_nonneg_right hRl hL.le
  rw [inv_mul_cancel₀ hL.ne'] at this; linarith

/-- **A single vine with the creation cone** (cf. L6-STEP1's `prop94_vine_final`). -/
theorem prop94_vine_final_cone {g : ℝ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cf C₂ : ℝ, 0 ≤ Cf ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ → 200 * η ≤ γ → 200 * η ≤ 1 - γ →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : Step1.VineCut g M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) → Step1.Charted M K.C.atoms K.C.upper K.C.lower →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents →
        ∀ (R : ℝ), L⁻¹ ≤ R → R ≤ L ^ (-γ + η) → Crit L γ η R →
        (∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * R) → JointCone K L γ δ η w Adm →
        VineCount.DecScale M L w Adm (Step1.VCLadderScale K L w P) →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Step1.Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cf * coneX d L η * (2 ^ d * (((4 + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (4 + 8 + 1))) *
            excessRHS L γ η [(R, 0), (R, 0)] 0 0)) := by
  obtain ⟨Cf, C₂, hCf, hC₂, hmain⟩ := vine_count_cone (g := g) hd hγ
  refine ⟨Cf, C₂, hCf, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hcnt⟩ := hmain δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η hC₁ hη hη1 hηγ h200a h200b => ?_⟩
  intro V D _ _ _ M K hMol hM hvine w Adm Adm' hAdm' P hP0 hP1 hP2 hF R hRl hRu hcrit hgap hcone hscale
  have hL1 : Real.exp 1 ≤ L := hL₀.trans hL
  have hL1' : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL1
  have hL0 : 0 < L := by linarith
  have hR0 : 0 < R := lt_of_lt_of_le (inv_pos.mpr hL0) hRl
  have hcount := hcnt L hL M K hMol hM hvine w Adm P hP0 hscale η (2 * R) (two_R_L hL0 hRl)
    (crit_theta hL1' hγ hη h200a h200b hcrit) hgap hcone
  obtain ⟨hbc, hm⟩ := Step1.vine_bonds_of_vine K hvine
  exact Step1.prop94_vine_single' K hd hM L γ δ C₁ C₂ η w Adm Adm' hAdm' P hL1 hδ.1 (hC₂.trans hC₁) (by linarith)
    hC₁ hP0 hP1 hP2 hη hη1 hηγ hF hbc hm R hR0.le hRu 0 (2 * R) (Or.inl ⟨rfl, rfl⟩) (Cf * coneX d L η)
    (mul_nonneg hCf (coneX_nonneg d hL0)) 4 hcount

/-- **A hyper object with the creation cone** (cf. L6-STEP1's `prop94_hyper_final`). -/
theorem prop94_hyper_final_cone {g : ℝ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cf C₂ : ℝ, 0 ≤ Cf ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ → 200 * η ≤ γ → 200 * η ≤ 1 - γ →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : Step1.VineCut g M)
        (R : Src.HyperLikeRealization g M K.C.atoms K.C.upper K.C.lower) (_h : K.C.shape = .hyper R),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) →
        Step1.Charted (Molecule.eraseBond M R.added) K.C.atoms K.C.upper K.C.lower →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        VineCount.DecScale M L w Adm (VineCount.SourceLadderGaps M L w P) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents →
        ∀ (Rg : ℝ), L⁻¹ ≤ Rg → Rg ≤ L ^ (-γ + η) → Crit L γ η Rg →
        (∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * Rg) → JointCone K L γ δ η w Adm →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Step1.Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cf * coneX d L η * (2 ^ d * (((4 + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (4 + 8 + 1))) *
            excessRHS L γ η [(Rg, 0), (Rg, 0)] 0 0)) := by
  obtain ⟨Cf, C₂, hCf, hC₂, hmain⟩ := hyper_count_cone (g := g) hd hγ
  refine ⟨Cf, C₂, hCf, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hcnt⟩ := hmain δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η hC₁ hη hη1 hηγ h200a h200b => ?_⟩
  intro V D _ _ _ M K R h hMol hM hvine w Adm Adm' hAdm' P hP0 hAdm hP1 hP2 hF Rg hRl hRu hcrit hgap hcone
  have hL1 : Real.exp 1 ≤ L := hL₀.trans hL
  have hL1' : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL1
  have hL0 : 0 < L := by linarith
  have hR0 : 0 < Rg := lt_of_lt_of_le (inv_pos.mpr hL0) hRl
  have hscale : VineCount.DecScale M L w Adm (Step1.VCLadderScale K L w P) :=
    fun c κ' hd hc hk => Step1.vcLadderScale_of_sourceAdm K hMol hM L w P hP1 hP2 hd hc (hAdm c κ' hd hc hk)
  have hcount := hcnt L hL M K R h hMol hM hvine w Adm P hP0 hscale η (2 * Rg) (two_R_L hL0 hRl)
    (crit_theta hL1' hγ hη h200a h200b hcrit) hgap hcone
  obtain ⟨hbc', hm'⟩ := Step1.vine_bonds_of_vine (Step1.adjointCut K R h) hvine
  have hbc : K.vc.bonds.card = 2 * (K.C.atoms.card - 1) := by
    rw [← Step1.adj_bonds_card K R h]; exact hbc'
  exact Step1.prop94_vine_single' K hd hM L γ δ C₁ C₂ η w Adm Adm' hAdm' P hL1 hδ.1 (hC₂.trans hC₁) (by linarith)
    hC₁ hP0 hP1 hP2 hη hη1 hηγ hF hbc hm' Rg hR0.le hRu 0 (2 * Rg) (Or.inl ⟨rfl, rfl⟩) (Cf * coneX d L η)
    (mul_nonneg hCf (coneX_nonneg d hL0)) 4 hcount

/-- **Two double bonds with the creation cone** (cf. L6-STEP1's `prop94_vine_double_full`). -/
theorem prop94_vine_double_cone {g : ℝ} {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    (K : Step1.VineCut g M) (S : Step1.DoubleShape K) (hd : 3 ≤ d) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (L γ δ C₁ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (P : Finset V → ℝ)
    (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hη1 : η < 1) (hηγ : η ≤ γ) (h200a : 200 * η ≤ γ)
    (h200b : 200 * η ≤ 1 - γ) (hF : K.post.numComponents = M.numComponents)
    (R : ℝ) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (hcrit : Crit L γ η R)
    (hgap : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * R)
    (hlow : ∀ κ', Adm κ' → R / 2 ≤ ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖) (hcone : JointCone K L γ δ η w Adm) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((Step1.Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (((9 ^ d * 5 ^ d * (2 * d)) * coneX d L η *
        (2 ^ d * (((0 + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (0 + 8 + 1)) * (1 + δ⁻¹)) *
          excessRHS L γ η [(R, 0), (R, 0)] 0 0)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hR : 0 < R := lt_of_lt_of_le (inv_pos.2 hL0) hRl
  have hA : K.C.atoms.card = 3 := by
    rw [S.atoms_eq]
    have h1 : K.C.upper ≠ S.x := S.x_ne_a.symm
    have h2 : S.x ≠ K.C.lower := S.x_ne_b
    have h3 : K.C.upper ≠ K.C.lower := K.ab_ne
    rw [Finset.card_insert_of_notMem (by simp [h1, h3]), Finset.card_pair h2]
  have hcount := double_count_cone S (η := η) (by omega) hL1 hδ hδ1 R (2 * R) hR (two_R_L hL0 hRl)
    (crit_theta hL1 hγ hη h200a h200b hcrit) hlow hgap hcone
  exact Step1.prop94_vine_double K hd hM L γ δ C₁ η w Adm Adm' hAdm' P hL hδ hδ1 hC hP0 hP1 hP2 hη hη1 hηγ hγ.2 hF
    (Step1.double_bonds_card S) hA (Step1.double_noLadder S) R hRl hRu 0 (2 * R) (Or.inl ⟨rfl, rfl⟩)
    ((9 ^ d * 5 ^ d * (2 * d)) * coneX d L η) (mul_nonneg (by positivity) (coneX_nonneg d hL0)) 0 hcount

/-- The constant normalization of a single-vine branch with a cone factor `X ≤ Y`. -/
theorem cone_const_single {Cf Cs t δ E X Y : ℝ} (d : ℕ) (hCf0 : 0 ≤ Cf) (hCf : Cf ≤ Cs) (ht : 0 < t) (hδ : 0 < δ)
    (hE : 0 ≤ E) (hX : 0 ≤ X) (hXY : X ≤ Y) :
    (Cf * X * (2 ^ d * (((4 + 8 + 1 : ℕ) : ℝ) / t) ^ (4 + 8 + 1))) * E ≤
      (Cs * (2 ^ d * ((13 : ℝ) / t) ^ 13) * (1 + δ⁻¹)) * Y * E := by
  have h := VineCount.dev_const_single d hCf0 hCf ht hδ (mul_nonneg hX hE)
  have hK : 0 ≤ Cs * (2 ^ d * ((13 : ℝ) / t) ^ 13) * (1 + δ⁻¹) := by
    have := hCf0.trans hCf; have := inv_nonneg.2 hδ.le; positivity
  calc (Cf * X * (2 ^ d * (((4 + 8 + 1 : ℕ) : ℝ) / t) ^ (4 + 8 + 1))) * E
      = Cf * (2 ^ d * (((4 + 8 + 1 : ℕ) : ℝ) / t) ^ (4 + 8 + 1)) * (X * E) := by ring
    _ ≤ (Cs * (2 ^ d * ((13 : ℝ) / t) ^ 13) * (1 + δ⁻¹)) * (X * E) := h
    _ ≤ (Cs * (2 ^ d * ((13 : ℝ) / t) ^ 13) * (1 + δ⁻¹)) * (Y * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hXY hE) hK
    _ = _ := by ring

/-- The constant normalization of the double-bond branch with a cone factor `X ≤ Y`. -/
theorem cone_const_double {Cd Cs t δ E X Y : ℝ} (d : ℕ) (hCd0 : 0 ≤ Cd) (hCd : Cd ≤ Cs) (ht : 0 < t) (ht2 : t ≤ 2)
    (hδ : 0 < δ) (hE : 0 ≤ E) (hX : 0 ≤ X) (hXY : X ≤ Y) :
    (Cd * X * (2 ^ d * (((0 + 8 + 1 : ℕ) : ℝ) / t) ^ (0 + 8 + 1)) * (1 + δ⁻¹)) * E ≤
      (Cs * (2 ^ d * ((13 : ℝ) / t) ^ 13) * (1 + δ⁻¹)) * Y * E := by
  have h := VineCount.dev_const_double d hCd0 hCd ht ht2 hδ (mul_nonneg hX hE)
  have hK : 0 ≤ Cs * (2 ^ d * ((13 : ℝ) / t) ^ 13) * (1 + δ⁻¹) := by
    have := hCd0.trans hCd; have := inv_nonneg.2 hδ.le; positivity
  calc (Cd * X * (2 ^ d * (((0 + 8 + 1 : ℕ) : ℝ) / t) ^ (0 + 8 + 1)) * (1 + δ⁻¹)) * E
      = (Cd * (2 ^ d * (((0 + 8 + 1 : ℕ) : ℝ) / t) ^ (0 + 8 + 1)) * (1 + δ⁻¹)) * (X * E) := by ring
    _ ≤ (Cs * (2 ^ d * ((13 : ℝ) / t) ^ 13) * (1 + δ⁻¹)) * (X * E) := h
    _ ≤ (Cs * (2 ^ d * ((13 : ℝ) / t) ^ 13) * (1 + δ⁻¹)) * (Y * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hXY hE) hK
    _ = _ := by ring

end WaveTurbulence.GammaLow.FinalCount.Ghost
