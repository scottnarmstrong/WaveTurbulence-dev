/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll3
public import WaveTurbulence.Foundations.FinalCount.G3Iota

/-! # H-ASM (packet L6-HASM): Step-1 counts in the ball form of the run

The G3 run supplies the `ι` condition of a `κ = 50` vine step as a ball in each parameter class (`IotaUnif.ball :
FinalCountG3.IotaBall`), main's `G3VineBall` form; L6-STEP1's counts take the stronger decoration-level `IotaReading`,
which they use only through `ball_of_iota (hι hκ50) c β k0 hp` (an `IotaBall`). The four theorems below are L6-STEP1's
`prop94_vine_double_full` (Prop94Statement), `prop94_vine_final` (VCStmt), `prop94_hyper_final` (VCAll1) and
`prop94_vine_all` (VCAll3), copied by source (sha256 in `ASM-COPIED-SHA256SUMS`) with exactly that hypothesis replaced by
`FinalCountG3.IotaBall … γ δ …` and the call by `(hι hκ50) c β k0 hp` (names suffixed `_low`: main's `prop94_*_ball` of `G3VineBall` take `VINEPARAM` and are H-G3's port; over
L6-STEP1's charted counts instead of VINEPARAM). They feed `AsmEx1ULow.ex1A_uniform`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.CountLemmas
variable {g : ℝ} {d : ℕ}

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **Prop 9.4, Step 1, a VC formed by two double bonds `a = x = b`: unconditional** (the count `𝔉` of L1801, last
sentence, is `DoubleShape.labelSet_le_vineG`). Source facts assumed: the shape `S`; `ΔF = 0` (`hF`, L1798);
`4` bonds in the VC (`hB`, two double bonds); no ladder in the VC (`hlad`); the label `|r| ~ R` of the new
`α`-atoms (`hgap`: `|r| <= 2R`, `hlow`: `|r| >= R/2`); for `κ = 50` the `ι` condition (`hι`). -/
theorem prop94_vine_double_full_ball_low {M : Molecule V D} (K : VineCut g M) (S : DoubleShape K) (hd : 3 ≤ d)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (L γ δ C₁ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (P : Finset V → ℝ)
    (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hη : 0 < η) (hη1 : η < 1) (hηγ : η ≤ γ) (hγ1 : γ < 1)
    (hF : K.post.numComponents = M.numComponents)
    (hB : K.vc.bonds.card = 4) (hlad : K.vc.maximalLadders = ∅)
    (R : ℝ) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (κ : ℕ) (ρ : ℝ)
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R ∧ L⁻¹ ≤ ρ))
    (hgap : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * R)
    (hlow : ∀ κ', Adm κ' → R / 2 ≤ ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖)
    (hι : κ = 50 → FinalCountG3.IotaBall M L γ δ w Adm K.x₁ K.x₂ (L ^ (-50 * η) * R)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (((9 ^ d * 5 ^ d * (2 * d)) * (2 ^ d * (((0 + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (0 + 8 + 1)) *
        (1 + δ⁻¹)) * excessRHS L γ η [(R, κ), (R, κ)] 0 0)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hR : 0 < R := lt_of_lt_of_le (inv_pos.2 hL0) hRl
  have hA : K.C.atoms.card = 3 := by
    rw [S.atoms_eq]
    have h1 : K.C.upper ≠ S.x := S.x_ne_a.symm
    have h2 : S.x ≠ K.C.lower := S.x_ne_b
    have h3 : K.C.upper ≠ K.C.lower := K.ab_ne
    rw [Finset.card_insert_of_notMem (by simp [h1, h3]), Finset.card_pair h2]
  have hρ0 : 0 ≤ ρ := by
    rcases hρ with ⟨-, rfl⟩ | ⟨-, rfl, -⟩
    · linarith
    · exact mul_nonneg (Real.rpow_nonneg hL0.le _) hR.le
  have hρL : 1 ≤ ρ * L := by
    rcases hρ with ⟨-, rfl⟩ | ⟨-, -, h⟩
    · have : 1 ≤ R * L := by
        have := mul_le_mul_of_nonneg_right hRl hL0.le
        rwa [inv_mul_cancel₀ hL0.ne'] at this
      nlinarith
    · have := mul_le_mul_of_nonneg_right h hL0.le
      rwa [inv_mul_cancel₀ hL0.ne'] at this
  have hball : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ' K.x₁ K.x₂ - r₀‖ ≤ ρ := by
    intro c β k0 hp
    rcases hρ with ⟨hκ0, rfl⟩ | ⟨hκ50, rfl, -⟩
    · exact ⟨0, fun κ' hκ' => by simpa using hgap κ' hκ'.2.2⟩
    · exact (hι hκ50) c β k0 hp
  have hcount : VineCountInputDouble K L γ δ R ρ (9 ^ d * 5 ^ d * (2 * d)) w Adm 0 :=
    S.labelSet_le_vineG (by omega) hL1 hδ hδ1 R ρ hR hρ0 hρL hlow hball
  exact Step1.prop94_vine_double K hd hM L γ δ C₁ η w Adm Adm' hAdm' P hL hδ hδ1 hC hP0 hP1 hP2 hη hη1 hηγ hγ1 hF hB hA hlad
    R hRl hRu κ ρ hρ _ (by positivity) 0 hcount

end

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- **DH23 Prop 9.4, Step 1, a single vine (L1797--L1801), of a charted vine (`Charted`; main: from `VINEPARAM`).** For `d ≥ 3`, `γ ∈ (0,1)`
there are constants `Cf, C₂` (depending on `d, γ`) such that for all `δ ∈ (0,1]`, `L` large, every `C₁ ≥ C₂`, every
`η ≤ γ`, every molecule `M` (`M.IsMolecule`, degrees `≤ 4`) and every vine removal `K` (Stage-2 operation `vine`)
whose removed object is a single vine, with `ΔF = 0` (`hF`, L1798), the new `α`-atoms labelled by `R ∈ [L⁻¹, L^{-γ+η}]`
(`κ ∈ {0, 50}`; for `κ = 50` the `ι`-condition `IotaReading`), and an admissible class `Adm` that carries the ladder scales
(`VCLadderScale`), the deviation of the operation is `≲ L^{-η³} ∏ L^{(γ+3η)/2-κη}R` (excesseqn2). -/
theorem prop94_vine_final_ball_low (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cf C₂ : ℝ, 0 ≤ Cf ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut g M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) → Charted M K.C.atoms K.C.upper K.C.lower →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents →
        ∀ (R : ℝ), L⁻¹ ≤ R → R ≤ L ^ (-γ + η) → ∀ (κ : ℕ) (ρ : ℝ),
        ((κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R ∧ L⁻¹ ≤ ρ)) →
        (∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * R) →
        (κ = 50 → FinalCountG3.IotaBall M L γ δ w Adm K.x₁ K.x₂ (L ^ (-50 * η) * R)) →
        DecScale M L w Adm (VCLadderScale K L w P) →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cf * (2 ^ d * (((4 + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (4 + 8 + 1))) *
            excessRHS L γ η [(R, κ), (R, κ)] 0 0)) := by
  obtain ⟨Cf, C₂, hCf, hC₂, hmain⟩ := vine_count_main hd hγ
  refine ⟨Cf, C₂, hCf, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hcnt⟩ := hmain δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η hC₁ hη hη1 hηγ => ?_⟩
  intro V D _ _ _ M K hMol hM hvine w Adm Adm' hAdm' P hP0 hP1 hP2 hF R hRl hRu κ ρ hρ hgap hι hscale
  have hL1 : Real.exp 1 ≤ L := hL₀.trans hL
  have hL1' : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL1
  have hL0 : 0 < L := by linarith
  have hR0 : 0 < R := lt_of_lt_of_le (inv_pos.mpr hL0) hRl
  have hRL : 1 ≤ R * L := by
    have := mul_le_mul_of_nonneg_right hRl hL0.le
    rwa [inv_mul_cancel₀ hL0.ne'] at this
  have hR1 : R ≤ 1 := hRu.trans (Real.rpow_le_one_of_one_le_of_nonpos hL1' (by linarith))
  have hρ0 : 0 ≤ ρ := by
    rcases hρ with ⟨-, rfl⟩ | ⟨-, rfl, -⟩
    · linarith
    · exact mul_nonneg (Real.rpow_nonneg hL0.le _) hR0.le
  have hρ2 : ρ ≤ 2 := by
    rcases hρ with ⟨-, rfl⟩ | ⟨-, rfl, -⟩
    · linarith
    · have : L ^ (-50 * η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1' (by linarith)
      nlinarith [Real.rpow_nonneg hL0.le (-50 * η)]
  have hρL : 1 ≤ ρ * L := by
    rcases hρ with ⟨-, rfl⟩ | ⟨-, -, h⟩
    · nlinarith
    · have := mul_le_mul_of_nonneg_right h hL0.le
      rwa [inv_mul_cancel₀ hL0.ne'] at this
  have hball : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ' K.x₁ K.x₂ - r₀‖ ≤ ρ := by
    intro c β k0 hp
    rcases hρ with ⟨hκ0, rfl⟩ | ⟨hκ50, rfl, -⟩
    · exact ⟨0, fun κ' hκ' => by simpa using hgap κ' hκ'.2.2⟩
    · exact (hι hκ50) c β k0 hp
  have hcount := hcnt L hL M K hMol hM hvine w Adm P hP0 hscale ρ hρ0 hρ2 hρL hball
  obtain ⟨hB, X, ⟨A⟩⟩ := hvine
  have hcard := card_atoms_eq K A
  have hbc : K.vc.bonds.card = 2 * (K.C.atoms.card - 1) := by
    rw [Step1.vc_bonds_card K hB, A.bond_count]; omega
  have hn1 : 1 ≤ A.indexing.shape.n := by unfold Shape.n; omega
  exact Step1.prop94_vine_single' K hd hM L γ δ C₁ C₂ η w Adm Adm' hAdm' P hL1 hδ.1 (hC₂.trans hC₁) (by linarith) hC₁
    hP0 hP1 hP2 hη hη1 hηγ hF hbc (by omega) R hR0.le hRu κ ρ hρ Cf hCf 4 hcount

/-- **DH23 Prop 9.4, Step 1, a hyper object whose adjoint VC is a single vine** (HV, and the triple bonds of
`subpro` (c): the adjoint is a double bond), of a charted vine (`Charted`; main: from `VINEPARAM`), the ladder scales being the molecule-level
canonical ladder-gap form `SourceLadderGaps` (lg-spine `sourceLadderGapScales`) of `Adm`.  The deleted bond between the joints is not counted (it stays in `𝕄_pos`). -/
theorem prop94_hyper_final_ball_low (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cf C₂ : ℝ, 0 ≤ Cf ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut g M)
        (R : Src.HyperLikeRealization g M K.C.atoms K.C.upper K.C.lower) (_h : K.C.shape = .hyper R),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) →
        Charted (Molecule.eraseBond M R.added) K.C.atoms K.C.upper K.C.lower →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        DecScale M L w Adm (SourceLadderGaps M L w P) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents →
        ∀ (Rg : ℝ), L⁻¹ ≤ Rg → Rg ≤ L ^ (-γ + η) → ∀ (κ : ℕ) (ρ : ℝ),
        ((κ = 0 ∧ ρ = 2 * Rg) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * Rg ∧ L⁻¹ ≤ ρ)) →
        (∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * Rg) →
        (κ = 50 → FinalCountG3.IotaBall M L γ δ w Adm K.x₁ K.x₂ (L ^ (-50 * η) * Rg)) →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cf * (2 ^ d * (((4 + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (4 + 8 + 1))) *
            excessRHS L γ η [(Rg, κ), (Rg, κ)] 0 0)) := by
  obtain ⟨Cf, C₂, hCf, hC₂, hmain⟩ := hyper_count_main hd hγ
  refine ⟨Cf, C₂, hCf, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hcnt⟩ := hmain δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η hC₁ hη hη1 hηγ => ?_⟩
  intro V D _ _ _ M K R h hMol hM hvine w Adm Adm' hAdm' P hP0 hAdm hP1 hP2 hF Rg hRl hRu κ ρ hρ hgap hι
  have hL1 : Real.exp 1 ≤ L := hL₀.trans hL
  have hL1' : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL1
  have hL0 : 0 < L := by linarith
  have hscale : DecScale M L w Adm (VCLadderScale K L w P) :=
    fun c κ' hd hc hk => Step1.vcLadderScale_of_sourceAdm K hMol hM L w P hP1 hP2 hd hc (hAdm c κ' hd hc hk)
  obtain ⟨hR0, hρ0, hρ2, hρL⟩ := Step1.rho_facts hL1' hRl hRu hη hηγ hρ
  have hball : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ' K.x₁ K.x₂ - r₀‖ ≤ ρ := by
    intro c β k0 hp
    rcases hρ with ⟨hκ0, rfl⟩ | ⟨hκ50, rfl, -⟩
    · exact ⟨0, fun κ' hκ' => by simpa using hgap κ' hκ'.2.2⟩
    · exact (hι hκ50) c β k0 hp
  have hcount := hcnt L hL M K R h hMol hM hvine w Adm P hP0 hscale ρ hρ0 hρ2 hρL hball
  obtain ⟨hbc', hm'⟩ := Step1.vine_bonds_of_vine (adjointCut K R h) hvine
  have hbc : K.vc.bonds.card = 2 * (K.C.atoms.card - 1) := by
    rw [← adj_bonds_card K R h]; exact hbc'
  exact Step1.prop94_vine_single' K hd hM L γ δ C₁ C₂ η w Adm Adm' hAdm' P hL1 hδ.1 (hC₂.trans hC₁) (by linarith) hC₁
    hP0 hP1 hP2 hη hη1 hηγ hF hbc hm' Rg hR0.le hRu κ ρ hρ Cf hCf 4 hcount

end

/-- **DH23 Prop 9.4, Step 1, for every vine-like object removed by `Stage2Op.vine K`** (L1773--L1801): a single vine
(ordinary VC or the adjoint of a hyper object) or two double bonds (VC or the adjoint of an HVC), with the new
`α`-atoms labelled `Rg ∈ [L⁻¹, L^{-γ+η}]`, `κ ∈ {0, 50}`.  Vine hypothesis: the removed single vine is charted (`SingleVineVC`; main: `VINEPARAM`).  Premises are the
source ones: the classification of `Prop subsetvc` (`hcls`), `ΔF = 0` (`hF`, L1798), the gap `|r| ∼ Rg`
(`hgap`, `hlow`, L1800), `ι` (L1782, L1801), the heredity of `P` along maximal ladders (F-FC-3) and the molecule-level
ladder-gap clause of `Adm` (`SourceLadderGaps` = lg-spine `sourceLadderGapScales`, requirement (ii) of `kqmainest2`, L1692), at decorations (`DecScale`).  (`hlow` is used for the
double bonds only.) -/
theorem prop94_vine_all_ball_low (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut g M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) → (SingleVineVC K ∨ Nonempty (DoubleShape K)) →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        DecScale M L w Adm (SourceLadderGaps M L w P) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents →
        ∀ (Rg : ℝ), L⁻¹ ≤ Rg → Rg ≤ L ^ (-γ + η) → ∀ (κ : ℕ) (ρ : ℝ),
        ((κ = 0 ∧ ρ = 2 * Rg) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * Rg ∧ L⁻¹ ≤ ρ)) →
        (∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * Rg) →
        (∀ κ', Adm κ' → Rg / 2 ≤ ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖) →
        (κ = 50 → FinalCountG3.IotaBall M L γ δ w Adm K.x₁ K.x₂ (L ^ (-50 * η) * Rg)) →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cs * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13) * (1 + δ⁻¹)) *
            excessRHS L γ η [(Rg, κ), (Rg, κ)] 0 0)) := by
  obtain ⟨Cf₁, C₂₁, hCf₁, hC₂₁, h₁⟩ := prop94_vine_final_ball_low hd hγ
  obtain ⟨Cf₂, C₂₂, hCf₂, hC₂₂, h₂⟩ := prop94_hyper_final_ball_low hd hγ
  refine ⟨max (max Cf₁ Cf₂) ((9 : ℝ) ^ d * 5 ^ d * (2 * d)), ?_, max C₂₁ C₂₂, le_max_of_le_left hC₂₁, ?_⟩
  · exact le_max_of_le_left (le_max_of_le_left hCf₁)
  intro δ hδ
  obtain ⟨L₁, hL₁, hh₁⟩ := h₁ δ hδ
  obtain ⟨L₂, hL₂, hh₂⟩ := h₂ δ hδ
  refine ⟨max (max L₁ L₂) (Real.exp 1), le_max_right _ _, ?_⟩
  intro L hL C₁ η hC₁ hη hη1 hηγ V D _ _ _ M K hMol hM hcls w Adm Adm' hAdm' P hP0 hAdm hP1 hP2 hF Rg hRl hRu κ ρ
    hρ hgap hlow hι
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1' : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hL0 : 0 < L := by linarith
  have hLa : L ≥ L₁ := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hLb : L ≥ L₂ := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have hCa : C₂₁ ≤ C₁ := (le_max_left _ _).trans hC₁
  have hCb : C₂₂ ≤ C₁ := (le_max_right _ _).trans hC₁
  obtain ⟨hR0, hρ0, hρ2, hρL⟩ := Step1.rho_facts hL1' hRl hRu hη hηγ hρ
  have ht : 0 < 2 * η - η ^ 3 := by nlinarith [sq_nonneg η, mul_pos hη hη]
  have ht2 : 2 * η - η ^ 3 ≤ 2 := by nlinarith [sq_nonneg η, pow_pos hη 3]
  have hE : 0 ≤ excessRHS L γ η [(Rg, κ), (Rg, κ)] 0 0 := by
    rw [excessRHS_alpha]; positivity
  set Cs := max (max Cf₁ Cf₂) ((9 : ℝ) ^ d * 5 ^ d * (2 * d)) with hCs
  rcases hcls with hs | hS
  · -- a single vine
    unfold Step1.SingleVineVC at hs
    rcases hsh : K.C.shape with hv | R
    · rw [hsh] at hs
      have hscale : DecScale M L w Adm (VCLadderScale K L w P) :=
        fun c κ' hd hc hk => Step1.vcLadderScale_of_sourceAdm K hMol hM L w P hP1 hP2 hd hc (hAdm c κ' hd hc hk)
      have := hh₁ L hLa C₁ η hCa hη hη1 hηγ M K hMol hM hs w Adm Adm' hAdm' P hP0 hP1 hP2 hF Rg hRl hRu κ ρ hρ hgap
        hι hscale
      refine isDeviation_mono this (ENNReal.ofReal_le_ofReal ?_)
      exact dev_const_single d hCf₁ (le_max_of_le_left (le_max_left _ _)) ht hδ.1 hE
    · rw [hsh] at hs
      have := hh₂ L hLb C₁ η hCb hη hη1 hηγ M K R hsh hMol hM hs w Adm Adm' hAdm' P hP0 hAdm hP1 hP2 hF Rg hRl hRu κ
        ρ hρ hgap hι
      refine isDeviation_mono this (ENNReal.ofReal_le_ofReal ?_)
      exact dev_const_single d hCf₂ (le_max_of_le_left (le_max_right _ _)) ht hδ.1 hE
  · -- two double bonds
    obtain ⟨S⟩ := hS
    have hC1 : 1 ≤ C₁ := hC₂₁.trans hCa
    have := prop94_vine_double_full_ball_low K S hd hM L γ δ C₁ η w Adm Adm' hAdm' P hLe hδ.1 hδ.2 hC1 hP0 hP1 hP2 hη hη1 hηγ
      hγ.2 hF (Step1.double_bonds_card S) (Step1.double_noLadder S) Rg hRl hRu κ ρ hρ hgap hlow hι
    refine isDeviation_mono this (ENNReal.ofReal_le_ofReal ?_)
    exact dev_const_double d (by positivity) (le_max_right _ _) ht ht2 hδ.1 hE

end WaveTurbulence.GammaLow.FinalCount.H
