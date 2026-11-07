/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCStmt
public import WaveTurbulence.Foundations.FinalCount.VCHyper4
public import WaveTurbulence.Foundations.FinalCount.VCSource
/-! # VINE-COUNT part 30: Prop 9.4 Step 1 for a single vine given by an ordinary VC or by a hyper object, with the
ladder scales taken from the molecule-level restriction of `Adm` (`SourceLadderGaps`, at decorations). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount WaveTurbulence.CountLemmas

variable {d : ℕ}

section Facts
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- The numerical facts about the label `R` of the new `α`-atoms and the gap ball, as in `prop94_vine_final`. -/
theorem rho_facts {L γ η R ρ : ℝ} {κ : ℕ} (hL1 : 1 ≤ L) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (hη : 0 < η)
    (hηγ : η ≤ γ) (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R ∧ L⁻¹ ≤ ρ)) :
    0 < R ∧ 0 ≤ ρ ∧ ρ ≤ 2 ∧ 1 ≤ ρ * L := by
  have hL0 : 0 < L := by linarith
  have hR0 : 0 < R := lt_of_lt_of_le (inv_pos.mpr hL0) hRl
  have hR1 : R ≤ 1 := hRu.trans (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith))
  refine ⟨hR0, ?_, ?_, ?_⟩
  · rcases hρ with ⟨-, rfl⟩ | ⟨-, rfl, -⟩
    · linarith
    · exact mul_nonneg (Real.rpow_nonneg hL0.le _) hR0.le
  · rcases hρ with ⟨-, rfl⟩ | ⟨-, rfl, -⟩
    · linarith
    · have : L ^ (-50 * η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
      nlinarith [Real.rpow_nonneg hL0.le (-50 * η)]
  · rcases hρ with ⟨-, rfl⟩ | ⟨-, -, h⟩
    · have : 1 ≤ R * L := by
        have := mul_le_mul_of_nonneg_right hRl hL0.le
        rwa [inv_mul_cancel₀ hL0.ne'] at this
      nlinarith
    · have := mul_le_mul_of_nonneg_right h hL0.le
      rwa [inv_mul_cancel₀ hL0.ne'] at this

/-- Bond count and size of a single vine: `2(|S|-1)` bonds, at least two atoms. -/
theorem vine_bonds_of_vine (hvp : VINEPARAM) {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} (hMol : M.IsMolecule) (K : VineCut M) {X : VineType}
    (hX : M.IsVine X K.C.atoms K.C.upper K.C.lower) :
    K.vc.bonds.card = 2 * (K.C.atoms.card - 1) ∧ 2 ≤ K.C.atoms.card := by
  obtain ⟨A⟩ := hvp V D M hMol X _ _ _ hX
  have hcard := card_atoms_eq K A
  have hn1 : 1 ≤ A.indexing.shape.n := by unfold Shape.n; omega
  refine ⟨?_, by omega⟩
  rw [vc_bonds_card K hX.1, A.bond_count]; omega

end Facts


/-- **DH23 Prop 9.4, Step 1, a hyper object whose adjoint VC is a single vine** (HV, and the triple bonds of
`subpro` (c): the adjoint is a double bond), from `VINEPARAM` alone, the ladder scales being the molecule-level
canonical ladder-gap form `SourceLadderGaps` (lg-spine `sourceLadderGapScales`) of `Adm`.  The deleted bond between the joints is not counted (it stays in `𝕄_pos`). -/
theorem prop94_hyper_final (hvp : VINEPARAM) (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cf C₂ : ℝ, 0 ≤ Cf ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut M)
        (R : HyperLikeRealization M K.C.atoms K.C.upper K.C.lower) (_h : K.C.shape = .hyper R),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) →
        (∃ X, (Molecule.eraseBond M R.added).IsVine X K.C.atoms K.C.upper K.C.lower) →
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
        (κ = 50 → IotaReading M L w Adm K.x₁ K.x₂ (L ^ (-50 * η) * Rg)) →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cf * (2 ^ d * (((4 + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (4 + 8 + 1))) *
            excessRHS L γ η [(Rg, κ), (Rg, κ)] 0 0)) := by
  obtain ⟨Cf, C₂, hCf, hC₂, hmain⟩ := hyper_count_main hvp hd hγ
  refine ⟨Cf, C₂, hCf, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hcnt⟩ := hmain δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η hC₁ hη hη1 hηγ => ?_⟩
  intro V D _ _ _ M K R h hMol hM hvine w Adm Adm' hAdm' P hP0 hAdm hP1 hP2 hF Rg hRl hRu κ ρ hρ hgap hι
  have hL1 : Real.exp 1 ≤ L := hL₀.trans hL
  have hL1' : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL1
  have hL0 : 0 < L := by linarith
  have hscale : DecScale M L w Adm (VCLadderScale K L w P) :=
    fun c κ' hd hc hk => vcLadderScale_of_sourceAdm K hMol hM L w P hP1 hP2 hd hc (hAdm c κ' hd hc hk)
  obtain ⟨hR0, hρ0, hρ2, hρL⟩ := rho_facts hL1' hRl hRu hη hηγ hρ
  have hball : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ' K.x₁ K.x₂ - r₀‖ ≤ ρ := by
    intro c β k0 hp
    rcases hρ with ⟨hκ0, rfl⟩ | ⟨hκ50, rfl, -⟩
    · exact ⟨0, fun κ' hκ' => by simpa using hgap κ' hκ'.2.2⟩
    · exact ball_of_iota (hι hκ50) c β k0 hp
  have hcount := hcnt L hL M K R h hMol hM hvine w Adm P hP0 hscale ρ hρ0 hρ2 hρL hball
  obtain ⟨X, hX⟩ := hvine
  have hMol' : (Molecule.eraseBond M R.added).IsMolecule := Vine.eraseBond_isMolecule M hMol _ (added_nonloop K R h)
  obtain ⟨hbc', hm'⟩ := vine_bonds_of_vine hvp hMol' (adjointCut K R h) hX
  have hbc : K.vc.bonds.card = 2 * (K.C.atoms.card - 1) := by
    rw [← adj_bonds_card K R h]; exact hbc'
  exact prop94_vine_single' K hd hM L γ δ C₁ C₂ η w Adm Adm' hAdm' P hL1 hδ.1 (hC₂.trans hC₁) (by linarith) hC₁
    hP0 hP1 hP2 hη hη1 hηγ hF hbc hm' Rg hR0.le hRu κ ρ hρ Cf hCf 4 hcount

end WaveTurbulence.VineCount
