/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.GardenB
public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.TreeFlatL

/-!
# The time coefficient of a paired tree, on the Wave B garden

DH21 (varat) (L1698–L1703): for a regular tree `𝒯` with lone leaf `ℓ_*`,
`𝒜*_𝒯(t, s, α[𝒩]) = ∫_𝒟 ∏_𝔫 e^{ζ_𝔫πiα_𝔫t_𝔫} dt`,
`𝒟 = {t_{(ℓ_*)^p} > s; 0 < t_{𝔫'} < t_𝔫 < t for 𝔫' a child of 𝔫}` (`treeAstar`, on a carrier
`G : Garden 1`). With the lone leaf at the path `lp` (`hlone`), `treeAstar` is the iterated integral
`treeIntL` (`treeAstar_eq`); Wave B's `kDomain` (layer `0`, (timepairtree)) is `𝒟`, and its
`phaseIntegral` is `𝒜*_𝒯` at `α = δL^{2γ}Ω`.
-/

@[expose] public section

namespace WaveTurbulence.MainCoef

open TTree MeasureTheory Complex Set
open scoped Real

section Tree

variable (G : Garden 1)

theorem fin_one_eq_zero' (j : Fin 1) : j = 0 := Subsingleton.elim _ _

/-- The branching nodes of a one-tree garden are those of its tree. -/
def gbEquiv1 : GBranch G.tree ≃ TB (G.tree 0) where
  toFun b := ⟨b.1.2, by have h := b.2; rwa [fin_one_eq_zero' b.1.1] at h⟩
  invFun p := ⟨(0, p.1), p.2⟩
  left_inv b := by
    rcases b with ⟨⟨j, p⟩, h⟩
    obtain rfl := fin_one_eq_zero' j
    rfl
  right_inv _ := rfl

/-- **The time domain 𝒟 of a paired tree** (DH21 (varat); Wave B (timepairtree)). -/
def treeDomG (t s : ℝ) : Set (GBranch G.tree → ℝ) :=
  {τ | ∀ b, 0 < τ b ∧ τ b < t ∧ (∀ b' : GBranch G.tree, b'.IsChildOf b → τ b' < τ b) ∧
    (G.IsLoneParent b → s < τ b)}

/-- The phase `∏_𝔫 e^{πiζ_𝔫α_𝔫t_𝔫}` of a one-tree garden. -/
noncomputable def treePhaseG (α : Fin 1 × TTree.Path → ℝ) (τ : GBranch G.tree → ℝ) : ℂ :=
  ∏ b : GBranch G.tree, cexp (π * I * (((nodeSign G.sig b.1 : ℤˣ) : ℤ) * α b.1 * τ b))

/-- **DH21's `𝒜*_𝒯(t, s, α[𝒩])`** (varat). -/
noncomputable def treeAstar (t s : ℝ) (α : Fin 1 × TTree.Path → ℝ) : ℂ :=
  ∫ τ : GBranch G.tree → ℝ, (treeDomG G t s).indicator (treePhaseG G α) τ

/-- The phases of the tree. -/
def treeBetaG (α : Fin 1 × TTree.Path → ℝ) (p : TTree.Path) : ℝ :=
  ((nodeSign G.sig (0, p) : ℤˣ) : ℤ) * α (0, p)

variable {G}

theorem isLoneParent_iff {lp : TTree.Path} (hlp : lp ∈ (G.tree 0).leaves)
    (hlone : ∀ ℓ : GLeaf G.tree, G.IsLone ℓ ↔ ℓ.1.2 = lp) (b : GBranch G.tree) :
    G.IsLoneParent b ↔ ∃ i : Fin 3, lp = b.1.2 ++ [i] := by
  constructor
  · rintro ⟨ℓ, hℓ, -, i, hi⟩
    exact ⟨i, ((hlone ℓ).1 hℓ).symm.trans hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨⟨(0, lp), hlp⟩, (hlone _).2 rfl, ?_, i, hi⟩
    exact (fin_one_eq_zero' _).trans (fin_one_eq_zero' _).symm

theorem treeDomG_reindex {lp : TTree.Path} (hlp : lp ∈ (G.tree 0).leaves)
    (hlone : ∀ ℓ : GLeaf G.tree, G.IsLone ℓ ↔ ℓ.1.2 = lp) {t s : ℝ} (hts : LoneOK (some lp) s t)
    (σ : TB (G.tree 0) → ℝ) :
    (fun b => σ (gbEquiv1 G b)) ∈ treeDomG G t s ↔ σ ∈ treeDomFL (G.tree 0) (some lp) s t := by
  simp only [treeDomG, treeDomFL, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨hts, fun p => ?_⟩
    have hb := h ((gbEquiv1 G).symm p)
    simp only [Equiv.apply_symm_apply] at hb
    refine ⟨hb.1, hb.2.1, fun q ⟨i, hi⟩ => ?_, fun i hi => hb.2.2.2 ?_⟩
    · have := hb.2.2.1 ((gbEquiv1 G).symm q) ⟨(fin_one_eq_zero' _).trans (fin_one_eq_zero' _).symm,
        i, hi⟩
      simpa using this
    · exact (isLoneParent_iff hlp hlone _).2 ⟨i, Option.some.inj hi⟩
  · rintro ⟨-, h⟩ b
    have hb := h (gbEquiv1 G b)
    refine ⟨hb.1, hb.2.1, fun b' ⟨_, i, hi⟩ => hb.2.2.1 (gbEquiv1 G b') ⟨i, hi⟩, fun hlb => ?_⟩
    obtain ⟨i, hi⟩ := (isLoneParent_iff hlp hlone b).1 hlb
    exact hb.2.2.2 i (congrArg some hi)

theorem treePhaseG_reindex (α : Fin 1 × TTree.Path → ℝ) (σ : TB (G.tree 0) → ℝ) :
    treePhaseG G α (fun b => σ (gbEquiv1 G b)) = treePhase (G.tree 0) (treeBetaG G α) σ := by
  unfold treePhaseG treePhase treeBetaG
  rw [← (gbEquiv1 G).symm.prod_comp]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp only [Equiv.apply_symm_apply]
  push_cast
  rfl

/-- **`𝒜*_𝒯` is the iterated integral with the lone leaf at `lp`.** -/
theorem treeAstar_eq {lp : TTree.Path} (hlp : lp ∈ (G.tree 0).leaves)
    (hlone : ∀ ℓ : GLeaf G.tree, G.IsLone ℓ ↔ ℓ.1.2 = lp) {t s : ℝ} (ht : 0 ≤ t)
    (hts : LoneOK (some lp) s t) (α : Fin 1 × TTree.Path → ℝ) :
    treeAstar G t s α = treeIntL (G.tree 0) (some lp) (treeBetaG G α) s t := by
  unfold treeAstar
  rw [← integral_reindex_pi (gbEquiv1 G)]
  have e : ∀ σ : TB (G.tree 0) → ℝ,
      (treeDomG G t s).indicator (treePhaseG G α) (fun b => σ (gbEquiv1 G b)) =
        (treeDomFL (G.tree 0) (some lp) s t).indicator (treePhase (G.tree 0) (treeBetaG G α)) σ := by
    intro σ
    by_cases hσ : σ ∈ treeDomFL (G.tree 0) (some lp) s t
    · rw [Set.indicator_of_mem ((treeDomG_reindex hlp hlone hts σ).2 hσ), Set.indicator_of_mem hσ,
        treePhaseG_reindex]
    · rw [Set.indicator_of_notMem (fun h => hσ ((treeDomG_reindex hlp hlone hts σ).1 h)),
        Set.indicator_of_notMem hσ]
  simp_rw [e]
  rw [treeDomFL_eq, integral_treeDomL _ _ _ _ _ ht]

end Tree

section TreeKernel

/-- `α_𝔫 = δL^{2γ}Ω_𝔫` on the branching nodes of a one-tree garden. -/
noncomputable def alphaOmegaT {d : ℕ} (L γ δ : ℝ) (G : Garden 1) (k : GNode G.tree → Mom d)
    (a : Fin 1 × TTree.Path) : ℝ :=
  if h : a.2 ∈ (G.tree a.1).branching then δ * L ^ (2 * γ) * omegaNode G k ⟨a, h⟩ else 0

/-- **Wave B's time domain of a paired tree is 𝒟** (layer `0`, `t ≤ 1`). -/
theorem kDomain_eq_treeDomG (LG : LayeredGarden 1) (h0 : ∀ a, LG.layer a = 0) {t : ℝ} (ht1 : t ≤ 1)
    (s : ℝ) : kDomain LG (fun _ => t) s = treeDomG LG.garden t s := by
  ext τ
  simp only [kDomain, treeDomG, Set.mem_ofPred_eq, h0, Nat.cast_zero, zero_add]
  constructor
  · intro h b
    exact ⟨(h b).2.2.1, (h b).2.2.2.1, (h b).2.2.2.2.1, (h b).2.2.2.2.2⟩
  · intro h b
    have hb := h b
    exact ⟨hb.1, hb.2.1.trans_le ht1, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩

/-- **Wave B's phase integral of a garden without flowers is 𝒜*** at `α = δL^{2γ}Ω`. -/
theorem phaseIntegral_eq_treeAstar {d : ℕ} (L γ δ : ℝ) {G : Garden 1}
    (hfp : ∀ b, ¬ G.IsFlowerParent b) (t s s' : ℝ) (k : GNode G.tree → Mom d) :
    phaseIntegral L γ δ G (treeDomG G t s) s' k = treeAstar G t s (alphaOmegaT L γ δ G k) := by
  have hph : phaseProd L γ δ G k = treePhaseG G (alphaOmegaT L γ δ G k) := by
    funext τ
    unfold phaseProd treePhaseG alphaOmegaT
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [dite_eq_left b.2, show (⟨b.1, b.2⟩ : GBranch G.tree) = b from rfl]
    congr 1
    push_cast
    simp only [Garden.sign, GBranch.toNode]
    ring
  unfold phaseIntegral treeAstar
  rw [hph]
  have e : ∀ τ : G.FreeBranch → ℝ, G.extendTime s' τ = fun b => τ ((Equiv.subtypeUnivEquiv hfp).symm b) := by
    intro τ
    funext b
    simp only [Garden.extendTime, hfp b, dite_false]
    rfl
  simp_rw [e]
  exact integral_reindex_pi (Equiv.subtypeUnivEquiv hfp).symm
    (fun τ => (treeDomG G t s).indicator (treePhaseG G (alphaOmegaT L γ δ G k)) τ)

end TreeKernel

end WaveTurbulence.MainCoef
