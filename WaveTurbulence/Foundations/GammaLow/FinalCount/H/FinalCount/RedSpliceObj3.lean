/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceObj3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceObj2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.G3GroupIso
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.RedSpliceInduced
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceObj3`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# REDSPLICE-DEF (S2a), B: the vine object of a skipped (CN) / root (CL) vine of a VC group in `G_sb`
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- **The vine object of the skipped vine of an SG VC group**, in `G_sb`: `π''A` with joints `π x`, `π y`:
a (CN) vine, or a root (CL) vine (TARGET subpro(2), `blockchainprop`). -/
theorem vc_object (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG)
    {sk : SkipData G S} (hsk : (groupUnitsOf G S).skip = some sk) (hbond : sk.bond = none) :
    ∃ O : Src.Object Src.γL (stSt G σ).G.molecule, Src.AllowedCollectionObject Src.γL (stSt G σ).G O ∧
      O.atoms = sk.A.image ((stSt G σ).M.pi (stSt G σ).hcls) ∧
      O.upper = (stSt G σ).M.pi (stSt G σ).hcls sk.x ∧ O.lower = (stSt G σ).M.pi (stSt G σ).hcls sk.y ∧
      ∃ h, O.shape = Src.VineLikeObject.vc h := by
  have H := skip_sdecomp hM σ hSm hσ hsk G.molecule (sk.skelM hbond)
  have hc := (stSt G σ).hcls
  let I := H.inducedIso ((stSt G σ).M.toMol hc)
  have hX := sk.vine
  have hv : Src.IsSomeVine Src.γL (stSt G σ).G.molecule (sk.A.image ((stSt G σ).M.pi hc))
      ((stSt G σ).M.pi hc sk.x) ((stSt G σ).M.pi hc sk.y) := I.isVineS hX
  -- the (CL) pattern of the runs
  have hupx : sk.L0 ≠ ∅ → ((stSt G σ).cls sk.x).getD sk.x = sk.x ∧ ¬ Mole.InternalParent G sk.L0 sk.x ∨
      (((stSt G σ).cls sk.x).getD sk.x = sk.a ∧ ¬ Mole.InternalParent G sk.L0 sk.a ∧ Mole.InternalParent G sk.L0 sk.x) := by
    intro hL
    obtain ⟨u, hu, hua, hj⟩ := unit_L' hM σ hSm hσ hsk hL
    have hxL := H.xL hL
    have hrc : ((stSt G σ).cls sk.x).getD sk.x = u.upper := stSt_repC_mem hM σ hu (hua ▸ hxL)
    have hcl := u.cl
    rw [hua] at hcl
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      refine ⟨hrc.trans h1, ?_, ?_⟩
      · have := hcl.1; rwa [h1] at this
      · have := hcl.2; rwa [h2] at this
    · left
      refine ⟨hrc.trans h1, ?_⟩
      have := hcl.1; rwa [h1] at this
  have hupy : sk.R0 ≠ ∅ → ((stSt G σ).cls sk.y).getD sk.y = sk.y ∧ ¬ Mole.InternalParent G sk.R0 sk.y ∨
      (((stSt G σ).cls sk.y).getD sk.y = sk.b ∧ ¬ Mole.InternalParent G sk.R0 sk.b ∧ Mole.InternalParent G sk.R0 sk.y) := by
    intro hR
    obtain ⟨u, hu, hua, hj⟩ := unit_R' hM σ hSm hσ hsk hR
    have hyR := H.yR hR
    have hrc : ((stSt G σ).cls sk.y).getD sk.y = u.upper := stSt_repC_mem hM σ hu (hua ▸ hyR)
    have hcl := u.cl
    rw [hua] at hcl
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨hrc.trans h1, ?_⟩
      have := hcl.1; rwa [h1] at this
    · right
      refine ⟨hrc.trans h1, ?_, ?_⟩
      · have := hcl.1; rwa [h1] at this
      · have := hcl.2; rwa [h2] at this
  have ipx := ip_x H (stSt G σ).M hc hupx
  have ipy := ip_y H (stSt G σ).M hc hupy
  refine ⟨objVC _ _ _ hv, ?_, rfl, rfl, rfl, _, rfl⟩
  refine ⟨hv, ?_⟩
  rcases sk.kind with hcn | ⟨hroot, c, hca, htop⟩
  · exact Or.inl ⟨fun h => hcn.1 (ipx.mp h), fun h => hcn.2 (ipy.mp h)⟩
  · have hroot := hroot hbond
    have hc' : c.atoms = sk.A := hca
    have hB1 : G.molecule.IsBlock c.atoms c.upper c.lower := c.isVine.block
    have hB2 : G.molecule.IsBlock c.atoms sk.x sk.y := hc' ▸ hX.block
    have hjoint := Vine.block_joints_unique G.molecule hB1 hB2
    -- degree bound
    have hdeg : (stSt G σ).G.molecule.deg ((stSt G σ).M.pi hc sk.x) +
        (stSt G σ).G.molecule.deg ((stSt G σ).M.pi hc sk.y) ≤ 6 := by
      obtain ⟨a', b', hvc', _, hd6⟩ := hroot
      have hj := Vine.block_joints_unique G.molecule hvc'.1 (sk.blockM hbond)
      have h1 := H.deg_x_le ((stSt G σ).M.toMol hc)
      have h2 := H.deg_y_le ((stSt G σ).M.toMol hc)
      rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · subst e1; subst e2; exact (add_le_add h1 h2).trans hd6
      · subst e1; subst e2; rw [Nat.add_comm] at hd6; exact (add_le_add h1 h2).trans hd6
    refine Or.inr ⟨?_, hdeg⟩
    have hnp : ¬ Mole.InternalParent G c.atoms c.upper := c.notParentUpper
    have hp : Mole.InternalParent G c.atoms c.lower := c.parentLower
    rw [hc'] at hnp hp
    rcases Mole.finset_pair_eq_pair_iff.mp hjoint with ⟨hu, hl⟩ | ⟨hu, hl⟩
    · rw [hu] at hnp; rw [hl] at hp
      exact Or.inl ⟨fun h => hnp (ipx.mp h), ipy.mpr hp⟩
    · rw [hu] at hnp; rw [hl] at hp
      exact Or.inr ⟨fun h => hnp (ipy.mp h), ipx.mpr hp⟩

end WaveTurbulence.GammaLow.FinalCount.H
