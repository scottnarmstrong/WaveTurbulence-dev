/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceSkip
public import WaveTurbulence.Foundations.FinalCount.RedSpliceObj3
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: the skipped vine of an unmarked SG group in the marked splice (`𝒞₁` at `Mk`)

Mk twins, for an unmarked group (`¬ markedGroup G Mk S`, whose units are main's `groupUnitsOf`), of
`no_unit_outside`, `unit_L`, `unit_R`, `unit_L'`, `unit_R'`, `skip_sdecomp` (RedSpliceSkip) and `vc_object`
(RedSpliceObj3); the proofs are main's, with `unitBlocks G σ Mk` (`mem_unitBlocksMk`, `groupUnitsMk_of_not_marked`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

section skip
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
  (hSm : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG)
  {sk : SkipData G S} (hsk : (groupUnitsOf G S).skip = some sk) {Mk : Set (Stage1.CLVine G)}
  (hnm : ¬ markedGroup G Mk S)
include hM hSm hσ hsk hnm

/-- No unit meets `S` outside the two runs. -/
theorem no_unit_outsideMk {v : GBranch G.tree} (hvS : v ∈ S) (hL : v ∉ sk.L0) (hR : v ∉ sk.R0) :
    ∀ u ∈ unitBlocks G σ Mk, v ∉ u.atoms := by
  intro u hu hv
  obtain ⟨S', hS'm, hσ', hu'⟩ := mem_unitBlocksMk.mp hu
  by_cases hSS : S' = S
  · subst hSS
    rw [groupUnitsMk_of_not_marked hnm] at hu'
    rcases ((groupUnitsOf G S').skip_units sk hsk).1 u hu' with ⟨h, _⟩ | ⟨h, _⟩
    · exact hL (h ▸ hv)
    · exact hR (h ▸ hv)
  · have hpart := partition_eq_maximalGroups (stage1Collection_isPartition hM)
    have hdisj : (maximalGroups G.molecule).Pairwise (fun S T => Disjoint S T) := by
      have := (stage1Collection_isPartition hM).2.1
      rwa [hpart] at this
    exact Finset.disjoint_left.mp (hdisj hS'm hSm hSS) (groupUnitsMk_sub hu' hv) hvS

/-- The unit with atoms `L0`. -/
theorem unit_LMk (hL : sk.L0 ≠ ∅) : ∃ u ∈ unitBlocks G σ Mk, u.atoms = sk.L0 := by
  obtain ⟨u, hu, hu'⟩ := (((groupUnitsOf G S).skip_units sk hsk).2.1).resolve_left hL
  exact ⟨u, mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (groupUnitsMk_of_not_marked hnm).symm ▸ hu⟩, hu'⟩

theorem unit_RMk (hR : sk.R0 ≠ ∅) : ∃ u ∈ unitBlocks G σ Mk, u.atoms = sk.R0 := by
  obtain ⟨u, hu, hu'⟩ := (((groupUnitsOf G S).skip_units sk hsk).2.2).resolve_left hR
  exact ⟨u, mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (groupUnitsMk_of_not_marked hnm).symm ▸ hu⟩, hu'⟩

/-- The unit of the left run, with its joints. -/
theorem unit_LMk' (hL : sk.L0 ≠ ∅) : ∃ u ∈ unitBlocks G σ Mk, u.atoms = sk.L0 ∧
    (u.upper = sk.a ∧ u.lower = sk.x ∨ u.upper = sk.x ∧ u.lower = sk.a) := by
  obtain ⟨u, hu, hu'⟩ := (((groupUnitsOf G S).skip_units sk hsk).2.1).resolve_left hL
  refine ⟨u, mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (groupUnitsMk_of_not_marked hnm).symm ▸ hu⟩, hu', ?_⟩
  rcases ((groupUnitsOf G S).skip_units sk hsk).1 u hu with ⟨_, h⟩ | ⟨h1, _⟩
  · exact h
  · exfalso
    have : u.atoms ⊆ sk.L0 ∩ sk.R0 := fun v hv => mem_inter.mpr ⟨hu' ▸ hv, h1 ▸ hv⟩
    have h2 := sk.disj
    rw [Finset.disjoint_iff_inter_eq_empty] at h2
    rw [h2] at this
    apply hL
    rw [← hu']
    exact Finset.subset_empty.mp this

theorem unit_RMk' (hR : sk.R0 ≠ ∅) : ∃ u ∈ unitBlocks G σ Mk, u.atoms = sk.R0 ∧
    (u.upper = sk.y ∧ u.lower = sk.b ∨ u.upper = sk.b ∧ u.lower = sk.y) := by
  obtain ⟨u, hu, hu'⟩ := (((groupUnitsOf G S).skip_units sk hsk).2.2).resolve_left hR
  refine ⟨u, mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (groupUnitsMk_of_not_marked hnm).symm ▸ hu⟩, hu', ?_⟩
  rcases ((groupUnitsOf G S).skip_units sk hsk).1 u hu with ⟨h1, _⟩ | ⟨_, h⟩
  · exfalso
    have : u.atoms ⊆ sk.L0 ∩ sk.R0 := fun v hv => mem_inter.mpr ⟨h1 ▸ hv, hu' ▸ hv⟩
    have h2 := sk.disj
    rw [Finset.disjoint_iff_inter_eq_empty] at h2
    rw [h2] at this
    apply hR
    rw [← hu']
    exact Finset.subset_empty.mp this
  · exact h

/-- The skipped vine of an SG group satisfies the residual hypotheses for the global splice. -/
theorem skip_sdecompMk {D' : Type*} [Fintype D'] [DecidableEq D'] (N : Molecule (GBranch G.tree) D')
    (hskel : SkelDecomp N S sk.A sk.L0 sk.R0 sk.a sk.b sk.x sk.y) :
    SDecomp N (stSt G σ Mk).cls S sk.A sk.L0 sk.R0 sk.a sk.b sk.x sk.y where
  toSkelDecomp := hskel
  hcls := (stSt G σ Mk).hcls
  hLcl := by
    intro p v hv h
    have hL : sk.L0 ≠ ∅ := fun h0 => by rw [h0] at hv; simp at hv
    obtain ⟨u, hu, hua⟩ := unit_LMk hM σ hSm hσ hsk hnm hL
    exact hua ▸ class_in_unitMk (Mk := Mk) hM σ hSm hσ hsk hu (hua ▸ hv) h
  hRcl := by
    intro p v hv h
    have hR : sk.R0 ≠ ∅ := fun h0 => by rw [h0] at hv; simp at hv
    obtain ⟨u, hu, hua⟩ := unit_RMk hM σ hSm hσ hsk hnm hR
    exact hua ▸ class_in_unitMk (Mk := Mk) hM σ hSm hσ hsk hu (hua ▸ hv) h
  hLc := by
    intro p hp q hq
    have hL : sk.L0 ≠ ∅ := fun h0 => by rw [h0] at hp; simp at hp
    obtain ⟨u, hu, hua⟩ := unit_LMk hM σ hSm hσ hsk hnm hL
    exact ⟨u.upper, stSt_cls_memMk (Mk := Mk) hM σ hu (hua ▸ hp), stSt_cls_memMk (Mk := Mk) hM σ hu (hua ▸ hq)⟩
  hRc := by
    intro p hp q hq
    have hR : sk.R0 ≠ ∅ := fun h0 => by rw [h0] at hp; simp at hp
    obtain ⟨u, hu, hua⟩ := unit_RMk hM σ hSm hσ hsk hnm hR
    exact ⟨u.upper, stSt_cls_memMk (Mk := Mk) hM σ hu (hua ▸ hp), stSt_cls_memMk (Mk := Mk) hM σ hu (hua ▸ hq)⟩
  hNone := fun v hvS hL hR => stSt_cls_noneMk (Mk := Mk) hM σ (no_unit_outsideMk hM σ hSm hσ hsk hnm hvS hL hR)

end skip

/-- **The vine object of the skipped vine of an SG VC group**, in `G_sb`: `π''A` with joints `π x`, `π y`:
a (CN) vine, or a root (CL) vine (TARGET subpro(2), `blockchainprop`). -/
theorem vc_objectMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG)
    {sk : SkipData G S} (hsk : (groupUnitsOf G S).skip = some sk) {Mk : Set (Stage1.CLVine G)}
    (hnm : ¬ markedGroup G Mk S) (hbond : sk.bond = none) :
    ∃ O : Object (stSt G σ Mk).G.molecule, AllowedCollectionObject (stSt G σ Mk).G O ∧
      O.atoms = sk.A.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) ∧
      O.upper = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls sk.x ∧ O.lower = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls sk.y ∧
      ∃ h, O.shape = VineLikeObject.vc h := by
  have H := skip_sdecompMk hM σ hSm hσ hsk hnm G.molecule (sk.skelM hbond)
  have hc := (stSt G σ Mk).hcls
  let I := H.inducedIso ((stSt G σ Mk).M.toMol hc)
  obtain ⟨X, hX⟩ := sk.vine
  have hv : Vine.IsSomeVine (stSt G σ Mk).G.molecule (sk.A.image ((stSt G σ Mk).M.pi hc))
      ((stSt G σ Mk).M.pi hc sk.x) ((stSt G σ Mk).M.pi hc sk.y) := ⟨X, I.isVine hX⟩
  -- the (CL) pattern of the runs
  have hupx : sk.L0 ≠ ∅ → ((stSt G σ Mk).cls sk.x).getD sk.x = sk.x ∧ ¬ Mole.InternalParent G sk.L0 sk.x ∨
      (((stSt G σ Mk).cls sk.x).getD sk.x = sk.a ∧ ¬ Mole.InternalParent G sk.L0 sk.a ∧ Mole.InternalParent G sk.L0 sk.x) := by
    intro hL
    obtain ⟨u, hu, hua, hj⟩ := unit_LMk' hM σ hSm hσ hsk hnm hL
    have hxL := H.xL hL
    have hrc : ((stSt G σ Mk).cls sk.x).getD sk.x = u.upper := stSt_repC_memMk (Mk := Mk) hM σ hu (hua ▸ hxL)
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
  have hupy : sk.R0 ≠ ∅ → ((stSt G σ Mk).cls sk.y).getD sk.y = sk.y ∧ ¬ Mole.InternalParent G sk.R0 sk.y ∨
      (((stSt G σ Mk).cls sk.y).getD sk.y = sk.b ∧ ¬ Mole.InternalParent G sk.R0 sk.b ∧ Mole.InternalParent G sk.R0 sk.y) := by
    intro hR
    obtain ⟨u, hu, hua, hj⟩ := unit_RMk' hM σ hSm hσ hsk hnm hR
    have hyR := H.yR hR
    have hrc : ((stSt G σ Mk).cls sk.y).getD sk.y = u.upper := stSt_repC_memMk (Mk := Mk) hM σ hu (hua ▸ hyR)
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
  have ipx := ip_x H (stSt G σ Mk).M hc hupx
  have ipy := ip_y H (stSt G σ Mk).M hc hupy
  refine ⟨objVC _ _ _ hv, ?_, rfl, rfl, rfl, _, rfl⟩
  refine ⟨hv, ?_⟩
  rcases sk.kind with hcn | ⟨hroot, c, hca, htop⟩
  · exact Or.inl ⟨fun h => hcn.1 (ipx.mp h), fun h => hcn.2 (ipy.mp h)⟩
  · have hroot := hroot hbond
    have hc' : c.atoms = sk.A := hca
    have hB1 : G.molecule.IsBlock c.atoms c.upper c.lower := c.isVine.choose_spec.1
    have hB2 : G.molecule.IsBlock c.atoms sk.x sk.y := hc' ▸ hX.1
    have hjoint := Vine.block_joints_unique G.molecule hB1 hB2
    -- degree bound
    have hdeg : (stSt G σ Mk).G.molecule.deg ((stSt G σ Mk).M.pi hc sk.x) +
        (stSt G σ Mk).G.molecule.deg ((stSt G σ Mk).M.pi hc sk.y) ≤ 6 := by
      obtain ⟨a', b', hvc', _, hd6⟩ := hroot
      have hj := Vine.block_joints_unique G.molecule hvc'.1 (sk.blockM hbond)
      have h1 := H.deg_x_le ((stSt G σ Mk).M.toMol hc)
      have h2 := H.deg_y_le ((stSt G σ Mk).M.toMol hc)
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

end WaveTurbulence.RedSplice
