/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceObj3
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceObj2
import Mathlib.Tactic

/-!
# R83 successor copy: the normalized collection `C_1`

Source copy: pinned/r83-RedSpliceColl.lean; hash recorded in COPIED-SHA256SUMS.

For every SG group `S` of `𝒞` that is an HV, or has a skipped ingredient, `exists_obj` produces the residual
object in `G_sb` (an HV; a (CN) vine; a root (CL) vine) with the properties used for
`SubproChoices.Structural` and `hingeOutsideFirst`: allowed, supported on the image of `S`, and hinge atoms
occur in it only as joints.  `objects G σ` is the list of these objects.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

theorem groups_disjoint (hM : G.molecule.IsMolecule) :
    (maximalGroups G.molecule).Pairwise (fun S T => Disjoint S T) := by
  have hpart := partition_eq_maximalGroups (stage1Collection_isPartition hM)
  have := (stage1Collection_isPartition hM).2.1
  rwa [hpart] at this

/-- The crown of an atom of a group lies in the group. -/
theorem repC_mem_group (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) {z : GBranch G.tree} (hz : z ∈ S) :
    repC (stSt G σ).cls z ∈ S := by
  by_cases h : ∃ u ∈ unitBlocks G σ, z ∈ u.atoms
  · obtain ⟨u, hu, hzu⟩ := h
    rw [stSt_repC_mem hM σ hu hzu]
    obtain ⟨S'', hS''m, _, hu''⟩ := mem_unitBlocks.mp hu
    have hsub := (groupUnitsOf G S'').sub u hu''
    by_cases hSS : S'' = S
    · subst hSS
      exact hsub u.isBlock.2.1
    · exact absurd hz (Finset.disjoint_left.mp (groups_disjoint hM hS''m hSm hSS) (hsub hzu)).elim
  · push Not at h
    rw [stSt_repC_none hM σ h]
    exact hz

/-- An SG group contributes an object to `C_1`. -/
@[expose] def HasObj (G : Garden w) (S : Finset (GBranch G.tree)) : Prop :=
  ((∃ a b, LGSpine.SourceVine.IsHV G.molecule S a b) ∧ ¬ ∃ a b, LGSpine.SourceVine.IsHVC G.molecule S a b) ∨
    ∃ sk : SkipData G S, (groupUnitsOf G S).skip = some sk

/-- The properties of the object of the group `S` in `G_sb`. -/
structure ObjSpec (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    (O : Object (stSt G σ).G.molecule) : Prop where
  allowed : AllowedCollectionObject (stSt G σ).G O
  atoms_sub : ∀ v ∈ O.atoms, ∃ z ∈ S, v = (stSt G σ).M.pi (stSt G σ).hcls z
  hinge : ∀ c, (stSt G σ).cls ((stSt G σ).M.ob c) ≠ none → c ∈ O.atoms → c = O.upper ∨ c = O.lower
  /-- SUBPRO amendment A2: the atoms of the object are exactly the image of a subset `A` of the group, and every
  unmerged atom of the group lies in `A` -/
  src : ∃ A : Finset (GBranch G.tree), A ⊆ S ∧ O.atoms = A.image ((stSt G σ).M.pi (stSt G σ).hcls) ∧
    (∀ z ∈ S, (stSt G σ).cls z = none → z ∈ A) ∧
    ((((∃ a b, LGSpine.SourceVine.IsHV G.molecule S a b) ∧ ¬ ∃ a b, LGSpine.SourceVine.IsHVC G.molecule S a b) ∧
        (groupUnitsOf G S).skip = none ∧
        ∃ a b e, hvGroupPick G S = some (a, b, e) ∧ O.upper = (stSt G σ).M.pi (stSt G σ).hcls a ∧
          O.lower = (stSt G σ).M.pi (stSt G σ).hcls b ∧
          ∃ R : HyperLikeRealization (stSt G σ).G.molecule O.atoms O.upper O.lower,
            O.shape = VineLikeObject.hyper R ∧ (stSt G σ).M.od R.added = e) ∨
      ∃ sk : SkipData G S, (groupUnitsOf G S).skip = some sk ∧ A = sk.A ∧
        O.upper = (stSt G σ).M.pi (stSt G σ).hcls sk.x ∧ O.lower = (stSt G σ).M.pi (stSt G σ).hcls sk.y ∧
        (sk.bond = none → ∃ h, O.shape = VineLikeObject.vc h) ∧
        ∀ e, sk.bond = some e → ∃ R : HyperLikeRealization (stSt G σ).G.molecule O.atoms O.upper O.lower,
          O.shape = VineLikeObject.hyper R ∧ (stSt G σ).M.od R.added = e)

theorem SDecomp.nonmerged_mem {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D}
    {cls : V → Option V} {S A L0 R0 : Finset V} {a b x y : V} (H : SDecomp N cls S A L0 R0 a b x y)
    {z : V} (hz : z ∈ S) (hn : cls z = none) : z ∈ A := by
  have := H.hS
  rw [this] at hz
  rcases mem_union.mp hz with h | h
  · rcases mem_union.mp h with h | h
    · obtain ⟨r, hr, -⟩ := H.hLc z h z h
      rw [hn] at hr; cases hr
    · exact h
  · obtain ⟨r, hr, -⟩ := H.hRc z h z h
    rw [hn] at hr; cases hr

theorem objSpec_of_skip (_hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (sk : SkipData G S) (O : Object (stSt G σ).G.molecule)
    (hO : AllowedCollectionObject (stSt G σ).G O)
    (hOa : O.atoms = sk.A.image ((stSt G σ).M.pi (stSt G σ).hcls))
    (hu : O.upper = (stSt G σ).M.pi (stSt G σ).hcls sk.x)
    (hl : O.lower = (stSt G σ).M.pi (stSt G σ).hcls sk.y)
    (hcase : ∀ z ∈ sk.A, (stSt G σ).cls (((stSt G σ).cls z).getD z) ≠ none → z = sk.x ∨ z = sk.y)
    (hnm : ∀ z ∈ S, (stSt G σ).cls z = none → z ∈ sk.A) (hsk : (groupUnitsOf G S).skip = some sk)
    (hsh1 : sk.bond = none → ∃ h, O.shape = VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : HyperLikeRealization (stSt G σ).G.molecule O.atoms O.upper O.lower,
      O.shape = VineLikeObject.hyper R ∧ (stSt G σ).M.od R.added = e) :
    ObjSpec G σ S O := by
  have hc := (stSt G σ).hcls
  refine ⟨hO, ?_, ?_, ⟨sk.A, ?_, hOa, hnm, Or.inr ⟨sk, hsk, rfl, hu, hl, hsh1, hsh2⟩⟩⟩
  · intro v hv
    rw [hOa] at hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
    have hzS : z ∈ S := by
      rw [sk.hS]
      exact mem_union_left _ (mem_union_right _ hz)
    exact ⟨z, hzS, rfl⟩
  · intro c hcn hcO
    rw [hOa] at hcO
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hcO
    rw [(stSt G σ).M.ob_pi hc] at hcn
    rcases hcase z hz hcn with rfl | rfl
    · exact Or.inl hu.symm
    · exact Or.inr hl.symm
  · intro z hz
    rw [sk.hS]
    exact mem_union_left _ (mem_union_right _ hz)

theorem exists_obj (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG) (h : HasObj G S) :
    ∃ O, ObjSpec G σ S O := by
  have hc := (stSt G σ).hcls
  have hsk_or : (((∃ a b, LGSpine.SourceVine.IsHV G.molecule S a b) ∧
      ¬ ∃ a b, LGSpine.SourceVine.IsHVC G.molecule S a b) ∧ (groupUnitsOf G S).skip = none) ∨
      ∃ sk : SkipData G S, (groupUnitsOf G S).skip = some sk := by
    rcases h with hl | hr
    · rcases hs : (groupUnitsOf G S).skip with _ | sk
      · exact Or.inl ⟨hl, rfl⟩
      · exact Or.inr ⟨sk, rfl⟩
    · exact Or.inr hr
  rcases hsk_or with ⟨⟨⟨a, b, hhv⟩, hnhvc⟩, hnone⟩ | ⟨sk, hsk⟩
  · obtain ⟨a0, b0, e0, hpk, hends, hvine⟩ := hvGroupPick_some ⟨hSm, ⟨a, b, hhv⟩, hnhvc⟩
    obtain ⟨O, hO, hOa, hou, hol, R, hR, hRe⟩ := hv_object hM σ hSm hnhvc hends hvine
    refine ⟨O, hO, ?_, ?_, ⟨S, subset_refl _, hOa, fun z hz _ => hz,
      Or.inl ⟨⟨⟨a, b, hhv⟩, hnhvc⟩, hnone, a0, b0, e0, hpk, hou, hol, R, hR, hRe⟩⟩⟩
    · intro v hv
      rw [hOa] at hv
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨z, hz, rfl⟩
    · intro c hcn hcO
      exfalso
      rw [hOa] at hcO
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hcO
      apply hcn
      rw [(stSt G σ).M.ob_pi hc]
      have hnone := stSt_cls_none hM σ (no_unit_hv hM σ hSm ⟨a, b, hhv⟩ hnhvc hz)
      have hr : repC (stSt G σ).cls z = z := by simp [repC, hnone]
      rw [hr]; exact hnone
  · rcases hb : sk.bond with _ | e
    · obtain ⟨O, hO, hOa, hu, hl, hsh⟩ := vc_object hM σ hSm hσ hsk hb
      have H := skip_sdecomp hM σ hSm hσ hsk G.molecule (sk.skelM hb)
      exact ⟨O, objSpec_of_skip hM σ sk O hO hOa hu hl (fun z hz hn => H.hinge_cases hz hn)
        (fun z hz hn => SDecomp.nonmerged_mem H hz hn) hsk (fun _ => hsh)
        (fun e' he' => by rw [hb] at he'; cases he')⟩
    · obtain ⟨O, hO, hOa, hu, hl, hsh⟩ := hvc_object hM σ hSm hσ hsk hb
      have H := skip_sdecomp hM σ hSm hσ hsk (Mole.eraseBond G.molecule e) (sk.skelN e hb)
      exact ⟨O, objSpec_of_skip hM σ sk O hO hOa hu hl (fun z hz hn => H.hinge_cases hz hn)
        (fun z hz hn => SDecomp.nonmerged_mem H hz hn) hsk (fun h => by rw [hb] at h; cases h)
        (fun e' he' => by
          rw [hb] at he'
          have : e = e' := Option.some.inj he'
          subst this
          exact hsh)⟩

end WaveTurbulence.VineA.NormalizedSplice
