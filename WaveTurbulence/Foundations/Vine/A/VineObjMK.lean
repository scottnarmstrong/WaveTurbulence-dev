/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSkipMK
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: the objects of `𝒞₁` at `Mk` (one per unmarked SG group with an object)

Mk twins, for an unmarked group (`¬ markedGroup G Mk S`), of `hvc_object`, `no_unit_hv`, `hv_object`
(VineNormalizedRedSpliceObj2) and `exists_obj` (VineNormalizedRedSpliceColl); main's proofs with `unitBlocks G σ Mk`.
`objOf_isSomeMk`: such a group has its object in `objects G σ Mk` (o75 Theorem 7.5′(2): `𝒞₁` = the objects of the
unmarked groups).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1
  WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- The HV of the skipped vine of an SG HVC group. -/
theorem hvc_objectMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG)
    {sk : SkipData G S} (hsk : (groupUnitsOf G S).skip = some sk) {Mk : Set (CLVine G)}
    (hnm : ¬ markedGroup G Mk S) {e : GardenDart G} (hbond : sk.bond = some e) :
    ∃ O : Object (stSt G σ Mk).G.molecule, AllowedCollectionObject (stSt G σ Mk).G O ∧
      O.atoms = sk.A.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) ∧
      O.upper = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls sk.x ∧ O.lower = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls sk.y ∧
      ∃ R : HyperLikeRealization (stSt G σ Mk).G.molecule O.atoms O.upper O.lower,
        O.shape = VineLikeObject.hyper R ∧ (stSt G σ Mk).M.od R.added = e :=
  hyper_objectMk (Mk := Mk) σ (skip_sdecompMk hM σ hSm hσ hsk hnm _ (sk.skelN e hbond)) (sk.blockN e hbond).1
    (sk.vineN e hbond)

/-- No unit meets an HV group. -/
theorem no_unit_hvMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hhv : ∃ a b, LGSpine.SourceVine.IsHV G.molecule S a b)
    (hnhvc : ¬ ∃ a b, LGSpine.SourceVine.IsHVC G.molecule S a b) {Mk : Set (CLVine G)}
    (hnm : ¬ markedGroup G Mk S)
    {v : GBranch G.tree} (hvS : v ∈ S) : ∀ u ∈ unitBlocks G σ Mk, v ∉ u.atoms := by
  intro u hu hv
  obtain ⟨S', hS'm, hσ', hu'⟩ := mem_unitBlocksMk.mp hu
  by_cases hSS : S' = S
  · subst hSS
    rw [groupUnitsMk_of_not_marked hnm, (groupUnitsOf G S').hv_empty hhv hnhvc] at hu'
    simp at hu'
  · have hpart := partition_eq_maximalGroups (stage1Collection_isPartition hM)
    have hdisj : (maximalGroups G.molecule).Pairwise (fun S T => Disjoint S T) := by
      have := (stage1Collection_isPartition hM).2.1
      rwa [hpart] at this
    exact Finset.disjoint_left.mp (hdisj hS'm hSm hSS) (groupUnitsMk_sub hu' hv) hvS

/-- The residual of an SG HV group (not touched by the splice): the canonical triple gives the object. -/
theorem hv_objectMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) {a b : GBranch G.tree} {e : GardenDart G}
    (hnhvc : ¬ ∃ a b, LGSpine.SourceVine.IsHVC G.molecule S a b) {Mk : Set (CLVine G)}
    (hnm : ¬ markedGroup G Mk S)
    (hends : G.molecule.ends e = s(a, b)) (hvine : Vine.IsSomeVine (Mole.eraseBond G.molecule e) S a b) :
    ∃ O : Object (stSt G σ Mk).G.molecule, AllowedCollectionObject (stSt G σ Mk).G O ∧
      O.atoms = S.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) ∧
      O.upper = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a ∧ O.lower = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls b ∧
      ∃ R : HyperLikeRealization (stSt G σ Mk).G.molecule O.atoms O.upper O.lower,
        O.shape = VineLikeObject.hyper R ∧ (stSt G σ Mk).M.od R.added = e := by
  have hab : a ≠ b := hvine.choose_spec.1.2.2.2.1
  have hne : G.molecule.atom e ≠ G.molecule.atom (G.molecule.mate e) := by
    intro h
    unfold Molecule.ends at hends
    rw [h] at hends
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hab (h1.symm.trans h2)
    · exact hab (h2.symm.trans h1)
  have hN := Vine.eraseBond_isMolecule G.molecule hM e hne
  have hnone : ∀ {v : GBranch G.tree}, v ∈ S → ∀ u ∈ unitBlocks G σ Mk, v ∉ u.atoms :=
    fun hv => no_unit_hvMk hM σ hSm ⟨a, b, e, hends, hvine⟩ hnhvc hnm hv
  have hsk : SkelDecomp (Mole.eraseBond G.molecule e) S S ∅ ∅ a b a b :=
    ⟨hN, by simp, hvine.choose_spec.1, hvine.choose_spec.1, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩,
      Finset.disjoint_empty_left _⟩
  have H : SDecomp (Mole.eraseBond G.molecule e) (stSt G σ Mk).cls S S ∅ ∅ a b a b :=
    { toSkelDecomp := hsk
      hcls := (stSt G σ Mk).hcls
      hLcl := fun p v hv => by simp at hv
      hRcl := fun p v hv => by simp at hv
      hLc := fun p hp => by simp at hp
      hRc := fun p hp => by simp at hp
      hNone := fun v hvS _ _ => stSt_cls_noneMk (Mk := Mk) hM σ (hnone hvS) }
  exact hyper_objectMk (Mk := Mk) σ H hends hvine

theorem exists_objMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG) (h : HasObj G S)
    {Mk : Set (CLVine G)} (hnm : ¬ markedGroup G Mk S) :
    ∃ O, ObjSpecMk G σ S Mk O := by
  have hc := (stSt G σ Mk).hcls
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
    obtain ⟨O, hO, hOa, hou, hol, R, hR, hRe⟩ := hv_objectMk hM σ hSm hnhvc hnm hends hvine
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
      rw [(stSt G σ Mk).M.ob_pi hc]
      have hnone := stSt_cls_noneMk (Mk := Mk) hM σ (no_unit_hvMk hM σ hSm ⟨a, b, hhv⟩ hnhvc hnm hz)
      have hr : repC (stSt G σ Mk).cls z = z := by simp [repC, hnone]
      rw [hr]; exact hnone
  · rcases hb : sk.bond with _ | e
    · obtain ⟨O, hO, hOa, hu, hl, hsh⟩ := vc_objectMk hM σ hSm hσ hsk hnm hb
      have H := skip_sdecompMk hM σ hSm hσ hsk hnm G.molecule (sk.skelM hb)
      exact ⟨O, objSpec_of_skipMk hM σ sk (Mk := Mk) O hO hOa hu hl (fun z hz hn => H.hinge_cases hz hn)
        (fun z hz hn => SDecomp.nonmerged_mem H hz hn) hsk (fun _ => hsh)
        (fun e' he' => by rw [hb] at he'; cases he')⟩
    · obtain ⟨O, hO, hOa, hu, hl, hsh⟩ := hvc_objectMk hM σ hSm hσ hsk hnm hb
      have H := skip_sdecompMk hM σ hSm hσ hsk hnm (Mole.eraseBond G.molecule e) (sk.skelN e hb)
      exact ⟨O, objSpec_of_skipMk hM σ sk (Mk := Mk) O hO hOa hu hl (fun z hz hn => H.hinge_cases hz hn)
        (fun z hz hn => SDecomp.nonmerged_mem H hz hn) hsk (fun h => by rw [hb] at h; cases h)
        (fun e' he' => by
          rw [hb] at he'
          have : e = e' := Option.some.inj he'
          subst this
          exact hsh)⟩


/-- **`𝒞₁` at `Mk`: an unmarked SG group with an object has its object in `objects G σ Mk`.** -/
theorem objOf_isSomeMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG) (h : HasObj G S)
    {Mk : Set (CLVine G)} (hnm : ¬ markedGroup G Mk S) :
    ∃ O, objOf G σ S Mk = some O ∧ O ∈ objects G σ Mk := by
  classical
  have hex : G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧ HasObj G S ∧
      ¬ markedGroup G Mk S ∧ ∃ O : Object (stSt G σ Mk).G.molecule, ObjSpecMk G σ S Mk O :=
    ⟨hM, hSm, hσ, h, hnm, exists_objMk hM σ hSm hσ h hnm⟩
  have hO : objOf G σ S Mk = some (Classical.choose hex.2.2.2.2.2) := by
    unfold objOf
    rw [dite_eq_left hex]
  refine ⟨_, hO, ?_⟩
  unfold objects
  exact List.mem_filterMap.mpr ⟨S, mem_sgGroups.mpr ⟨hSm, hσ⟩, hO⟩

end WaveTurbulence.VineA.NormalizedSplice
