/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceObj
public import WaveTurbulence.Foundations.Vine.A.VineGroupPickSpec
import Mathlib.Tactic

/-!
# R83 successor copy: HV objects and normalized candidate selection

Source copy: pinned/r83-RedSpliceObj2.lean; hash recorded in COPIED-SHA256SUMS.
The arbitrary hvPick definition is replaced by VineGroupPickSpec.hvGroupPick.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- B1b (Mk-general form of `hyper_object`). -/
theorem hyper_objectMk (σ : Prescription G) {S A L0 R0 : Finset (GBranch G.tree)} {a b x y : GBranch G.tree}
    {e : GardenDart G}
    {Mk : Set (Stage1.CLVine _)} (H : SDecomp (Mole.eraseBond G.molecule e) (stSt (Mk := Mk) G σ).cls S A L0 R0 a b x y)
    (hends : G.molecule.ends e = s(a, b)) (hvine : Vine.IsSomeVine (Mole.eraseBond G.molecule e) A x y) :
    ∃ O : Object (stSt (Mk := Mk) G σ).G.molecule, AllowedCollectionObject (stSt (Mk := Mk) G σ).G O ∧
      O.atoms = A.image ((stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls) ∧
      O.upper = (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls x ∧ O.lower = (stSt (Mk := Mk) G σ).M.pi (stSt (Mk := Mk) G σ).hcls y ∧
      ∃ R : HyperLikeRealization (stSt (Mk := Mk) G σ).G.molecule O.atoms O.upper O.lower,
        O.shape = VineLikeObject.hyper R ∧ (stSt (Mk := Mk) G σ).M.od R.added = e := by
  have hnc : ¬ ∃ a', (stSt (Mk := Mk) G σ).cls (G.molecule.atom e) = some a' ∧
      (stSt (Mk := Mk) G σ).cls (G.molecule.atom (G.molecule.mate e)) = some a' := by
    unfold Molecule.ends at hends
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact H.ends_not_class
    · rw [h1, h2]
      rintro ⟨r, ha, hb⟩
      exact H.ends_not_class ⟨r, hb, ha⟩
  obtain ⟨e', rfl⟩ := ((stSt (Mk := Mk) G σ).M.od_range e).mpr hnc
  have hc := (stSt (Mk := Mk) G σ).hcls
  let I := H.inducedIso ((stSt (Mk := Mk) G σ).M.eraseMol hc e')
  obtain ⟨X, hX⟩ := hvine
  have hv : Vine.IsSomeVine (Mole.eraseBond (stSt (Mk := Mk) G σ).G.molecule e')
      (A.image ((stSt (Mk := Mk) G σ).M.pi hc)) ((stSt (Mk := Mk) G σ).M.pi hc x) ((stSt (Mk := Mk) G σ).M.pi hc y) :=
    ⟨X, I.isVine hX⟩
  have hobx : (stSt (Mk := Mk) G σ).M.ob ((stSt (Mk := Mk) G σ).M.pi hc x) = ((stSt (Mk := Mk) G σ).cls x).getD x :=
    (stSt (Mk := Mk) G σ).M.ob_pi hc x
  have hoby : (stSt (Mk := Mk) G σ).M.ob ((stSt (Mk := Mk) G σ).M.pi hc y) = ((stSt (Mk := Mk) G σ).cls y).getD y :=
    (stSt (Mk := Mk) G σ).M.ob_pi hc y
  have hpx : (stSt (Mk := Mk) G σ).M.ob ((stSt (Mk := Mk) G σ).G.molecule.atom e') = ((stSt (Mk := Mk) G σ).cls a).getD a ∨
      (stSt (Mk := Mk) G σ).M.ob ((stSt (Mk := Mk) G σ).G.molecule.atom e') = ((stSt (Mk := Mk) G σ).cls b).getD b := by
    rw [(stSt (Mk := Mk) G σ).M.ob_atom e']
    unfold Molecule.ends at hends
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (by rw [h1]; rfl)
    · exact Or.inr (by rw [h1]; rfl)
  have hends' : (stSt (Mk := Mk) G σ).G.molecule.ends e' = s((stSt (Mk := Mk) G σ).M.pi hc x, (stSt (Mk := Mk) G σ).M.pi hc y) := by
    unfold Molecule.ends at hends ⊢
    have hm : (stSt (Mk := Mk) G σ).M.ob ((stSt (Mk := Mk) G σ).G.molecule.atom ((stSt (Mk := Mk) G σ).G.molecule.mate e')) =
        ((stSt (Mk := Mk) G σ).cls (G.molecule.atom (G.molecule.mate ((stSt (Mk := Mk) G σ).M.od e')))).getD
          (G.molecule.atom (G.molecule.mate ((stSt (Mk := Mk) G σ).M.od e'))) := by
      rw [(stSt (Mk := Mk) G σ).M.ob_atom, (stSt (Mk := Mk) G σ).M.od_mate]; rfl
    have h0 : (stSt (Mk := Mk) G σ).M.ob ((stSt (Mk := Mk) G σ).G.molecule.atom e') =
        ((stSt (Mk := Mk) G σ).cls (G.molecule.atom ((stSt (Mk := Mk) G σ).M.od e'))).getD (G.molecule.atom ((stSt (Mk := Mk) G σ).M.od e')) :=
      (stSt (Mk := Mk) G σ).M.ob_atom e'
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at h0; rw [h2] at hm
      have e1 : (stSt (Mk := Mk) G σ).G.molecule.atom e' = (stSt (Mk := Mk) G σ).M.pi hc x :=
        (stSt (Mk := Mk) G σ).M.ob_inj (h0.trans (H.rc_a.trans hobx.symm))
      have e2 : (stSt (Mk := Mk) G σ).G.molecule.atom ((stSt (Mk := Mk) G σ).G.molecule.mate e') = (stSt (Mk := Mk) G σ).M.pi hc y :=
        (stSt (Mk := Mk) G σ).M.ob_inj (hm.trans (H.rc_b.trans hoby.symm))
      rw [e1, e2]
    · rw [h1] at h0; rw [h2] at hm
      have e1 : (stSt (Mk := Mk) G σ).G.molecule.atom e' = (stSt (Mk := Mk) G σ).M.pi hc y :=
        (stSt (Mk := Mk) G σ).M.ob_inj (h0.trans (H.rc_b.trans hoby.symm))
      have e2 : (stSt (Mk := Mk) G σ).G.molecule.atom ((stSt (Mk := Mk) G σ).G.molecule.mate e') = (stSt (Mk := Mk) G σ).M.pi hc x :=
        (stSt (Mk := Mk) G σ).M.ob_inj (hm.trans (H.rc_a.trans hobx.symm))
      rw [e1, e2, Sym2.eq_swap]
  exact ⟨objHyper e' _ _ _ hends' hv, allowed_hyper e' _ _ _ hends' hv, rfl, rfl, rfl, _, rfl, rfl⟩

/-- **The HV residual** of a vine `A` of the adjoint `eraseBond M e` of a decomposed group, in `G_sb`: the vine
`π''A` with the image `e'` of the added bond `e` (TARGET `blockchainprop` and subpro(2): an HVC reduces to an
SG HV; an SG HV is unchanged). -/
theorem hyper_object (σ : Prescription G) {S A L0 R0 : Finset (GBranch G.tree)} {a b x y : GBranch G.tree}
    {e : GardenDart G}
    (H : SDecomp (Mole.eraseBond G.molecule e) (stSt G σ).cls S A L0 R0 a b x y)
    (hends : G.molecule.ends e = s(a, b)) (hvine : Vine.IsSomeVine (Mole.eraseBond G.molecule e) A x y) :
    ∃ O : Object (stSt G σ).G.molecule, AllowedCollectionObject (stSt G σ).G O ∧
      O.atoms = A.image ((stSt G σ).M.pi (stSt G σ).hcls) ∧
      O.upper = (stSt G σ).M.pi (stSt G σ).hcls x ∧ O.lower = (stSt G σ).M.pi (stSt G σ).hcls y ∧
      ∃ R : HyperLikeRealization (stSt G σ).G.molecule O.atoms O.upper O.lower,
        O.shape = VineLikeObject.hyper R ∧ (stSt G σ).M.od R.added = e := hyper_objectMk (Mk := ∅) σ H hends hvine

/-- The HV of the skipped vine of an SG HVC group. -/
theorem hvc_object (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG)
    {sk : SkipData G S} (hsk : (groupUnitsOf G S).skip = some sk) {e : GardenDart G}
    (hbond : sk.bond = some e) :
    ∃ O : Object (stSt G σ).G.molecule, AllowedCollectionObject (stSt G σ).G O ∧
      O.atoms = sk.A.image ((stSt G σ).M.pi (stSt G σ).hcls) ∧
      O.upper = (stSt G σ).M.pi (stSt G σ).hcls sk.x ∧ O.lower = (stSt G σ).M.pi (stSt G σ).hcls sk.y ∧
      ∃ R : HyperLikeRealization (stSt G σ).G.molecule O.atoms O.upper O.lower,
        O.shape = VineLikeObject.hyper R ∧ (stSt G σ).M.od R.added = e :=
  hyper_object σ (skip_sdecomp hM σ hSm hσ hsk _ (sk.skelN e hbond)) (sk.blockN e hbond).1 (sk.vineN e hbond)

/-- No unit meets an HV group. -/
theorem no_unit_hv (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) (hhv : ∃ a b, LGSpine.SourceVine.IsHV G.molecule S a b)
    (hnhvc : ¬ ∃ a b, LGSpine.SourceVine.IsHVC G.molecule S a b)
    {v : GBranch G.tree} (hvS : v ∈ S) : ∀ u ∈ unitBlocks G σ, v ∉ u.atoms := by
  intro u hu hv
  obtain ⟨S', hS'm, hσ', hu'⟩ := mem_unitBlocks.mp hu
  by_cases hSS : S' = S
  · subst hSS
    rw [(groupUnitsOf G S').hv_empty hhv hnhvc] at hu'
    simp at hu'
  · have hpart := partition_eq_maximalGroups (stage1Collection_isPartition hM)
    have hdisj : (maximalGroups G.molecule).Pairwise (fun S T => Disjoint S T) := by
      have := (stage1Collection_isPartition hM).2.1
      rwa [hpart] at this
    exact Finset.disjoint_left.mp (hdisj hS'm hSm hSS) ((groupUnitsOf G S').sub u hu' hv) hvS

/-- The residual of an SG HV group (not touched by the splice): the canonical triple gives the object. -/
theorem hv_object (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) {a b : GBranch G.tree} {e : GardenDart G}
    (hnhvc : ¬ ∃ a b, LGSpine.SourceVine.IsHVC G.molecule S a b)
    (hends : G.molecule.ends e = s(a, b)) (hvine : Vine.IsSomeVine (Mole.eraseBond G.molecule e) S a b) :
    ∃ O : Object (stSt G σ).G.molecule, AllowedCollectionObject (stSt G σ).G O ∧
      O.atoms = S.image ((stSt G σ).M.pi (stSt G σ).hcls) ∧
      O.upper = (stSt G σ).M.pi (stSt G σ).hcls a ∧ O.lower = (stSt G σ).M.pi (stSt G σ).hcls b ∧
      ∃ R : HyperLikeRealization (stSt G σ).G.molecule O.atoms O.upper O.lower,
        O.shape = VineLikeObject.hyper R ∧ (stSt G σ).M.od R.added = e := by
  have hab : a ≠ b := hvine.choose_spec.1.2.2.2.1
  have hne : G.molecule.atom e ≠ G.molecule.atom (G.molecule.mate e) := by
    intro h
    unfold Molecule.ends at hends
    rw [h] at hends
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hab (h1.symm.trans h2)
    · exact hab (h2.symm.trans h1)
  have hN := Vine.eraseBond_isMolecule G.molecule hM e hne
  have hnone : ∀ {v : GBranch G.tree}, v ∈ S → ∀ u ∈ unitBlocks G σ, v ∉ u.atoms :=
    fun hv => no_unit_hv hM σ hSm ⟨a, b, e, hends, hvine⟩ hnhvc hv
  have hsk : SkelDecomp (Mole.eraseBond G.molecule e) S S ∅ ∅ a b a b :=
    ⟨hN, by simp, hvine.choose_spec.1, hvine.choose_spec.1, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩,
      Finset.disjoint_empty_left _⟩
  have H : SDecomp (Mole.eraseBond G.molecule e) (stSt G σ).cls S S ∅ ∅ a b a b :=
    { toSkelDecomp := hsk
      hcls := (stSt G σ).hcls
      hLcl := fun p v hv => by simp at hv
      hRcl := fun p v hv => by simp at hv
      hLc := fun p hp => by simp at hp
      hRc := fun p hp => by simp at hp
      hNone := fun v hvS _ _ => stSt_cls_none hM σ (hnone hvS) }
  exact hyper_object σ H hends hvine

end WaveTurbulence.VineA.NormalizedSplice
