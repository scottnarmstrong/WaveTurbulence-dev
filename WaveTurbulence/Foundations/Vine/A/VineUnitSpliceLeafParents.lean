/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceLeaves
/-! The full surviving-leaf correspondence preserves actual roots, all
parent incidences and tree indices across selected simultaneous LF splices. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist
variable {w : ℕ} {G : Garden w}

/-- The concrete LF map fixes every trivial-root leaf address. -/
theorem coreLeaf_root_address (P : CorePlacement G) (q : GLeaf G.tree) (hq : q.1.2 = []) :
    (coreLeafEquiv G P q).1 = q.1 := by
  have hd : ¬ (q.1.1 = P.lower.1.1 ∧ P.lower.1.2 <+: q.1.2) :=
    fun h => P.nonroot (List.prefix_nil.mp (hq ▸ h.2))
  have hn : q.1 ≠ (G.pair P.retained).1 := by
    intro he
    exact P.paired_nonroot ((congrArg Prod.snd he).symm.trans hq)
  rw [coreLeafEquiv_address]
  simp only [exchangeAddress, hd, hn, ↓reduceIte]

/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_root_address`). -/
theorem unitSpliceLeafEquiv_root_addressMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt G σ Mk).G.tree)
    (hq : q.1.2 = []) : (unitSpliceLeafEquivMk Z σ hT hsel q).1 = q.1 := by
  have hnew := (unitSpliceLeafEquiv_rootMk Z σ hT hsel q).mpr hq
  have ho := ((spliceFoldLeafTrace (unitBlocks G σ Mk)).root q).mpr hq
  exact ((spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).root_address _ hnew).symm.trans
    ((congrArg Subtype.val (unitSpliceLeafEquiv_namesMk Z σ hT hsel q)).trans
      ((coreLeaf_root_address Z.P _ ho).trans ((spliceFoldLeafTrace (unitBlocks G σ Mk)).root_address q hq)))

/-- Actual full-leaf roots retain their literal addresses after both simultaneous splices. -/
theorem unitSpliceLeafEquiv_root_address (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree)
    (hq : q.1.2 = []) : (unitSpliceLeafEquiv Z σ hsel q).1 = q.1 :=
  unitSpliceLeafEquiv_root_addressMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel q hq

/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_parent`). -/
theorem unitSpliceLeafEquiv_parentMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt G σ Mk).G.tree) (hn : q.1.2 ≠ []) :
    let e := unitSpliceLeafEquivMk Z σ hT hsel
    let hnew : (e q).1.2 ≠ [] := fun h => hn ((unitSpliceLeafEquiv_rootMk Z σ hT hsel q).mp h)
    (unitSpliceMolIsoMk Z σ hT hsel).e (GNode.parent q.toNode hn) = GNode.parent (e q).toNode hnew := by
  dsimp only
  let e := unitSpliceLeafEquivMk Z σ hT hsel
  let T := spliceFoldLeafTrace (unitBlocks G σ Mk)
  let U := spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')
  let M := (stSt G σ Mk).M
  let N := (stSt Z.target (transportPrescription Z.iso σ) Mk').M
  have hnew : (e q).1.2 ≠ [] := fun h => hn ((unitSpliceLeafEquiv_rootMk Z σ hT hsel q).mp h)
  have ho : (T.leaf q).1.2 ≠ [] := fun h => hn ((T.root q).mp h)
  have hon : (U.leaf (e q)).1.2 ≠ [] := fun h => hnew ((U.root (e q)).mp h)
  have hne : T.leaf q ≠ G.pair Z.P.retained := fun he => active_pair_not_survivingMk Z σ hsel ⟨q, he⟩
  have hpn : GNode.parent (U.leaf (e q)).toNode hon =
      GNode.parent (coreLeafEquiv G Z.P (T.leaf q)).toNode ((coreLeafEquiv_nonroot G Z.P _).mpr ho) := by
    apply Subtype.ext
    change ((U.leaf (e q)).1.1, (U.leaf (e q)).1.2.dropLast) =
      ((coreLeafEquiv G Z.P (T.leaf q)).1.1, (coreLeafEquiv G Z.P (T.leaf q)).1.2.dropLast)
    exact congrArg (fun l : GLeaf Z.target.tree => (l.1.1, l.1.2.dropLast))
      (unitSpliceLeafEquiv_namesMk Z σ hT hsel q)
  have hp : GNode.parent (U.leaf (e q)).toNode hon = Z.iso.e (GNode.parent (T.leaf q).toNode ho) :=
    hpn.trans (leafParent_transport G Z.P (T.leaf q) ho hne)
  apply N.ob_inj
  exact (unitSpliceMolIso_branch_namesMk Z σ hT hsel (GNode.parent q.toNode hn)).trans
    ((congrArg Z.iso.e (T.parent q hn ho)).trans
      ((unitBlocks_repC_twistMk Z σ hT hsel (GNode.parent (T.leaf q).toNode ho)).symm.trans
        ((congrArg (repC (stSt Z.target (transportPrescription Z.iso σ) Mk').cls) hp).symm.trans
          (U.parent (e q) hnew hon).symm)))

/-- The full leaf map intertwines every actual surviving parent, including non-LP leaves. -/
theorem unitSpliceLeafEquiv_parent (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree) (hn : q.1.2 ≠ []) :
    let e := unitSpliceLeafEquiv Z σ hsel
    let hnew : (e q).1.2 ≠ [] := fun h => hn ((unitSpliceLeafEquiv_root Z σ hsel q).mp h)
    (unitSpliceMolIso Z σ hsel).e (GNode.parent q.toNode hn) = GNode.parent (e q).toNode hnew :=
  unitSpliceLeafEquiv_parentMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel q hn

/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_index`). -/
theorem unitSpliceLeafEquiv_indexMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt G σ Mk).G.tree) :
    (unitSpliceLeafEquivMk Z σ hT hsel q).1.1 = q.1.1 := by
  by_cases hroot : q.1.2 = []
  · exact congrArg Prod.fst (unitSpliceLeafEquiv_root_addressMk Z σ hT hsel q hroot)
  · have hp := unitSpliceLeafEquiv_parentMk Z σ hT hsel q hroot
    have hi := unitSpliceMolIso_branch_indexMk Z σ hT hsel (GNode.parent q.toNode hroot)
    have he := congrArg (fun b : GBranch (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree => b.1.1) hp
    exact he.symm.trans hi

/-- Tree indices of all actual surviving leaves, hence their root-time indices, agree. -/
theorem unitSpliceLeafEquiv_index (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree) :
    (unitSpliceLeafEquiv Z σ hsel q).1.1 = q.1.1 :=
  unitSpliceLeafEquiv_indexMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel q

end WaveTurbulence.VineA
