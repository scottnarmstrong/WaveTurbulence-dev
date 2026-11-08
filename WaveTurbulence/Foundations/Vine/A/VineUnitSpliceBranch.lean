/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceIso
public import WaveTurbulence.Foundations.Vine.A.VineSpliceBranchTrace
public import WaveTurbulence.Foundations.Molecule.TwistParents
/-! Actual selected unit LF twists preserve the signs, roots and parent
relations of branches surviving the actual simultaneous splice. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist
variable {w : ℕ} {G : Garden w}

/-- Unit twists preserve the branching-root predicate. -/
theorem coreBranch_root_iff (P : CorePlacement G) (b : GBranch G.tree) :
    (coreBranchEquiv G P b).1.2 = [] ↔ b.1.2 = [] := by
  classical
  simpa only [not_not] using not_congr (coreBranchEquiv_nonroot G P b)

/-- Actual branching-root addresses are untouched by the concrete unit twist. -/
theorem coreBranch_root_address (P : CorePlacement G) (b : GBranch G.tree) (hb : b.1.2 = []) :
    (coreBranchEquiv G P b).1 = b.1 := by
  apply coreBranchEquiv_fixed_val G P b
  intro hd
  exact P.nonroot (List.prefix_nil.mp (hb ▸ hd.2))

/-- B1b-2 (Mk-general form of `unitSpliceMolIso_branch_sign`). -/
theorem unitSpliceMolIso_branch_signMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    (c : GBranch (stSt G σ Mk).G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ) Mk').G.sign
      ((unitSpliceMolIsoMk Z σ hT hsel).e c).toNode = (stSt G σ Mk).G.sign c.toNode := by
  have hn : (stSt G σ Mk).M.ob c ≠ Z.P.lower :=
    fun he => active_lower_not_survivingMk Z σ hsel ⟨c, he⟩
  calc
    _ = Z.target.sign ((stSt Z.target (transportPrescription Z.iso σ) Mk').M.ob
        ((unitSpliceMolIsoMk Z σ hT hsel).e c)).toNode :=
      (spliceFoldBranchTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).sign _
    _ = Z.target.sign (Z.iso.e ((stSt G σ Mk).M.ob c)).toNode :=
      congrArg (fun b : GBranch Z.target.tree => Z.target.sign b.toNode) (unitSpliceMolIso_branch_namesMk Z σ hT hsel c)
    _ = G.sign ((stSt G σ Mk).M.ob c).toNode :=
      (coreBranchEquiv_sign G Z.P _).trans (ite_eq_right hn)
    _ = _ := ((spliceFoldBranchTrace (unitBlocks G σ Mk)).sign c).symm

/-- The actual spliced branch map preserves signs: its only sign-changing node was deleted. -/
theorem unitSpliceMolIso_branch_sign (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (c : GBranch (stSt G σ).G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ)).G.sign
      ((unitSpliceMolIso Z σ hsel).e c).toNode = (stSt G σ).G.sign c.toNode :=
  unitSpliceMolIso_branch_signMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel c

/-- B1b-2 (Mk-general form of `unitSpliceMolIso_branch_root`). -/
theorem unitSpliceMolIso_branch_rootMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    (c : GBranch (stSt G σ Mk).G.tree) :
    ((unitSpliceMolIsoMk Z σ hT hsel).e c).1.2 = [] ↔ c.1.2 = [] := by
  exact ((stSt Z.target (transportPrescription Z.iso σ) Mk').M.ob_root _).symm.trans
    ((Iff.of_eq (congrArg (fun b : GBranch Z.target.tree => b.1.2 = [])
      (unitSpliceMolIso_branch_namesMk Z σ hT hsel c))).trans
        ((coreBranch_root_iff Z.P _).trans ((stSt G σ Mk).M.ob_root c)))

/-- The actual spliced branch map preserves the root predicate. -/
theorem unitSpliceMolIso_branch_root (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (c : GBranch (stSt G σ).G.tree) :
    ((unitSpliceMolIso Z σ hsel).e c).1.2 = [] ↔ c.1.2 = [] :=
  unitSpliceMolIso_branch_rootMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel c

/-- B1b-2 (Mk-general form of `unitSpliceMolIso_root_address`). -/
theorem unitSpliceMolIso_root_addressMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (c : GBranch (stSt G σ Mk).G.tree)
    (hroot : c.1.2 = []) : ((unitSpliceMolIsoMk Z σ hT hsel).e c).1 = c.1 := by
  have hm := (unitSpliceMolIso_branch_rootMk Z σ hT hsel c).mpr hroot
  have hold := ((stSt G σ Mk).M.ob_root c).mpr hroot
  exact ((spliceFoldBranchTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).root_address _ hm).symm.trans
    ((congrArg Subtype.val (unitSpliceMolIso_branch_namesMk Z σ hT hsel c)).trans
      ((coreBranch_root_address Z.P _ hold).trans
        ((spliceFoldBranchTrace (unitBlocks G σ Mk)).root_address c hroot)))

/-- Actual branching-root addresses are fixed after splicing on both sides of the twist. -/
theorem unitSpliceMolIso_root_address (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (c : GBranch (stSt G σ).G.tree)
    (hroot : c.1.2 = []) : ((unitSpliceMolIso Z σ hsel).e c).1 = c.1 :=
  unitSpliceMolIso_root_addressMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel c hroot

/-- B1b-2 (Mk-general form of `unitSpliceMolIso_parent`). -/
theorem unitSpliceMolIso_parentMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (c : GBranch (stSt G σ Mk).G.tree) (hn : c.1.2 ≠ []) :
    let F := unitSpliceMolIsoMk Z σ hT hsel
    let hnew : (F.e c).1.2 ≠ [] := fun h => hn ((unitSpliceMolIso_branch_rootMk Z σ hT hsel c).mp h)
    F.e (GNode.parent c.toNode hn) = GNode.parent (F.e c).toNode hnew := by
  dsimp only
  let F := unitSpliceMolIsoMk Z σ hT hsel
  let M := (stSt G σ Mk).M
  let N := (stSt Z.target (transportPrescription Z.iso σ) Mk').M
  have hnew : (F.e c).1.2 ≠ [] := fun h => hn ((unitSpliceMolIso_branch_rootMk Z σ hT hsel c).mp h)
  have ho : (M.ob c).1.2 ≠ [] := fun h => hn ((M.ob_root c).mp h)
  have hon : (N.ob (F.e c)).1.2 ≠ [] := fun h => hnew ((N.ob_root (F.e c)).mp h)
  have hne : M.ob c ≠ Z.P.lower := fun he => active_lower_not_survivingMk Z σ hsel ⟨c, he⟩
  have hpn : GNode.parent (N.ob (F.e c)).toNode hon =
      GNode.parent (Z.iso.e (M.ob c)).toNode ((coreBranchEquiv_nonroot G Z.P _).mpr ho) := by
    apply Subtype.ext
    change ((N.ob (F.e c)).1.1, (N.ob (F.e c)).1.2.dropLast) =
      ((Z.iso.e (M.ob c)).1.1, (Z.iso.e (M.ob c)).1.2.dropLast)
    exact congrArg (fun b : GBranch Z.target.tree => (b.1.1, b.1.2.dropLast))
      (unitSpliceMolIso_branch_namesMk Z σ hT hsel c)
  have hp : GNode.parent (N.ob (F.e c)).toNode hon = Z.iso.e (GNode.parent (M.ob c).toNode ho) :=
    hpn.trans (branchParent_transport G Z.P (M.ob c) ho hne)
  apply N.ob_inj
  rw [unitSpliceMolIso_branch_namesMk, M.ob_parent c hn ho, N.ob_parent (F.e c) hnew hon,
    hp]
  exact (unitBlocks_repC_twistMk Z σ hT hsel (GNode.parent (M.ob c).toNode ho)).symm

/-- Every actual retained branching parent agrees through the induced unit-twist quotient. -/
theorem unitSpliceMolIso_parent (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (c : GBranch (stSt G σ).G.tree) (hn : c.1.2 ≠ []) :
    let F := unitSpliceMolIso Z σ hsel
    let hnew : (F.e c).1.2 ≠ [] := fun h => hn ((unitSpliceMolIso_branch_root Z σ hsel c).mp h)
    F.e (GNode.parent c.toNode hn) = GNode.parent (F.e c).toNode hnew :=
  unitSpliceMolIso_parentMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel c hn

/-- B1b-2 (Mk-general form of `unitSpliceMolIso_branch_index`). -/
theorem unitSpliceMolIso_branch_indexMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (c : GBranch (stSt G σ Mk).G.tree) :
    ((unitSpliceMolIsoMk Z σ hT hsel).e c).1.1 = c.1.1 := by
  by_cases hroot : c.1.2 = []
  · exact congrArg Prod.fst (unitSpliceMolIso_root_addressMk Z σ hT hsel c hroot)
  · have hp := unitSpliceMolIso_parentMk Z σ hT hsel c hroot
    have hi := unitSpliceMolIso_branch_indexMk Z σ hT hsel (GNode.parent c.toNode hroot)
    have he := congrArg (fun b : GBranch (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree => b.1.1) hp
    exact he.symm.trans hi
termination_by c.1.2.length
decreasing_by
  change c.1.2.dropLast.length < c.1.2.length
  rw [List.length_dropLast]
  have hpos := List.length_pos_of_ne_nil hroot
  omega

/-- Actual tree indices, hence root-time indices, agree after simultaneous splicing. -/
theorem unitSpliceMolIso_branch_index (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (c : GBranch (stSt G σ).G.tree) :
    ((unitSpliceMolIso Z σ hsel).e c).1.1 = c.1.1 :=
  unitSpliceMolIso_branch_indexMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel c

end WaveTurbulence.VineA
