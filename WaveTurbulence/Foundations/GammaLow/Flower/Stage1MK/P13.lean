/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Bridge
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P1
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P2
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P3
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P4
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P6
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P7
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P8
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P9
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P10
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Iface
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P11
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P12
public import WaveTurbulence.Foundations.Vine.A.VineSurvSGMK
public import WaveTurbulence.Foundations.Vine.A.VineSurvPairMK
public import WaveTurbulence.Foundations.Vine.A.VineHingePairMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproItemsMK
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceTripleDesigMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SurvConnMK
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK4
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK5
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproContainedMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCrossMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproSupportMK
public import WaveTurbulence.Foundations.Flower.MkSubpro.Survivors
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Zero
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Assembly
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.SurvCount
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Pieces
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Gate
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Prefix
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Unclean
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects

/-! # FLOWER-LOW (packet L8), item I (wave 13): marked Stage-1′ declarations over `𝒱_γ`

Item-I declarations of L8's sub-areas (I-BASE, I-GATE) that became portable after the latest publications, copied
by source (sha256 in COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **A bond of a survivor lifts to a bond of its image object** (both shapes; for the 75-W1 HV, the added bond is not
a survivor bond). -/
theorem survObj_containsDartLow {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ Fama.survivorsMk γF G σ Mk) {y : GardenDart (Fama.stSt γF G σ Mk).G}
    (hy : G.molecule.InGroup t.1 ((Fama.stSt γF G σ Mk).M.od y)) : (survObjLow ht).ContainsDart y := by
  obtain ⟨hat, -⟩ := survObj_specLow ht
  have hg : (Fama.stSt γF G σ Mk).G.molecule.InGroup (survObjLow ht).atoms y := by
    refine ⟨?_, ?_⟩
    · rw [atom_liftLow hM σ, hat]
      exact Finset.mem_image_of_mem _ hy.1
    · rw [atom_liftLow hM σ, hat, (Fama.stSt γF G σ Mk).M.od_mate]
      exact Finset.mem_image_of_mem _ hy.2
  unfold Src.Object.ContainsDart
  split
  · exact hg
  · rename_i R hR
    refine ⟨fun h => ?_, fun h => ?_, hg⟩
    · exact survObj_hyper_addedLow ht hR (h ▸ hy)
    · apply survObj_hyper_addedLow ht hR
      rw [h, (Fama.stSt γF G σ Mk).M.od_mate] at hy
      exact ⟨by simpa only [G.molecule.mate_mate] using hy.2, hy.1⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **No survivor has a joint at a hinge of an unmarked group** (survivors lie in marked groups). -/
theorem not_survPairAt_of_unmarkedLow {S : Finset (GBranch G.tree)} (hSm : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hnm : ¬ Fama.markedGroup γF G Mk S) {u : CLBlock G} (hu : u ∈ Fama.groupUnitsMk γF G Mk S)
    {v : GBranch (Fama.stSt γF G σ Mk).G.tree} (hcr : (Fama.stSt γF G σ Mk).M.ob v = u.upper) :
    ¬ ∃ q, Fama.VineA.NormalizedSplice.survPairAt γF G σ v = some q := by
  classical
  rintro ⟨q, hq⟩
  unfold Fama.VineA.NormalizedSplice.survPairAt at hq
  obtain ⟨Tj, hTj, -⟩ := Option.bind_eq_some_iff.mp hq
  unfold Fama.VineA.NormalizedSplice.survJointAt at hTj
  obtain ⟨t, ht, -⟩ := Option.map_eq_some_iff.mp hTj
  have htm := List.mem_of_find?_eq_some ht
  have hp := List.find?_some ht
  obtain ⟨S', hS', -, hmk, htS, htsub⟩ := survivorsMk_groupLow htm
  have hends := Fama.isSomeVine_ends ((markedUnitsOfMKLow hmk).surv_spec t htS).1
  have huB : u ∈ Fama.unitBlocks γF G σ Mk := Fama.mem_unitBlocksMk.mpr ⟨S, hSm, hσ, hu⟩
  have hvu := pi_of_crownLow hM σ huB hcr u.isBlock.2.1
  have huS : u.upper ∈ S := Fama.groupUnitsMk_sub hu u.isBlock.2.1
  have hvj : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.2 = v ∨
      (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1 = v := by simpa using hp
  rcases hvj with h | h
  · have := group_eq_of_pi_eqLow hM σ hS' hSm (htsub hends.2.1) huS (h.trans hvu.symm)
    subst this
    exact hnm hmk
  · have := group_eq_of_pi_eqLow hM σ hS' hSm (htsub hends.1) huS (h.trans hvu.symm)
    subst this
    exact hnm hmk

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- A hinge that is an atom of an object of `𝒞₁` is the crown of a unit of an unmarked group. -/
theorem unmarked_hinge_of_objLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    {v : GBranch (Fama.stSt γF G σ Mk).G.tree} (hv : v ∈ (Fama.stSt γF G σ Mk).hinges)
    {O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule} (hOm : O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk) (hvO : v ∈ O.atoms) :
    ∃ S, S ∈ Fama.maximalGroupsG γF G.molecule ∧ σ S = Molecule.GapKind.SG ∧ ¬ Fama.markedGroup γF G Mk S ∧
      ∃ u ∈ (Fama.groupUnitsOf γF G S).units, (Fama.stSt γF G σ Mk).M.ob v = u.upper := by
  obtain ⟨S, hSm, hσ, u, hu, hcr⟩ := hinge_groupMkLow hM σ hv
  obtain ⟨S', hS', hnm', hsub⟩ := mem_objects_groupLow hOm
  obtain ⟨z', hz', hvz'⟩ := hsub v hvO
  have huB : u ∈ Fama.unitBlocks γF G σ Mk := Fama.mem_unitBlocksMk.mpr ⟨S, hSm, hσ, hu⟩
  have hvu := pi_of_crownLow hM σ huB hcr u.isBlock.2.1
  have hSS : S = S' := group_eq_of_pi_eqLow hM σ hSm hS' (Fama.groupUnitsMk_sub hu u.isBlock.2.1) hz' (hvu.trans hvz')
  subst hSS
  exact ⟨S, hSm, hσ, hnm', u, Fama.groupUnitsMk_of_not_marked hnm' ▸ hu, hcr⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **One step inside a survivor**: from an unmerged atom of a survivor image off its joints, every bond of `G_sb`
leads back into the survivor image. -/
theorem survObj_stepLow {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ Fama.survivorsMk γF G σ Mk) {p : GBranch (Fama.stSt γF G σ Mk).G.tree} (hp : p ∈ (survObjLow ht).atoms)
    (hpH : p ∉ (Fama.stSt γF G σ Mk).hinges) (hpu : p ≠ (survObjLow ht).upper) (hpl : p ≠ (survObjLow ht).lower)
    {y : GardenDart (Fama.stSt γF G σ Mk).G} (hy : (Fama.stSt γF G σ Mk).G.molecule.atom y = p) :
    (Fama.stSt γF G σ Mk).G.molecule.atom ((Fama.stSt γF G σ Mk).G.molecule.mate y) ∈ (survObjLow ht).atoms := by
  obtain ⟨hat, hup, hlo, -⟩ := survObj_specLow ht
  obtain ⟨S, -, -, hmk, htm, -⟩ := survivorsMk_groupLow ht
  obtain ⟨hvine, -, -⟩ := (markedUnitsOfMKLow hmk).surv_spec t htm
  have hX := hvine
  have hB := (Src.isBlock_of_isSomeVine hX)
  rw [hat] at hp
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
  have hzn := unmerged_of_not_hingeLow hM σ hpH
  have hz1 : z ≠ t.2.1 := fun h => hpu (by rw [hup, h])
  have hz2 : z ≠ t.2.2 := fun h => hpl (by rw [hlo, h])
  have h4 := hB.2.2.2.2.2.2.2.2.1 z hz hz1 hz2
  have hod : G.molecule.atom ((Fama.stSt γF G σ Mk).M.od y) = z :=
    eq_of_pi_eq_unmergedLow hM σ hzn ((atom_liftLow hM σ).symm.trans hy)
  have hg := inGroup_of_degIn_four hM (hB.1 hz) h4 hod
  rw [atom_liftLow hM σ, (Fama.stSt γF G σ Mk).M.od_mate, hat]
  exact Finset.mem_image_of_mem _ hg.2

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **o75 §4.5(d)**: an object of `G_sb` made of images of atoms of a marked SG group, avoiding the hinges and the
survivor joints, lies in one survivor. -/
theorem obj_in_survivorLow {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hmk : Fama.markedGroup γF G Mk S) (P : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule)
    (hPS : ∀ p ∈ P.atoms, ∃ z ∈ S, p = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls z)
    (hH : Disjoint P.atoms (Fama.stSt γF G σ Mk).hinges)
    (hJ : ∀ t (ht : t ∈ Fama.survivorsMk γF G σ Mk), (survObjLow ht).upper ∉ P.atoms ∧ (survObjLow ht).lower ∉ P.atoms) :
    ∃ t, ∃ ht : t ∈ Fama.survivorsMk γF G σ Mk, P.atoms ⊆ (survObjLow ht).atoms := by
  classical
  have hp0 : P.upper ∈ P.atoms := obj_joint_memLow P (Or.inl rfl)
  obtain ⟨z0, hz0S, hz0⟩ := hPS _ hp0
  have hz0n : (Fama.stSt γF G σ Mk).cls z0 = none :=
    unmerged_of_not_hingeLow hM σ (hz0 ▸ Finset.disjoint_left.mp hH hp0)
  rcases (markedUnitsOfMKLow hmk).partition z0 hz0S with ⟨u, hu, hz0u⟩ | ⟨t, htm, hz0t⟩
  · exfalso
    have huB : u ∈ Fama.unitBlocks γF G σ Mk :=
      Fama.mem_unitBlocksMk.mpr ⟨S, hS, hσ, (groupUnitsMk_of_markedMKLow hmk).symm ▸ hu⟩
    rw [Fama.stSt_cls_memMk (Mk := Mk) hM σ huB hz0u] at hz0n
    cases hz0n
  have ht : t ∈ Fama.survivorsMk γF G σ Mk := mem_survivorsMk_iffMKLow.mpr ⟨S, hS, hσ, hmk, htm⟩
  refine ⟨t, ht, ?_⟩
  obtain ⟨hat, -⟩ := survObj_specLow ht
  have hp0T : P.upper ∈ (survObjLow ht).atoms := by rw [hat, hz0]; exact Finset.mem_image_of_mem _ hz0t
  -- one step of `P` stays in the survivor
  have step : ∀ a b, a ∈ P.atoms → a ∈ (survObjLow ht).atoms → ∀ x : GardenDart (Fama.stSt γF G σ Mk).G,
      (Fama.stSt γF G σ Mk).G.molecule.atom x = a → (Fama.stSt γF G σ Mk).G.molecule.atom ((Fama.stSt γF G σ Mk).G.molecule.mate x) = b →
      b ∈ (survObjLow ht).atoms := by
    intro a b haP haT x hx hxb
    rw [← hxb]
    exact survObj_stepLow hM σ ht haT (Finset.disjoint_left.mp hH haP)
      (fun h => (hJ t ht).1 (h ▸ haP)) (fun h => (hJ t ht).2 (h ▸ haP)) hx
  have key : ∀ a b, Relation.EqvGen (fun a b => ∃ x, (Fama.stSt γF G σ Mk).G.molecule.InGroup P.atoms x ∧
      (Fama.stSt γF G σ Mk).G.molecule.atom x = a ∧ (Fama.stSt γF G σ Mk).G.molecule.atom ((Fama.stSt γF G σ Mk).G.molecule.mate x) = b)
      a b → (a ∈ (survObjLow ht).atoms ↔ b ∈ (survObjLow ht).atoms) := by
    intro a b h
    induction h with
    | rel a b hr =>
      obtain ⟨x, hx, h1, h2⟩ := hr
      constructor
      · intro haT
        exact step a b (h1 ▸ hx.1) haT x h1 h2
      · intro hbT
        refine step b a (h2 ▸ hx.2) hbT ((Fama.stSt γF G σ Mk).G.molecule.mate x) h2 ?_
        rw [(Fama.stSt γF G σ Mk).G.molecule.mate_mate]; exact h1
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  intro q hq
  exact (key _ _ (obj_connectedLow P _ hp0 q hq)).mp hp0T

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- The image of an unmerged unmarked group is disjoint from every survivor (survivors lie in marked groups). -/
theorem image_disjoint_survObjLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    {g : Finset (GBranch G.tree)} (hg : g ∈ Fama.maximalGroupsG γF G.molecule) (hnm : ¬ Fama.markedGroup γF G Mk g)
    (hall : ∀ z0 ∈ g, (Fama.stSt γF G σ Mk).cls z0 = none)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ Fama.survivorsMk γF G σ Mk) :
    Disjoint (g.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls)) (survObjLow ht).atoms := by
  obtain ⟨hat, -⟩ := survObj_specLow ht
  obtain ⟨S, hS, -, hmk, -, htS⟩ := survivorsMk_groupLow ht
  rw [hat, Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨z1, hz1, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨z2, hz2, he⟩ := Finset.mem_image.mp hv'
  have h21 : z2 = z1 := eq_of_pi_eq_unmergedLow hM σ (hall z1 hz1) he
  have hz1S : z1 ∈ S := h21 ▸ htS hz2
  have hgS : g = S := by
    by_contra hne
    exact Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hg hS hne) hz1 hz1S
  exact hnm (hgS ▸ hmk)

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- Main's `Fama.VineA.NormalizedSplice.gapSpecification_pair_of_object` for an unmarked group of the marked splice. -/
theorem gapSpecification_pair_of_objectMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {Mk : Set (Fama.CLVineG γF G)} {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hnm : ¬ Fama.markedGroup γF G Mk S) :
    ∃ a O, Fama.VineA.NormalizedSplice.groupJoint γF G S = some a ∧ Fama.VineA.NormalizedSplice.designatedObject γF G S = some O ∧
      ∃ e : LocalGapSpecification (Fama.stSt γF G σ Mk).G ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a),
        Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a) = some e ∧ e.kind = σ S ∧
        (((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a ∉ (Fama.stSt γF G σ Mk).hinges →
          (a = O.upper ∨ a = O.lower) ∧ O.ContainsDart ((Fama.stSt γF G σ Mk).M.od e.first) ∧
            O.ContainsDart ((Fama.stSt γF G σ Mk).M.od e.second)) ∧
        ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a ∈ (Fama.stSt γF G σ Mk).hinges →
          Fama.VineA.NormalizedSplice.HingeSpec γF G S a ((Fama.stSt γF G σ Mk).M.od e.first, (Fama.stSt γF G σ Mk).M.od e.second))) := by
  obtain ⟨a, ha, e, he, hk, p, h1, h2, hnh⟩ := gapSpecificationMk_groupLow hM σ hS hnm
  obtain ⟨a', O, ha', hO, -⟩ := Fama.VineA.NormalizedSplice.designatedObject_spec hS
  rw [ha] at ha'
  cases ha'
  refine ⟨a, O, ha, hO, e, he, hk, fun h => ?_, fun h => ?_⟩
  · obtain ⟨-, hsp⟩ := hnh.2 h
    unfold Fama.VineA.NormalizedSplice.IntSpec at hsp
    obtain ⟨a1, O1, ha1, hO1, hOj, -, hx, hy⟩ := hsp
    rw [ha] at ha1; cases ha1
    rw [hO] at hO1; cases hO1
    rw [h1, h2]
    exact ⟨hOj, hx, hy⟩
  · obtain ⟨-, hsp⟩ := hnh.1 h
    rw [h1, h2]
    exact hsp

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- Every survivor object is listed in `survObjsLow`. -/
theorem survObj_mem_getLow {σ : Prescription G} {Mk : Set (Fama.CLVineG γF G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ Fama.survivorsMk γF G σ Mk) :
    ∃ i, (survObjsLow G σ Mk).get i = survObjLow ht := by
  have hmem : survObjLow ht ∈ survObjsLow G σ Mk := by
    unfold survObjsLow
    exact List.mem_map.mpr ⟨⟨t, ht⟩, List.mem_attach _ _, rfl⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
  exact ⟨i, hi⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- **The zero piece of a prescribed point**: empty marked set (no survivors), `nProt = 0`, no pins or filters,
indicator `1`. -/
def zeroPieceLow (P : WTParams) [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (a : Fama.VineA.PrescribedPrimeGarden P.γ (2 * R)) : Stage1PieceMKG P R :=
  stage1PieceMKOfLow P a.prime.prime.1 a.layered a.prime.decodes a.totalSigma ∅ ∅ 0 (fun _ => none)
    (fun _ => none) (fun _ => 1)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

theorem zeroPiece_mLow (P : WTParams) [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (a : Fama.VineA.PrescribedPrimeGarden P.γ (2 * R)) : (zeroPieceLow P a).surv.m = 0 := by
  show (survObjsLow a.prime.skeleton a.totalSigma ∅).length = 0
  rw [survObjs_lengthLow, Fama.survivorsMk_empty]
  rfl

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

theorem zeroPiece_restLow (P : WTParams) [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (a : Fama.VineA.PrescribedPrimeGarden P.γ (2 * R)) (cθ : ℝ) :
    MkPieceRestLow (zeroPieceLow P a) cθ where
  survivors_card := by rw [zeroPiece_mLow]; exact Nat.zero_le _
  prot_card := (Finset.card_eq_zero.mpr rfl).trans_le (Nat.zero_le _)
  fix_prot := fun b hb => by simp [zeroPieceLow, stage1PieceMKOfLow] at hb
  fix_layer := fun b t hb => by simp [zeroPieceLow, stage1PieceMKOfLow] at hb
  filt_ok := fun a q hq => by simp [zeroPieceLow, stage1PieceMKOfLow] at hq
  ind_ok := fun k => by simp [zeroPieceLow, stage1PieceMKOfLow]
  ind_local := fun k k' _ => rfl
  lb_free := fun b hb => by simp [zeroPieceLow, stage1PieceMKOfLow] at hb
  lb_prot := fun b hb => by simp [zeroPieceLow, stage1PieceMKOfLow] at hb
  lb_layer := fun b x hb => by simp [zeroPieceLow, stage1PieceMKOfLow] at hb

end

end WaveTurbulence.GammaLow.Flower
