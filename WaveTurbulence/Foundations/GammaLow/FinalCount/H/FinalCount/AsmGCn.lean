/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGCn
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEnd3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AtMapGarden
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmGCn`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (garden level): the `CnBound` bridge** (census item (f)).

`remMol M₀ ps` for first-stage pieces (the ordinary members of `C₁`, which are CN or root-CL vines by TARGET `subpro` (2) /
`AllowedCollectionObject`) is the universe's `removeBlockFamily G F` (TARGET Prop `cnblock`) up to the renaming `Sum.inl`:
* `pieceKill_iff_inGroup`: for an ordinary piece with two distinct node darts at each joint, a dart or its mate is killed iff it is
  internal to the piece (the node darts are all the internal darts at the joints, `block_joint_darts`);
* `exists_segments`: the pieces give a pairwise-disjoint family `F` of CN / root-CL block segments with the same atoms and joints;
* `numComponents_rename'`, `deg_rename'`: a dart bijection compatible with an injective atom map preserves components and degrees;
* `cnBound_garden`: `cnblock_component_bound` transported; `cnBound_of_garden`: the asm's named input `CnBound`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.AtomTransport WaveTurbulence.MoleProp

section rename
variable {V W : Type*} [DecidableEq V] [DecidableEq W] {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

end rename

section piece
variable {V : Type*} [DecidableEq V] {D₀ : Type*} [Fintype D₀] [DecidableEq D₀]

/-- **Killed darts of an ordinary piece = its internal darts.** -/
theorem pieceKill_iff_inGroup {M : Molecule V D₀} (hM : M.IsMolecule) (P : Src.Object Src.γL M) (N : Quad D₀)
    (hvc : ∃ h, P.shape = .vc h)
    (hCD : P.ContainsDart N.1 ∧ P.ContainsDart N.2.1 ∧ P.ContainsDart N.2.2.1 ∧ P.ContainsDart N.2.2.2)
    (hJ : (M.atom N.1 = P.upper ∧ M.atom N.2.2.1 = P.lower) ∨ (M.atom N.1 = P.lower ∧ M.atom N.2.2.1 = P.upper))
    (hN : M.atom N.2.1 = M.atom N.1 ∧ M.atom N.2.2.2 = M.atom N.2.2.1 ∧ N.1 ≠ N.2.1 ∧ N.2.2.1 ≠ N.2.2.2)
    (z : D₀) : (z ∈ PieceKill P N ∨ M.mate z ∈ PieceKill P N) ↔ M.InGroup P.atoms z := by
  have hB : M.IsBlock P.atoms P.upper P.lower := object_vc_block P hvc
  have hcd : ∀ x, P.ContainsDart x ↔ M.InGroup P.atoms x := by
    obtain ⟨h, hs⟩ := hvc
    intro x
    unfold Src.Object.ContainsDart
    rw [hs]
  have hN4 : ∀ t, t = N.1 ∨ t = N.2.1 ∨ t = N.2.2.1 ∨ t = N.2.2.2 → M.InGroup P.atoms t := by
    rintro t (rfl | rfl | rfl | rfl)
    · exact (hcd _).1 hCD.1
    · exact (hcd _).1 hCD.2.1
    · exact (hcd _).1 hCD.2.2.1
    · exact (hcd _).1 hCD.2.2.2
  -- one direction: killed darts are internal
  have hkill : ∀ t, t ∈ PieceKill P N → M.InGroup P.atoms t := by
    rintro t ⟨hta, himp⟩
    by_cases hj : M.atom t = P.upper ∨ M.atom t = P.lower
    · exact hN4 t (himp hj)
    · push Not at hj
      have h4 := hB.2.2.2.2.2.2.2.2.1 _ hta hj.1 hj.2
      exact ⟨hta, Mole.full_degree_no_exit M hM (hB.1 hta) h4 rfl⟩
  constructor
  · rintro (h | h)
    · exact hkill z h
    · exact (inGroup_mate_iff M _ z).1 (hkill _ h)
  · intro hz
    left
    refine ⟨hz.1, fun hj => ?_⟩
    have hx1 := hN4 _ (Or.inl rfl)
    have hx2 := hN4 _ (Or.inr (Or.inl rfl))
    have hy1 := hN4 _ (Or.inr (Or.inr (Or.inl rfl)))
    have hy2 := hN4 _ (Or.inr (Or.inr (Or.inr rfl)))
    have hjj : M.atom z = M.atom N.1 ∨ M.atom z = M.atom N.2.2.1 := by
      rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hj with h | h
      · exact Or.inl (h.trans e1.symm)
      · exact Or.inr (h.trans e2.symm)
      · exact Or.inr (h.trans e2.symm)
      · exact Or.inl (h.trans e1.symm)
    have hjN1 : M.atom N.1 = P.upper ∨ M.atom N.1 = P.lower := by rcases hJ with ⟨e1, -⟩ | ⟨e1, -⟩ <;> simp [e1]
    have hjN3 : M.atom N.2.2.1 = P.upper ∨ M.atom N.2.2.1 = P.lower := by
      rcases hJ with ⟨-, e2⟩ | ⟨-, e2⟩ <;> simp [e2]
    rcases hjj with h | h
    · rcases block_joint_darts hB hjN1 rfl hN.1 hN.2.2.1 hx1 hx2 h hz with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    · rcases block_joint_darts hB hjN3 rfl hN.2.1 hN.2.2.2 hy1 hy2 h hz with e | e
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr e))

end piece

section garden
variable {R d : ℕ} {G : Garden (2 * R)}

/-- The first-stage objects: the ordinary members of `C₁` (CN / root-CL vines, TARGET `subpro` (2)). -/
def fstG (C : Src.SubproChoices Src.γL G) : Set (Src.Object Src.γL G.molecule) :=
  {U | (∃ i, U = C.collection i) ∧ ∃ h, U.shape = .vc h}

/-- An ordinary allowed object is a CN or root-CL block segment with the same atoms and joints. -/
theorem exists_seg {U : Src.Object Src.γL G.molecule} (hA : Src.AllowedCollectionObject Src.γL G U) (hvc : ∃ h, U.shape = .vc h) :
    ∃ B : Mole.GardenBlockSegment G, B.atoms = U.atoms ∧
      ((B.leftJoint = U.upper ∧ B.rightJoint = U.lower) ∨ (B.leftJoint = U.lower ∧ B.rightJoint = U.upper)) ∧
      Mole.IsCNOrRootCL G B := by
  obtain ⟨h, hs⟩ := hvc
  unfold Src.AllowedCollectionObject Src.γL at hA
  rw [hs] at hA
  obtain ⟨hV, hpat⟩ := hA
  have hB : G.molecule.IsBlock U.atoms U.upper U.lower := hV.block
  rcases hpat with hcn | ⟨hcl | hcl, hdeg⟩
  · exact ⟨Molecpl.currentBlockSegment G hB, rfl, Or.inl ⟨rfl, rfl⟩, Or.inl hcn⟩
  · exact ⟨Molecpl.currentBlockSegment G hB, rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨hcl, hdeg⟩⟩
  · refine ⟨Molecpl.currentBlockSegment G (Mole.block_swap_joints G.molecule hB), rfl, Or.inr ⟨rfl, rfl⟩,
      Or.inr ⟨hcl, ?_⟩⟩
    show G.molecule.deg U.lower + G.molecule.deg U.upper ≤ 6
    omega

/-- The relation between a piece of `inlMol G.molecule` and a block segment of `G`. -/
def SegRel (B : Mole.GardenBlockSegment G) (P : Src.Object Src.γL (inlMol G.molecule)) : Prop :=
  B.atoms.map (inlEmb _) = P.atoms ∧
    ((inlEmb _ B.leftJoint = P.upper ∧ inlEmb _ B.rightJoint = P.lower) ∨
      (inlEmb _ B.leftJoint = P.lower ∧ inlEmb _ B.rightJoint = P.upper)) ∧ Mole.IsCNOrRootCL G B

theorem exists_segments (C : Src.SubproChoices Src.γL G) (hst : C.Structural) (ps : List (Src.Object Src.γL (inlMol G.molecule) × Quad (GardenDart G)))
    (hF : ∀ p ∈ ps, p.1 ∈ objMap (ι := inlEmb _) '' fstG C) (hpw : ps.Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms)) :
    ∃ F : Finset (Mole.GardenBlockSegment G), (∀ B ∈ F, ∃ p ∈ ps, SegRel B p.1) ∧ (∀ p ∈ ps, ∃ B ∈ F, SegRel B p.1) ∧
      Set.PairwiseDisjoint (F : Set (Mole.GardenBlockSegment G)) Mole.GardenBlockSegment.atoms := by
  induction ps with
  | nil => exact ⟨∅, by simp, by simp, by simp⟩
  | cons p ps ih =>
    obtain ⟨hp1, hpw'⟩ := List.pairwise_cons.1 hpw
    obtain ⟨F, h1, h2, h3⟩ := ih (fun q hq => hF q (List.mem_cons_of_mem _ hq)) hpw'
    obtain ⟨U, ⟨⟨i, rfl⟩, hvc⟩, hU⟩ := hF p List.mem_cons_self
    obtain ⟨B, hBa, hBj, hBk⟩ := exists_seg (hst.1 i) hvc
    have hrel : SegRel B p.1 := by
      refine ⟨?_, ?_, hBk⟩
      · rw [← hU, objMap_atoms, hBa]
      · rw [← hU, objMap_upper, objMap_lower]
        rcases hBj with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inl ⟨by rw [e1], by rw [e2]⟩
        · exact Or.inr ⟨by rw [e1], by rw [e2]⟩
    have hdisB : ∀ B' ∈ F, Disjoint B.atoms B'.atoms := by
      intro B' hB'
      obtain ⟨q, hq, hrq⟩ := h1 B' hB'
      have := hp1 q hq
      rw [← hrel.1, ← hrq.1] at this
      exact (Finset.disjoint_map _).1 this
    refine ⟨insert B F, ?_, ?_, ?_⟩
    · intro B' hB'
      rcases Finset.mem_insert.1 hB' with rfl | hB'
      · exact ⟨p, List.mem_cons_self, hrel⟩
      · obtain ⟨q, hq, hr⟩ := h1 B' hB'
        exact ⟨q, List.mem_cons_of_mem _ hq, hr⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨B, Finset.mem_insert_self _ _, hrel⟩
      · obtain ⟨B', hB', hr⟩ := h2 q hq
        exact ⟨B', Finset.mem_insert_of_mem hB', hr⟩
    · rw [Finset.coe_insert]
      exact h3.insert fun B' hB' _ => hdisB B' hB'

/-- **`cnblock` on the renamed molecule.** -/
theorem cnBound_garden (hP : G.IsPlain) (hR : 1 ≤ R) (C : Src.SubproChoices Src.γL G) (hst : C.Structural)
    (ps : List (Src.Object Src.γL (inlMol G.molecule) × Quad (GardenDart G)))
    (hps : ∀ p ∈ ps, p.1 ∈ objMap (ι := inlEmb _) '' fstG C ∧
      (p.1.ContainsDart p.2.1 ∧ p.1.ContainsDart p.2.2.1 ∧ p.1.ContainsDart p.2.2.2.1 ∧ p.1.ContainsDart p.2.2.2.2) ∧
      (((inlMol G.molecule).atom p.2.1 = p.1.upper ∧ (inlMol G.molecule).atom p.2.2.2.1 = p.1.lower) ∨
        ((inlMol G.molecule).atom p.2.1 = p.1.lower ∧ (inlMol G.molecule).atom p.2.2.2.1 = p.1.upper)) ∧
      ((inlMol G.molecule).atom p.2.2.1 = (inlMol G.molecule).atom p.2.1 ∧ (inlMol G.molecule).atom p.2.2.2.2 = (inlMol G.molecule).atom p.2.2.2.1 ∧ p.2.1 ≠ p.2.2.1 ∧
        p.2.2.2.1 ≠ p.2.2.2.2))
    (hpw : ps.Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms)) :
    (remMol (inlMol G.molecule) ps).numComponents ≤ 2 * R ∧
      ((remMol (inlMol G.molecule) ps).numComponents = 2 * R →
        ∃ v ∈ (remMol (inlMol G.molecule) ps).atoms, (remMol (inlMol G.molecule) ps).deg v = 0) := by
  have hM₀ : (inlMol G.molecule).IsMolecule := isMolecule_inl (Mole.garden_isMolecule G)
  obtain ⟨F, hF1, hF2, hdis⟩ := exists_segments C hst ps (fun p hp => (hps p hp).1) hpw
  have hkind : ∀ B ∈ F, Mole.IsCNOrRootCL G B := fun B hB => by
    obtain ⟨p, -, hr⟩ := hF1 B hB; exact hr.2.2
  have hvcp : ∀ p ∈ ps, ∃ h, p.1.shape = .vc h := by
    intro p hp
    obtain ⟨U, ⟨-, hvc⟩, hU⟩ := (hps p hp).1
    rw [← hU]; exact (objMap_shape_vc_iff (inlEmb _) U).2 hvc
  -- darts
  have hdart : ∀ z : GardenDart G, (z ∉ KillS ps ∧ (inlMol G.molecule).mate z ∉ KillS ps) ↔
      ∀ B ∈ F, ¬ G.molecule.InGroup B.atoms z := by
    intro z
    have hp : ∀ p ∈ ps, (z ∈ PieceKill p.1 p.2 ∨ (inlMol G.molecule).mate z ∈ PieceKill p.1 p.2) ↔
        (inlMol G.molecule).InGroup p.1.atoms z :=
      fun p hp => pieceKill_iff_inGroup hM₀ p.1 p.2 (hvcp p hp) (hps p hp).2.1 (hps p hp).2.2.1 (hps p hp).2.2.2 z
    constructor
    · rintro ⟨h1, h2⟩ B hB hin
      obtain ⟨p, hpm, hr⟩ := hF1 B hB
      have : (inlMol G.molecule).InGroup p.1.atoms z := by
        rw [← hr.1]; exact (mapAtoms_inGroup G.molecule (inlEmb _) B.atoms z).2 hin
      rcases (hp p hpm).2 this with h | h
      · exact h1 ⟨p, hpm, h⟩
      · exact h2 ⟨p, hpm, h⟩
    · intro h
      refine ⟨fun ⟨p, hpm, hk⟩ => ?_, fun ⟨p, hpm, hk⟩ => ?_⟩
      · obtain ⟨B, hB, hr⟩ := hF2 p hpm
        apply h B hB
        have hin := (hp p hpm).1 (Or.inl hk)
        rw [← hr.1] at hin
        exact (mapAtoms_inGroup G.molecule (inlEmb _) B.atoms z).1 hin
      · obtain ⟨B, hB, hr⟩ := hF2 p hpm
        apply h B hB
        have hin := (hp p hpm).1 (Or.inr hk)
        rw [← hr.1] at hin
        exact (mapAtoms_inGroup G.molecule (inlEmb _) B.atoms z).1 hin
  -- atoms
  have hatoms : (remMol (inlMol G.molecule) ps).atoms = (Mole.removeBlockFamily G F).atoms.image (inlEmb _) := by
    ext v
    change v ∈ (inlMol G.molecule).atoms.filter (fun v => ∀ p ∈ ps, ¬ PieceInt p.1 v) ↔
      v ∈ (G.molecule.atoms \ Mole.removedBlockInteriors G F).image (inlEmb _)
    rw [Finset.mem_filter, inlMol_atoms, Finset.mem_map, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hni⟩
      refine ⟨a, Finset.mem_sdiff.2 ⟨ha, ?_⟩, rfl⟩
      rw [Mole.mem_removedBlockInteriors]
      rintro ⟨B, hB, haB, hl, hr⟩
      obtain ⟨p, hpm, hrel⟩ := hF1 B hB
      apply hni p hpm
      have hmem : inlEmb _ a ∈ p.1.atoms := by rw [← hrel.1]; exact Finset.mem_map_of_mem _ haB
      rcases hrel.2.1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact ⟨hmem, fun e => hl ((inlEmb _).injective (e.trans e1.symm)),
          fun e => hr ((inlEmb _).injective (e.trans e2.symm))⟩
      · exact ⟨hmem, fun e => hr ((inlEmb _).injective (e.trans e2.symm)),
          fun e => hl ((inlEmb _).injective (e.trans e1.symm))⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨ha, hni⟩ := Finset.mem_sdiff.1 ha
      rw [Mole.mem_removedBlockInteriors] at hni
      refine ⟨⟨a, ha, rfl⟩, fun p hpm hint => hni ?_⟩
      obtain ⟨B, hB, hrel⟩ := hF2 p hpm
      obtain ⟨h1, h2, h3⟩ := hint
      have haB : a ∈ B.atoms := by
        rw [← hrel.1] at h1; exact (Finset.mem_map' (inlEmb _)).1 h1
      refine ⟨B, hB, haB, ?_, ?_⟩
      · intro e; subst e
        rcases hrel.2.1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact h2 e1
        · exact h3 e1
      · intro e; subst e
        rcases hrel.2.1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact h3 e2
        · exact h2 e2
  let e : Mole.BlockFamilyDart G F ≃ {z : GardenDart G // z ∉ KillS ps ∧ (inlMol G.molecule).mate z ∉ KillS ps} :=
    Equiv.subtypeEquivRight (fun z => (hdart z).symm)
  have hinj : ∀ a ∈ (Mole.removeBlockFamily G F).atoms, ∀ b ∈ (Mole.removeBlockFamily G F).atoms, inlEmb _ a = inlEmb _ b → a = b :=
    fun a _ b _ h => (inlEmb _).injective h
  have hatom : ∀ x, (remMol (inlMol G.molecule) ps).atom (e x) = inlEmb _ ((Mole.removeBlockFamily G F).atom x) :=
    fun x => rfl
  have hmate : ∀ x, (remMol (inlMol G.molecule) ps).mate (e x) = e ((Mole.removeBlockFamily G F).mate x) :=
    fun x => rfl
  have hnum := numComponents_rename' e (inlEmb _) hatoms hinj hatom hmate
  obtain ⟨hb1, hb2⟩ := Mole.cnblock_component_bound G hP hR F hdis hkind
  refine ⟨hnum ▸ hb1, fun heq => ?_⟩
  obtain ⟨v, hv, hv0⟩ := hb2 (hnum ▸ heq)
  refine ⟨inlEmb _ v, by rw [hatoms]; exact Finset.mem_image_of_mem _ hv, ?_⟩
  rw [deg_rename' e (inlEmb _) hinj hatom hv, hv0]

end garden

end WaveTurbulence.GammaLow.FinalCount.H
