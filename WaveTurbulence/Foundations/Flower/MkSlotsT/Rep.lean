/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsT.Kind
public import WaveTurbulence.Foundations.Flower.MkSlots.Data

/-! # B3s-HELPER5 (γ) T1, part 3: the classification on the representative of a class

For a prescribed point `a` (the representative `repPt π` of a fine′ class) and a fine marking `mkF`, the piece lives on
`G_sb = (stA mkF a).G = (stSt S σ (classMk mkF a)).G` (`S = a.prime.skeleton`, `σ = a.totalSigma`); its units are
`unitsRep mkF a j = unitBlkMk … j` (the runs of `𝒱₀(σ) \ classMk mkF a`), with main's splice shape
`shapeRep mkF a = VineB.stShape …` (`br = (stA mkF a).M.ob`, hinges `= (stA mkF a).hinges`, the piece's
`Cs.hinges`).

* `stemAvoid_of_cleanPt`: B4's `CleanPt J a` is stem avoidance of `𝐀(c)` for every `c ∈ 𝒱₀(σ)`;
* **`stemRet_rep`**: `CleanPt J a ⇒ StemRet` for the units of the piece (each unit carries main's aligned chain
  assembly, whose pieces are vines of `𝒱₀(σ) \ classMk mkF a`, IntAdm's `alignedPiece_mem_vinesV0`);
* **`kindRep`** (the classification function on the representative's reconstruction) and **`kindRep_spec`**: on a
  stem-clean point every node on a capped stem of `a.layered` is exactly one of
  (a) `atom c`: the core branch of `ob c`, `c` a non-hinge branch of `G_sb`;
  (b) `top j`: the core branch of the upper joint of the unit `j`;
  (c) `slot s`: a non-core native node of a retained slot `s`.
  In particular no capped-stem node is a hinge other than a unit upper joint (STOP condition of the brief: absent).
* `onStemAddr_of_mem_stemSetCap`: the capped stem sets `stemSetCap` consist of stem addresses. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.VineB (SpliceShape Ret Disj)
open WaveTurbulence.RedSplice (CLBlock Prescription stSt vinesV0 unitBlocks)
open WaveTurbulence.Flower.MkMark (owner activeSet StemAvoid CapFlowerAt)
open WaveTurbulence.Flower.MkSlots (slotOf stA)

namespace WaveTurbulence.Flower.MkSlotsT

variable {w : ℕ}

/-- The number of units of the piece of `a`. -/
abbrev nUnits (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) : ℕ :=
  (unitBlocks a.prime.skeleton a.totalSigma (classMk mkF a)).length

/-- The units of the piece of `a` (the spliced runs). -/
abbrev unitsRep (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) : Fin (nUnits mkF a) → CLBlock a.prime.skeleton :=
  VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a)

theorem unitsRep_disj (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) : Disj (unitsRep mkF a) :=
  VineB.unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a)

/-- Main's splice shape of the piece of `a` (`br = ob`). -/
abbrev shapeRep (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) : SpliceShape (unitsRep mkF a) (stA mkF a).G :=
  VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a)

theorem shapeRep_br (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    (shapeRep mkF a).br = (stA mkF a).M.ob := rfl

theorem shapeRep_hinges (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    (shapeRep mkF a).hinges (unitsRep_disj mkF a) = (stA mkF a).hinges :=
  VineB.stShape_hingesMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a)

/-- **Stem-cleanness of a prescribed point is stem avoidance of every twist-active set of `𝒱₀(σ)`.** -/
theorem stemAvoid_of_cleanPt {J : Finset (Fin w)} {a : PrescribedPrimeGarden w} (hc : CleanPt J a)
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) :
    ∀ c ∈ vinesV0 a.prime.skeleton a.totalSigma Mk,
      StemAvoid a.layered J (activeSet a.prime.skeleton a.prime.data.tree c.atoms c.upper) := by
  intro c hc0
  exact (MkMark.stemCleanAt_iff J a.prime c.atoms c.upper).mp (hc c (RedSplice.mem_vinesV0.mp hc0).1)

/-- **T1 (retention at the representative).** On a stem-clean point the capped stem meets no interior of a unit of
the piece. -/
theorem stemRet_rep {J : Finset (Fin w)} (mkF : Stage1Mk.MarkFn w) {a : PrescribedPrimeGarden w}
    (hc : CleanPt J a) : StemRet a.prime.skeleton a.prime.data.tree (unitsRep mkF a) a.layered J :=
  stemRet_of_clean a.prime.data.tree (unitsRep mkF a) (vinesV0 a.prime.skeleton a.totalSigma (classMk mkF a))
    (stemAvoid_of_cleanPt hc (classMk mkF a)) (fun j => Represents.unitN a.totalSigma j)
    (fun j => VineAlign.alignedAssemblyMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a) j)
    (fun j i => MkSlots.alignedPiece_mem_vinesV0 a.totalSigma (classMk mkF a) j i)

/-- **The classification function on the representative.** -/
def kindRep (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    GNode (a.prime.data.forest a.prime.prime.1) → StemKind (stA mkF a).G (Fin (nUnits mkF a)) a.prime.skeleton :=
  kindOf a.prime.data a.prime.prime.1 (shapeRep mkF a)

/-- **T1 at the representative.** On a stem-clean point, a node `z` on a capped stem of `a.layered` is the core
branch of a non-hinge atom `c` of `G_sb` (kind `atom c`), the core branch of the upper joint of a unit `j` (kind
`top j`), or a non-core native node of a retained slot `s` (kind `slot s`). -/
theorem kindRep_spec {J : Finset (Fin w)} (mkF : Stage1Mk.MarkFn w) {a : PrescribedPrimeGarden w}
    (hc : CleanPt J a) {z : GNode (a.prime.data.forest a.prime.prime.1)} (hz : OnStemAddr a.layered J z.1) :
    (∀ c : GBranch (stA mkF a).G.tree, (kindRep mkF a z = StemKind.atom c) ↔
      (z = (a.prime.data.coreBranch a.prime.prime.1 ((stA mkF a).M.ob c)).toNode ∧ c ∉ (stA mkF a).hinges)) ∧
    (∀ j : Fin (nUnits mkF a), (kindRep mkF a z = StemKind.top j) ↔
      z = (a.prime.data.coreBranch a.prime.prime.1 (unitsRep mkF a j).upper).toNode) ∧
    (∀ s : ReplacementSlot a.prime.skeleton, (kindRep mkF a z = StemKind.slot s) ↔
      (slotOf a.prime.data a.prime.prime.1 z = s ∧
        ∀ β : GBranch a.prime.skeleton.tree, z ≠ (a.prime.data.coreBranch a.prime.prime.1 β).toNode)) ∧
    SlotRet a.prime.prime.1 (blk := unitsRep mkF a) (slotOf a.prime.data a.prime.prime.1 z) := by
  have h := kindOf_spec a.prime.data a.prime.prime.1 (shapeRep mkF a) (unitsRep_disj mkF a) (stemRet_rep mkF hc) hz
  rw [shapeRep_hinges] at h
  exact h

/-- Members of the capped stem sets are stem addresses. -/
theorem onStemAddr_of_mem_stemSetCap {LG : LayeredGarden w} {J : Finset (Fin w)} {j : Fin w}
    {b : GBranch LG.garden.tree} (hb : b ∈ stemSetCap LG J j) : OnStemAddr LG J b.1 := by
  obtain ⟨-, -, hst, -⟩ := (MkMark.mem_stemSetCap_iff LG J j b).mp hb
  exact hst

/-- Stem addresses only depend on the layered garden through its garden (transport along an equality). -/
theorem onStemAddr_congr {LG LG' : LayeredGarden w} (h : LG = LG') (J : Finset (Fin w)) (z : Address w) :
    OnStemAddr LG J z ↔ OnStemAddr LG' J z := by
  subst h; exact Iff.rfl

end WaveTurbulence.Flower.MkSlotsT
