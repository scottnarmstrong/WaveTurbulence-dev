/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.StemW1

/-! # B3s-HELPER7 WP4 (part 2): the stem/selection weight of a reconstruction, factorized

On the reconstruction `LG = layeredReconstruction D hS layer hLayer` of a plain skeleton `S`, with units
`blk : ι → CLBlock S` (`Disj blk`), a splice shape `Φ : SpliceShape blk Gsb` and γ's stem retention `StemRet`
(the capped stem meets no unit interior), at the coset decoration of any decoration `κ` of the reconstructed garden:

**`genWeight_factor`**: σ's capped stem filters times the selected-face weights at the intrinsic selected vertices are
* the selection constant `∏_j [v_j] Rs_j⁻¹`,
* times the CORE part: `genNW` at the cores of the non-hinge `G_sb` atoms and of the unit uppers, at the skeleton
  resonance factors of the collapsed decoration `collapseGenDecoration D hS κ` (a function of the collapsed
  decoration: the class-common core multiplier),
* times the SLOT part `∏_s genΘs s (slotMom … s) (restrictRelativeDecorations D hS κ s)` — exactly β's per-slot
  factor form in `MkSlotsB.kernelLeaves_skeleton_reduction_selNWFMRL` with `Θs := genΘs …`.

Route: `stemFilterCap_mul_selWeightCap_eq_prod` (helper G's `radRaw` identity as a node product of `genNW`), γ's
partition `MkSlotsT.stem_split` (the unit interior carries no stem node, `StemRet`), γ's
`MkSlotsT.omegaNode_core_collapse` at the core nodes, and the native resonance identity `slotFac_genNW` at the slots.
No hypothesis on `L`, `Rs` is needed (`genNW` is defined with `radRaw` itself). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs
open WaveTurbulence.VineB (SpliceShape Ret Disj)
open WaveTurbulence.RedSplice (CLBlock)

namespace WaveTurbulence.Flower.MkSlotsI

variable {w d : ℕ}

section Factor

variable {S Gsb : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) {ι : Type} [Fintype ι] [DecidableEq ι] {blk : ι → CLBlock S}
  (Φ : SpliceShape blk Gsb) (hd : Disj blk) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ)
  (Rs : Fin w → ℝ)

/-- At a core node the general stem node weight reads the skeleton resonance factor of the collapsed decoration. -/
theorem genNW_core_collapse {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration (D.garden hS) d n nfl)
    (base : Mom d) (β : GBranch S.tree) :
    genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs (D.coreBranch hS β).toNode
        (MkSlotsS.omegaAt (G := D.garden hS) (cosetDecoration (D.garden hS) L base κ.1)
          (D.coreBranch hS β).toNode) =
      genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs (D.coreBranch hS β).toNode
        (omegaNode S (cosetDecoration S L base (collapseGenDecoration D hS κ).1) β) := by
  exact congrArg (genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs (D.coreBranch hS β).toNode)
    ((omegaAt_toNode (G := D.garden hS) _ (D.coreBranch hS β)).trans
      (MkSlotsT.omegaNode_core_collapse D hS κ L base β))

/-- **WP4: the stem/selection weight of a reconstruction, factorized** into the selection constant, the core part
(non-hinge `G_sb` atoms and unit uppers, read on the collapsed decoration) and β's per-slot factors `genΘs` at the
slot momenta and the relative decorations. -/
theorem genWeight_factor
    (hR : MkSlotsT.StemRet S D.tree blk (layeredReconstruction D hS layer hLayer) J)
    {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration (D.garden hS) d n nfl) (base : Mom d) :
    ((stemFilterCap (layeredReconstruction D hS layer hLayer) J L σ (cosetDecoration (D.garden hS) L base κ.1) *
        selWeightCap (layeredReconstruction D hS layer hLayer) J
          (selCap (layeredReconstruction D hS layer hLayer) J kSel) Rs
          (cosetDecoration (D.garden hS) L base κ.1) : ℝ) : ℂ) =
      (∏ j, (selCap (layeredReconstruction D hS layer hLayer) J kSel j).elim 1
          (fun _ => (((Rs j)⁻¹ : ℝ) : ℂ))) *
        ((∏ c ∈ Finset.univ.filter (fun c => c ∉ Φ.hinges hd),
            genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs (D.coreBranch hS (Φ.br c)).toNode
              (omegaNode S (cosetDecoration S L base (collapseGenDecoration D hS κ).1) (Φ.br c))) *
          ∏ j : ι, genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs
            (D.coreBranch hS (blk j).upper).toNode
            (omegaNode S (cosetDecoration S L base (collapseGenDecoration D hS κ).1) (blk j).upper)) *
        ∏ s, genΘs D hS layer hLayer J L σ kSel Rs s
          (MkSlotsB.slotMom hS L base (collapseGenDecoration D hS κ).1 s) (restrictRelativeDecorations D hS κ s) := by
  refine (stemFilterCap_mul_selWeightCap_eq_prod (layeredReconstruction D hS layer hLayer) J L σ kSel Rs
    (cosetDecoration (D.garden hS) L base κ.1)).trans ?_
  rw [mul_assoc]
  congr 1
  have hG : ∀ z : GNode (D.forest hS), ¬ MkSlotsT.OnStemAddr (layeredReconstruction D hS layer hLayer) J z.1 →
      genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs z
        (MkSlotsS.omegaAt (G := D.garden hS) (cosetDecoration (D.garden hS) L base κ.1) z) = 1 :=
    fun z hz => genNW_of_not_onStem (layeredReconstruction D hS layer hLayer) J L σ kSel Rs z hz _
  refine (MkSlotsT.stem_split D hS Φ hd hR _ hG).trans ?_
  congr 1
  · congr 1
    · exact Finset.prod_congr rfl fun c _ => genNW_core_collapse D hS layer hLayer J L σ kSel Rs κ base (Φ.br c)
    · exact Finset.prod_congr rfl fun j _ =>
        genNW_core_collapse D hS layer hLayer J L σ kSel Rs κ base (blk j).upper
  · exact Finset.prod_congr rfl fun s _ => slotFac_genNW D hS layer hLayer J L σ kSel Rs κ base s

/-- **The core multiplier** of the stem/selection weight, as a function of a skeleton decoration `κ'` (β's `Θ`): the
selection constant times `genNW` at the cores of the non-hinge `G_sb` atoms and of the unit uppers, at the skeleton
resonance factors of the coset decoration of `κ'`. -/
def genCoreW (base : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ' : GenDecoration S d n nfl) : ℂ :=
  (∏ j, (selCap (layeredReconstruction D hS layer hLayer) J kSel j).elim 1 (fun _ => (((Rs j)⁻¹ : ℝ) : ℂ))) *
    ((∏ c ∈ Finset.univ.filter (fun c => c ∉ Φ.hinges hd),
        genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs (D.coreBranch hS (Φ.br c)).toNode
          (omegaNode S (cosetDecoration S L base κ'.1) (Φ.br c))) *
      ∏ j : ι, genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs (D.coreBranch hS (blk j).upper).toNode
        (omegaNode S (cosetDecoration S L base κ'.1) (blk j).upper))

/-- **`genWeight_factor` in β's weight form** `Θ (collapse κ) · ∏_s Θs s (slotMom … s) (κ|_s)` of
`MkSlotsB.kernelLeaves_skeleton_reduction_selNWFMRL`, with `Θ := genCoreW …` and `Θs := genΘs …`. -/
theorem genWeight_factor_core
    (hR : MkSlotsT.StemRet S D.tree blk (layeredReconstruction D hS layer hLayer) J)
    {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration (D.garden hS) d n nfl) (base : Mom d) :
    ((stemFilterCap (layeredReconstruction D hS layer hLayer) J L σ (cosetDecoration (D.garden hS) L base κ.1) *
        selWeightCap (layeredReconstruction D hS layer hLayer) J
          (selCap (layeredReconstruction D hS layer hLayer) J kSel) Rs
          (cosetDecoration (D.garden hS) L base κ.1) : ℝ) : ℂ) =
      genCoreW D hS layer hLayer Φ hd J L σ kSel Rs base (collapseGenDecoration D hS κ) *
        ∏ s, genΘs D hS layer hLayer J L σ kSel Rs s
          (MkSlotsB.slotMom hS L base (collapseGenDecoration D hS κ).1 s) (restrictRelativeDecorations D hS κ s) :=
  genWeight_factor D hS layer hLayer Φ hd J L σ kSel Rs hR κ base

end Factor

end WaveTurbulence.Flower.MkSlotsI
