/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WAlign3
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WInteg
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Core1
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD9

/-! # STAGE1W-VINE (T3): the weighted value of a reconstruction in mode form

* `skelVal_slotFW`: the skeleton expression of the frontier-weighted slot family is O4′'s weighted skeleton reduction
  (`kernelLeaves_skeleton_reduction_selNW`, `prod_slotFnNW`).
* `valueSelW_modesW`: main's `valueSel_modes` (RepVB10) for the weighted value `valueSelW … (fwWeight p g base ·)`:
  the outer mode sum with VINE-B♯'s unit factors `unitKernelMG (slotFW …)`, plus summability of the mode series.
* `valueSelW_selAt_reconstruction` (RepVD7 with a weight), `member_ker_eqW` (RepVD6 with a weight): for a class
  member, VINE-B♯'s unit factor of the weighted slot family is the pinned `unitRecenteredFW p (g j₁) none y (y.2 j) …` with
  the common weight `g j₁` of the representative's unit (`source_upper_tree_index`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineC
  WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.Stage1 WaveTurbulence.RepAnalytic WaveTurbulence.VineA

open scoped Classical in
theorem skelVal_slotFW {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (selSk : GenDecoration S d roots 0 → Prop)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (p : ℕ) (g : Fin w → Mom d → ℂ) :
    skelVal D hS L γ δ base roots tt layer selSk (slotFW D hS layer hLayer L γ δ h p g) =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d roots 0, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
          (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L base κ.1) τ *
              Stage1WNoVine.reducedStarProductLeavesNW D hS L γ δ
                (typeProfiles (layeredReconstruction D hS layer hLayer) h)
                (Stage1WNoVine.fwNode (layeredReconstruction D hS layer hLayer) p g) layer hLayer tt base κ.1 τ) τ
          else 0 := by
  unfold skelVal
  congr 2
  funext κ
  have key : ∀ τ : GBranch S.tree → ℝ, (∏ s, slotFW D hS layer hLayer L γ δ h p g s (slotTs hS tt τ s)
      (base + latticePoint L (κ.1 (slotNode hS s)))) =
      Stage1WNoVine.reducedStarProductLeavesNW D hS L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h)
        (Stage1WNoVine.fwNode (layeredReconstruction D hS layer hLayer) p g) layer hLayer tt base κ.1 τ :=
    fun τ => Stage1WNoVine.prod_slotFnNW D hS L γ δ _ _ layer hLayer tt base κ.1 τ
  simp only [key]

open scoped Classical in
/-- **The weighted value of a reconstruction in mode form** (main's `valueSel_modes` with the frontier weight). -/
theorem valueSelW_modesW {P : WTParams} {R : ℕ} (U : TypeFamily P (2 * R)) {S : Garden (2 * R)} {J : Type}
    [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden (2 * R)} (Φ : SpliceShape blk Gsb)
    (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (hctrl : U.toLF.Controlled (layeredReconstruction D hS layer hLayer)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration S P.d roots 0 → Prop) (Zw : GenDecoration Gsb P.d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S P.d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (p : ℕ) (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ)
    (RB : ∀ i, RegBound blk hS (slotFW D hS layer hLayer P.L P.γ P.δ (U.h i) p g) P.L base)
    (fam : U.ι → SlotFam Gsb P.d) (Box : U.ι → ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ i s', ∀ ts ∈ Box i s', ∀ x, HasSum
      (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
      (slotFW D hS layer hLayer P.L P.γ P.δ (U.h i) p g (Φ.iota hS hSb s') ts x))
    (hbox : ∀ i, ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box i s') :
    valueSelW U.toLF tt base roots (layeredReconstruction D hS layer hLayer)
        (fun κ => selSk (collapseGenDecoration D hS κ)) (fwWeight p g base (layeredReconstruction D hS layer hLayer)) =
      @Finset.sum U.ι ℂ _ (@Finset.univ _ U.fin) (fun i =>
        ((U.sign i : ℝ) : ℂ) * ∑' ξ : (∀ s, (fam i).Λ s), ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM Gsb P.L P.γ P.δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
            (Φ.hinges hd) Zw hSb (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
            (unitKernelMG blk D hS (slotFW D hS layer hLayer P.L P.γ P.δ (U.h i) p g) P.L P.γ P.δ layer base)) ∧
    ∀ i, Summable (fun ξ : (∀ s, (fam i).Λ s) => ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM Gsb P.L P.γ P.δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
            (Φ.hinges hd) Zw hSb (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
            (unitKernelMG blk D hS (slotFW D hS layer hLayer P.L P.γ P.δ (U.h i) p g) P.L P.γ P.δ layer base)) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  refine ⟨?_, fun i => (hasSum_skelVal_outerValMG Φ (RB i) hd hSb hL0 P.γ P.δ D layer tt selSk Zw hZ (fam i)
    (Box i) (hexp i) (hbox i)).summable⟩
  rw [Stage1WNoVine.valueSelW_skeleton_reduction U.toLF D hS layer hLayer hctrl hd1 hL1 tt base roots selSk p g cψ
    hc hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have := (hasSum_skelVal_outerValMG Φ (RB i) hd hSb hL0 P.γ P.δ D layer tt selSk Zw hZ (fam i) (Box i) (hexp i)
    (hbox i)).tsum_eq
  rw [this, skelVal_slotFW]
  rfl

open scoped Classical in
theorem valueSelW_selAt_reconstruction {P : WTParams} {w : ℕ} {S : Garden w} (F : LeafFamily P w)
    (D : ReconstructionData S) (hprime : IsPrimeGarden S) (layer : GNode (D.forest hprime.1) → ℕ)
    (hLayer : IsLayering (D.garden hprime.1) layer) (LG : LayeredGarden w)
    (hspec : layeredReconstruction D hprime.1 layer hLayer = LG) (hd : D.Decodes hprime.1 LG.garden)
    (σ : NormalizedSplice.GroupPrescription S) (tt : Fin w → ℝ) (base : Mom P.d) (roots : Fin w → (Fin P.d → ℤ))
    (wt : ∀ LG : LayeredGarden w, GenDecoration LG.garden P.d roots 0 → ℂ) :
    valueSelW F tt base roots LG (fun κ => selAt P base ⟨S, hprime, D, hd⟩ σ κ) (wt LG) =
      valueSelW F tt base roots (layeredReconstruction D hprime.1 layer hLayer)
        (fun κ => NormalizedSplice.selOf σ P.L P.γ P.η base (collapseGenDecoration D hprime.1 κ).1)
        (wt (layeredReconstruction D hprime.1 layer hLayer)) := by
  subst hspec
  rfl

variable {p : ℕ} {kind : Bool}

/-- For a class member, VINE-B♯'s unit factor of the weighted slot family is the pinned `unitRecenteredFW` with the
common unit weight `g j₁`. -/
theorem member_ker_eqW {R d : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) (L γ δ : ℝ)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (base : Mom d) (g : Fin (2 * R) → Mom d → ℂ)
    (hcan : IsCanonGC (p + 1) y.1.layered) (hlay : ∀ x, stateLayer y.1 x ≤ p) :
    unitKernelMG (fun j => unitClBlock (y.2 j)) y.1.data y.1.plain
        (slotFW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ h p g) L γ δ (stateLayer y.1)
        base =
      fun (j : Fin (unitBlocks a.prime.skeleton a.totalSigma).length) (lam : ℤ) (t : Fin 3 → ℝ) (k : Fin 4 → Mom d) =>
        unitRecenteredFW p (g (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma j).upper.1.1) none
          y.1 (y.2 j) L γ δ (unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) h j) base
          (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3) := by
  funext j lam t k
  rw [unitKernelMG_slotFW_eq y.1 y.2 (stateLayer y.1) (stateLayer_isLayering y.1) (stateLayer_spec y.1) L γ δ h p g
    base hcan hlay j lam t k]
  have hidx := source_upper_tree_index a y hy j
  have h1 : unitProfile (fun j => unitClBlock (y.2 j)) h j =
      unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) h j := by
    funext q
    unfold unitProfile
    exact congrArg₂ (fun u v => h q u v) hidx hidx
  have h2 : g (y.2 j).blk.a.1.1 = g (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma j).upper.1.1 :=
    congrArg g hidx
  rw [h1, h2]

end WaveTurbulence.Flower.Stage1WVine
