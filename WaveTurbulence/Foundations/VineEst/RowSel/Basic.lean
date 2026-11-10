/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.Vocab
public import WaveTurbulence.Foundations.VineEst.RowSel.RowData
public import WaveTurbulence.Frozen.Defs.KQstar
public import WaveTurbulence.Frozen.Defs.KTstar

/-! # V5W-B (ruling F2): the row selector of the V5 tower

Ruling R151 (F2) generalizes main's V5 vine-estimate tower in place: every module of the reverse closure of
`RegRedDraft.CLLocalFactors` inside `KindFinal.Export`'s closure carries
`variable {rowSelU : Unit} [rowSel : VineEst.RowSel rowSelU]`, and the row-carrying bodies read their rows through the
selector below instead of a literal `KQstar`/`KTstar`.

The class carries a trivial index `u : outParam Unit` (the only dependency).  It makes the section instance depend on
the section variable `rowSelU`, so that Lean includes it in a theorem or definition exactly when the statement or body
reads a selected row; a parameter-free class would be included in *every* theorem of the tower (Lean's rule for
instance-implicit section variables), and through their proof terms in definitions such as `sourceSumintDatum`,
making the statement-shape definitions (`CoupleEligible`, `RowCoherent`, `step3W`, …) depend on the instance.

* `RowSel`: a dependency-free class carrying a switch `weighted`, the top layer `p`, the presentation constant `cψ` and
  the weight `g d : Mom d → ℂ`, real and bounded by `cψ ≥ 1` (the S-STAGE1W weight class; the `GPresented (32 d)`
  presentation itself is a hypothesis of the consumers, not a field).  The per-arm family `g j` of S-STAGE1W enters
  through the instance: a consumer instantiates `RowSel` per vine region with the weight `g j` of the region's arm
  (V5W-0's kernel `twistedRecenteredFW p (g a.1.1)` reads one weight per class kernel).  A weight read from each row's
  own tree index would not be twist invariant (a generic twist placement can move nodes across tree indices,
  `LFTwist/SameTree`).
* `RowSel.plain`: the global instance with no weights (`weighted = false`).  Every selected body reduces to main's
  original body under it **by `rfl`**, so every statement outside the tower resolves `RowSel.plain` and is unchanged.
* `KQsel`, `KTsel`: selection by incoherency index.  With weights, a coherent row (index `0`) keeps the plain
  `KQstar`/`KTstar`; an incoherent row carries its own top-weighted kernel `coupleLeavesTop`/`treeLeavesTop` (V5W-0's
  pinned row kernels, at the layer profiles) normalized by `cψ^{-(4n+2)}` (couples) resp. `cψ^{-(4n+1)}` (trees), `2n`
  the order of the row (written `cψ ^ (2 * order + 2)`, resp. `+ 1`: the number of leaves), so that the engine's
  per-row accounting is unchanged (S-V5W §4) and the selected row obeys `KQstar`'s majorant (`RowSel/Bounds`).
* `selCoupleRow`, `selTreeRow`: the selected row of a source pair / branch of a reconstruction: incoherency
  `coupleIncoh`/`treeIncoh`, root parent layers
  `coupleRootParents`/`treeRootParent` at the selector's `p`, native layered object `nativeCoupleLayered`/
  `nativeChainLayered`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.VineEst
open WaveTurbulence WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree

/-- **The row selector** (ruling F2).  `weighted = false` is the plain V5 tower. -/
class RowSel (u : outParam Unit) : Type where
  /-- Whether incoherent rows carry their top weight. -/
  weighted : Bool
  /-- The top layer `p` of the frontier weight. -/
  p : ℕ
  /-- The presentation constant of the weights (the incoherent rows are normalized by its powers). -/
  cψ : ℝ
  /-- The weight on `Mom d` (one per vine region: the weight of the region's arm). -/
  g : (d : ℕ) → Mom d → ℂ
  /-- `1 ≤ cψ` (S-STAGE1W weight class). -/
  one_le_cψ : 1 ≤ cψ
  /-- The weights are bounded by `cψ` (a consequence of their `GPresented (32 d)` presentation of mass `≤ cψ`). -/
  norm_g_le : ∀ d x, ‖g d x‖ ≤ cψ
  /-- The weights are real. -/
  g_real : ∀ d x, (g d x).im = 0

/-- **The plain selector**: no weights; every row is main's `KQstar`/`KTstar`. -/
instance RowSel.plain : RowSel () where
  weighted := false
  p := 0
  cψ := 1
  g := fun _ _ => 1
  one_le_cψ := le_refl 1
  norm_g_le := fun _ _ => by simp
  g_real := fun _ _ => by simp

section Kernels
variable {u : Unit} [S : RowSel u] {d : ℕ}

/-- The selected couple row kernel of a layered couple with incoherency index `incoh` and root parent layers `q, q'`. -/
def KQsel (incoh q q' : ℕ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) (t s : ℝ) (k : Mom d) : ℂ :=
  cond S.weighted
    (if incoh = 0 then KQstar L γ δ F LG t s k
      else (((S.cψ ^ (2 * LG.garden.order + 2))⁻¹ : ℝ) : ℂ) *
        Flower.Stage1W.coupleLeavesTop L γ δ S.p (S.g d) q q' LG (LGSpine.layerProfiles LG F) t s k)
    (KQstar L γ δ F LG t s k)

/-- The selected tree row kernel of a layered tree with incoherency index `incoh` and root parent layer `q`. -/
def KTsel (incoh q : ℕ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1) (t s : ℝ) (k : Mom d) : ℂ :=
  cond S.weighted
    (if incoh = 0 then KTstar L γ δ F LG t s k
      else (((S.cψ ^ (2 * LG.garden.order + 1))⁻¹ : ℝ) : ℂ) *
        Flower.Stage1W.treeLeavesTop L γ δ S.p (S.g d) q LG (LGSpine.layerProfiles LG F) t s k)
    (KTstar L γ δ F LG t s k)

theorem KQsel_of_incoh_eq_zero {incoh : ℕ} (h : incoh = 0) (q q' : ℕ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden 2) (t s : ℝ) (k : Mom d) :
    KQsel incoh q q' L γ δ F LG t s k = KQstar L γ δ F LG t s k := by
  unfold KQsel
  cases S.weighted <;> simp [h]

theorem KTsel_of_incoh_eq_zero {incoh : ℕ} (h : incoh = 0) (q : ℕ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden 1) (t s : ℝ) (k : Mom d) :
    KTsel incoh q L γ δ F LG t s k = KTstar L γ δ F LG t s k := by
  unfold KTsel
  cases S.weighted <;> simp [h]

theorem KQsel_of_weighted_eq_false (h : S.weighted = false) (incoh q q' : ℕ) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) (t s : ℝ) (k : Mom d) :
    KQsel incoh q q' L γ δ F LG t s k = KQstar L γ δ F LG t s k := by
  unfold KQsel
  rw [h]
  rfl

theorem KTsel_of_weighted_eq_false (h : S.weighted = false) (incoh q : ℕ) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1) (t s : ℝ) (k : Mom d) :
    KTsel incoh q L γ δ F LG t s k = KTstar L γ δ F LG t s k := by
  unfold KTsel
  rw [h]
  rfl

end Kernels

section Rows
variable {u : Unit} [S : RowSel u] {w d : ℕ} {G : Garden w}

/-- **The selected couple row of a source pair** `pr` of a reconstruction (in place of
`KQstar L γ δ F (nativeCoupleLayered D hG layer hLayer pr)`). -/
def selCoupleRow (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (D : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (pr : SourcePair G) (t s : ℝ)
    (k : Mom d) : ℂ :=
  KQsel (Flower.V5W.coupleIncoh D hG layer hLayer pr)
    (Flower.V5W.coupleRootParents S.p D hG layer hLayer pr 0) (Flower.V5W.coupleRootParents S.p D hG layer hLayer pr 1)
    L γ δ F (nativeCoupleLayered D hG layer hLayer pr) t s k

/-- **The selected tree row of a branch** `v` of a reconstruction (in place of
`KTstar L γ δ F (nativeChainLayered D hG layer hLayer v)`). -/
def selTreeRow (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (D : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (v : GBranch G.tree) (t s : ℝ)
    (k : Mom d) : ℂ :=
  KTsel (Flower.V5W.treeIncoh D hG layer hLayer v) (Flower.V5W.treeRootParent S.p D hG layer hLayer v)
    L γ δ F (nativeChainLayered D hG layer hLayer v) t s k

/-- Rows with the same selection data are equal (the transport form used by the rigid and twist invariances). -/
theorem selCoupleRow_congr (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) {w' : ℕ} {G' : Garden w'}
    (D : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (pr : SourcePair G)
    (D' : ReconstructionData G') (hG' : G'.IsPlain) (layer' : GNode (D'.forest hG') → ℕ)
    (hLayer' : IsLayering (D'.garden hG') layer') (pr' : SourcePair G')
    (hLG : nativeCoupleLayered D' hG' layer' hLayer' pr' = nativeCoupleLayered D hG layer hLayer pr)
    (hinc : Flower.V5W.coupleIncoh D' hG' layer' hLayer' pr' = Flower.V5W.coupleIncoh D hG layer hLayer pr)
    (hq : ∀ i, Flower.V5W.coupleRootParents S.p D' hG' layer' hLayer' pr' i =
      Flower.V5W.coupleRootParents S.p D hG layer hLayer pr i) (t s : ℝ) (k : Mom d) :
    selCoupleRow L γ δ F D' hG' layer' hLayer' pr' t s k = selCoupleRow L γ δ F D hG layer hLayer pr t s k := by
  unfold selCoupleRow
  rw [hLG, hinc, hq 0, hq 1]

/-- Tree rows with the same selection data are equal. -/
theorem selTreeRow_congr (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) {w' : ℕ} {G' : Garden w'}
    (D : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (v : GBranch G.tree)
    (D' : ReconstructionData G') (hG' : G'.IsPlain) (layer' : GNode (D'.forest hG') → ℕ)
    (hLayer' : IsLayering (D'.garden hG') layer') (v' : GBranch G'.tree)
    (hLG : nativeChainLayered D' hG' layer' hLayer' v' = nativeChainLayered D hG layer hLayer v)
    (hinc : Flower.V5W.treeIncoh D' hG' layer' hLayer' v' = Flower.V5W.treeIncoh D hG layer hLayer v)
    (hq : Flower.V5W.treeRootParent S.p D' hG' layer' hLayer' v' = Flower.V5W.treeRootParent S.p D hG layer hLayer v)
    (t s : ℝ) (k : Mom d) :
    selTreeRow L γ δ F D' hG' layer' hLayer' v' t s k = selTreeRow L γ δ F D hG layer hLayer v t s k := by
  unfold selTreeRow
  rw [hLG, hinc, hq]

end Rows

/-- Under the plain selector the selected couple row is main's `KQstar` row, by `rfl`. -/
theorem selCoupleRow_plain {w d : ℕ} {G : Garden w} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (D : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (pr : SourcePair G)
    (t s : ℝ) (k : Mom d) :
    selCoupleRow (S := RowSel.plain) L γ δ F D hG layer hLayer pr t s k =
      KQstar L γ δ F (nativeCoupleLayered D hG layer hLayer pr) t s k := rfl

/-- Under the plain selector the selected tree row is main's `KTstar` row, by `rfl`. -/
theorem selTreeRow_plain {w d : ℕ} {G : Garden w} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (D : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (v : GBranch G.tree)
    (t s : ℝ) (k : Mom d) :
    selTreeRow (S := RowSel.plain) L γ δ F D hG layer hLayer v t s k =
      KTstar L γ δ F (nativeChainLayered D hG layer hLayer v) t s k := rfl

end WaveTurbulence.VineEst
