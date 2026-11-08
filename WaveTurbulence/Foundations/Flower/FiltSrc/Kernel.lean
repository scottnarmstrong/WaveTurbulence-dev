/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltSrc.TopIdentity
public import WaveTurbulence.Foundations.Flower.FiltSrc.Identity

/-! # D5b-1 FILT-SRC: the D5 gate kernels are filtered weighted raw operators (K1 + `TopIdentity`)

For the multiplier of `ProtDefs.FiltIncoherentDecayAt`,
`m κ = starWeight S ω κ * filtWeight F ann M κ * filtWeight Fu false Mu κ`, the leafwise kernel `kernelLeavesW` equals
the filtered weighted raw operator of `Source.lean` with
- internal measure INC-TOP's star root measure at `k` (`starRootMeasure J S ω c h (coupleRow hQ)).at k`), and
- link multipliers `φ = coupleLinkFilt hQ F Fu ann M Mu` (trees: `treeLinkFilt`), i.e. link `j` carries the two filter
  layers of its two branches at `|Ω| = |2⟨x_j, y_j⟩|`.

These are the weighted copies of INC-TOP's `StarDecay` kernel rewrites (`coupleLeavesW_eq_weightedRaw_of_summable …
(couple_starWeight_eq_value …)`), with `hW'` discharged by `Identity` and the filter bound by
`exists_linkFilt_bound`. The only premise left is INC-TOP's lattice summability `hs` (discharged in `StarDecay` by
`couple_lattice_summable` from the input norms). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace WaveTurbulence.Flower.FiltSrc
open WaveTurbulence.IncohInst WaveTurbulence.Incoh WaveTurbulence.Links
open WaveTurbulence.LGSpine WaveTurbulence.IncohLeafwise WaveTurbulence.Flower.Stage1W
open WaveTurbulence.Flower.IncTop WaveTurbulence.Flower.FiltLink

/-- **Two-root couples**: the D5 kernel is the filtered weighted raw couple operator. -/
theorem coupleLeavesW_starFilt_eq_weightedRaw {LG : LayeredGarden 2} {Q : RegCpl}
    (hQ : Q.Decodes LG.garden) (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching)
    {d : ℕ} (L γ δ : ℝ) (H : LeafProfiles 2 d) (k : Mom d) (ts : Fin 2 → ℝ)
    (J : ℕ) (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
    (c : GNode LG.garden.tree → ℝ) (h : ∀ a ∈ S, StarPresented J (ω a) (c a))
    (F Fu : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
    (M Mu : GBranch LG.garden.tree → ℝ)
    (hs : Summable (fun p : Fin Q.links.length × Fin 2 → Fin d → ℤ =>
      ‖(coupleCarrier hQ).sourceLeafWeight (coupleInputFunctionsL LG H) k
        (fun i j => latticePoint L (p (i, j)))‖)) :
    kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0
        (fun κ => starWeight S ω κ * ProtDefs.filtWeight F ann M κ *
          ProtDefs.filtWeight Fu (fun _ => false) Mu κ) =
      (MomentumTreeData.weightedSourceCoupleKernelFilt (P := (coupleCarrier hQ)))
        ((starRootMeasure J S ω c h (coupleRow hQ)).at k) (gardenCircle LG.garden)
        (coupleRootCoordinates hQ hb) L γ δ (coupleLayerLinks LG hQ) (coupleLinkFilt hQ F Fu ann M Mu)
        (coupleInternalLinkDomain LG hQ) (coupleInputFunctionsL LG H) ts k := by
  obtain ⟨B, -, hB, -⟩ := exists_linkFilt_bound
  exact coupleLeavesW_eq_weightedRaw_of_summableFilt hQ hb L γ δ H k ts _ _
    (coupleLinkFilt hQ F Fu ann M Mu) (hB hQ F Fu ann M Mu)
    (fun p => couple_starFiltWeight_eq hQ J S ω c h L k F Fu ann M Mu p) hs

/-- **One-root couples**: the D5 kernel is the filtered weighted one-clock raw operator. -/
theorem coupleLeavesW_starFilt_eq_weightedOneClock {LG : LayeredGarden 2} {Q : RegCpl}
    (hQ : Q.Decodes LG.garden) (hn : 1 ≤ Q.links.length) (a : Fin 2)
    (hb : ([] : TTree.Path) ∈ (LG.garden.tree a).branching)
    (hwidth : ∀ b : GBranch LG.garden.tree, b.1.1 = a)
    {d : ℕ} (L γ δ : ℝ) (H : LeafProfiles 2 d) (k : Mom d) (ts : Fin 2 → ℝ)
    (J : ℕ) (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
    (c : GNode LG.garden.tree → ℝ) (h : ∀ a ∈ S, StarPresented J (ω a) (c a))
    (F Fu : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
    (M Mu : GBranch LG.garden.tree → ℝ)
    (hs : Summable (fun p : Fin Q.links.length × Fin 2 → Fin d → ℤ =>
      ‖(coupleCarrier hQ).sourceLeafWeight (coupleInputFunctionsL LG H) k
        (fun i j => latticePoint L (p (i, j)))‖)) :
    kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0
        (fun κ => starWeight S ω κ * ProtDefs.filtWeight F ann M κ *
          ProtDefs.filtWeight Fu (fun _ => false) Mu κ) =
      weightedSourceOneClockKernelFilt (coupleCarrier hQ) ((starRootMeasure J S ω c h (coupleRow hQ)).at k)
        (gardenCircle LG.garden)
        (oneClockSelection Q.links.length hn ((coupleLinkEquiv hQ).symm ⟨(a, []), hb⟩) a) a
        L γ δ (coupleLayerLinks LG hQ) (coupleLinkFilt hQ F Fu ann M Mu) (coupleInternalLinkDomain LG hQ)
        (coupleInputFunctionsL LG H) ts k := by
  obtain ⟨B, -, hB, -⟩ := exists_linkFilt_bound
  exact coupleLeavesW_eq_weightedOneClock_of_summableFilt hQ hn a hb hwidth L γ δ H k ts _ _
    (coupleLinkFilt hQ F Fu ann M Mu) (hB hQ F Fu ann M Mu)
    (fun p => couple_starFiltWeight_eq hQ J S ω c h L k F Fu ann M Mu p) hs

/-- **Paired trees**: the D5 kernel is the filtered weighted raw tree operator. -/
theorem treeLeavesW_starFilt_eq_weightedRaw {LG : LayeredGarden 1} {X : RegChain}
    (hX : X.DecodesTree LG.garden) (C : TreeClockSelection hX)
    {d : ℕ} (L γ δ : ℝ) (H : LeafProfiles 1 d) (k : Mom d) (ts : Fin 2 → ℝ)
    (J : ℕ) (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
    (c : GNode LG.garden.tree → ℝ) (h : ∀ a ∈ S, StarPresented J (ω a) (c a))
    (F Fu : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
    (M Mu : GBranch LG.garden.tree → ℝ)
    (hs : Summable (fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ =>
      ‖(treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k
        (fun i j => latticePoint L (p (i, j)))‖)) :
    kernelLeavesW L γ δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
        (fun κ => starWeight S ω κ * ProtDefs.filtWeight F ann M κ *
          ProtDefs.filtWeight Fu (fun _ => false) Mu κ) =
      (MomentumTreeData.weightedSourceTreeKernelFilt (P := (treeCarrier hX)))
        ((starRootMeasure J S ω c h (treeRow hX)).at k) (gardenCircle LG.garden) C.rootCoordinates
        L γ δ (treeLayerLinks LG hX) (treeLinkFilt hX F Fu ann M Mu) (actualTreeFibers (d := d) LG hX C).timeDomain
        (treeInputFunctionsL LG H) ts k := by
  obtain ⟨B, -, -, hB⟩ := exists_linkFilt_bound
  exact treeLeavesW_eq_weightedRaw_of_summableFilt hX C L γ δ H k ts _ _
    (treeLinkFilt hX F Fu ann M Mu) (hB hX F Fu ann M Mu)
    (fun p => tree_starFiltWeight_eq hX J S ω c h L k F Fu ann M Mu p) hs

end WaveTurbulence.Flower.FiltSrc
