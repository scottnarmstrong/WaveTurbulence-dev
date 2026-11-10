/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WB.B.RowsDarts
public import WaveTurbulence.Foundations.Flower.V5WB.K.Defs
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Pullback
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.WeightedMerge

/-! # V5W-B-WORLD B5: the pinned class kernel at `S = none` is a selector class with the masked weight

`twistedRecenteredFW_none_eq`: V5W-0's pinned class kernel `twistedRecenteredFW p g none …` (each member: incoherent rows
with their top weight, coherent rows plain, the masked R135 bond product) is the V5-SPACE class
`twistedRecenteredModCX` at the weighted selector `selW p g cψ` (incoherent rows normalized by `cψ^{-(2·order+e)}`) with
each member's masked, normalized bond weight `bWN ⟨topPsi p g, cψ⟩` (the normalization moves from the rows to the
multiplier: `clLocalStarProductFW_eq`, `bWN_eq_regionWeightFW`).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.V5WB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 Links
open WaveTurbulence.VineSpaceK (ClassMember nodeWeight)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts layX memberCoreLayer memberCoreLayer_eq)
open WaveTurbulence.Flower.V5W (nodeRowIncoh regionWeightFW stateCoreLayer topFilterWeight clLocalKernelFW
  clLocalSummandFW twistedLocalKernelFW twistedRecenteredFW clLocalStarProductFW)
open WaveTurbulence.Flower.Stage1W (topPsi)

variable {w d : ℕ} {ι : Type*}

/-- The data of the masked bond weight of the frontier: `topPsi p g` with the normalization constant `cψ`. -/
def wdOf (p : ℕ) (g : Mom d → ℂ) (cψ : ℝ) : WD d := ⟨topPsi p g, cψ⟩

/-- **The masked, normalized bond weight is V5W-0's multiplier (`S = none`) times the row normalization.** -/
theorem bWN_eq_regionWeightFW (p : ℕ) (g : Mom d → ℂ) {cψ : ℝ} (hc : 0 ≤ cψ) (κ : KPar d)
    (X : FamilyReconstruction w ι) (c : ChainAt X.skeleton X.family) (x : GNode X.skeleton.tree → Fin d → ℤ) :
    bWN (wdOf p g cψ) κ X c.U x =
      regionWeightFW p g none κ.L κ.base X c.U c.a x *
        (rowNorm cψ X.data X.plain (clRegionData X.skeleton c.block c.cl) (stateLayer X)
          (stateLayer_isLayering X) : ℂ) := by
  have hN := prod_nodeNorm_regionDarts X.data X.plain (stateLayer X) (stateLayer_isLayering X) cψ hc c.block
    (clRegionData X.skeleton c.block c.cl)
  rw [← hN]
  unfold bWN bondWD regionWeightFW
  have h1 : nodeWeight (topFilterWeight (none : Option ℝ)) κ.L κ.base c.a x = 1 := by
    simp [nodeWeight, topFilterWeight]
  rw [h1, mul_one, show Finset.univ.filter (X.skeleton.molecule.InGroup c.U) = regionDarts X.skeleton c.U from rfl]
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y _ => ?_
  have hl1 : stateCoreLayer X (X.skeleton.molecule.atom (X.skeleton.molecule.mate y)) =
      layX X (X.skeleton.molecule.atom (X.skeleton.molecule.mate y)) :=
    memberCoreLayer_eq ⟨X, c⟩ _
  have hl2 : stateCoreLayer X (X.skeleton.molecule.atom y) = layX X (X.skeleton.molecule.atom y) :=
    memberCoreLayer_eq ⟨X, c⟩ _
  unfold ΨX nodeNorm
  rw [hl1, hl2]
  split_ifs <;> simp [wdOf]

variable {rowSelU : Unit} [rowSel : VineEst.RowSel rowSelU]

/-- The pinned summand is the normalization times the selected summand at `selW`. -/
theorem clLocalSummandFW_eq {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (p : ℕ) (g : Mom d → ℂ) (cψ : ℝ) (h1 : 1 ≤ cψ) (hg : ∀ x, ‖g x‖ ≤ cψ) (hr : ∀ x, (g x).im = 0)
    (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (boundary : Fin 4 → Mom d) (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary) (τ : CLInternalTime R) :
    clLocalSummandFW p g D hG R L γ δ F layer hLayer base boundary t κ τ =
      (rowNorm cψ D hG R layer hLayer : ℂ) *
        clLocalSummand (rowSel := selW p g cψ h1 hg hr) D hG R L γ δ F layer hLayer base boundary t κ τ := by
  unfold clLocalSummandFW clLocalSummand
  by_cases hτ : τ ∈ clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t
  · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hτ, clLocalStarProductFW_eq p g cψ h1 hg hr]
    ring
  · rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hτ]
    ring

end WaveTurbulence.Flower.V5WB
