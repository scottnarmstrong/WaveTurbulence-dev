/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WAlign2
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD1

/-! # STAGE1W-VINE (weighted VINE-ALIGN, part 3): the outer frontier-weighted slot kernels are class-common

* `sourceShape_wLay`: the weight layer `wLay` of every argument of an outer slot is common to the class (the route is
  common, root clocks map to root clocks, core layers are common: main's `sourceShape_clkLayer` argument).
* `sourceShape_slotFW`: **the weighted R-SLOT** — for a member `y` of the unit class of the representative `a`, the
  frontier-weighted kernel of the outer slot `ι_y s'` is the representative's kernel of `ι_a s'`, as functions of times
  and momentum.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open TTree WaveTurbulence WaveTurbulence.RegRed Finset WaveTurbulence.Represents Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W
  WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.VineA WaveTurbulence.VineB WaveTurbulence.VineC
  WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist

variable {p d : ℕ} {kind : Bool}

/-- The weight layers of the arguments of the outer slots are common to the class. -/
theorem sourceShape_wLay {R : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (hG : a.fullProfile.piece.gap.garden.IsPlain) (s : ReplacementSlot a.fullProfile.piece.gap.garden) (i : Fin 2)
    (pw : ℕ) :
    wLay pw (fun b => stateLayer y.1 (y.1.data.coreBranch y.1.plain b).toNode)
        (argSrc y.1.plain ((sourceShape a y hy).iota y.1.plain hG s) i) =
      wLay pw (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        (argSrc a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hG s) i) := by
  obtain ⟨M, hr, hbr, hlow⟩ := sourceShape_trace a y hy
  have hroute := congrFun (congrFun (sourceShape_route a y hy hG) s) i
  rcases hr' : (profileShape a).route a.prime.prime.1 hG s i with y' | j
  · rw [hr'] at hroute
    rw [(sourceShape a y hy).route_inl _ hG hroute, (profileShape a).route_inl _ hG hr']
    rcases y' with r | c
    · rfl
    · show stateLayer y.1 (y.1.data.coreBranch y.1.plain ((sourceShape a y hy).br c)).toNode =
        sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 ((profileShape a).br c)).toNode
      rw [sourceShape_core_layer, profileShape_core_layer]
  · rw [hr'] at hroute
    rw [(sourceShape a y hy).route_inr _ hG hroute, (profileShape a).route_inr _ hG hr']
    show stateLayer y.1 (y.1.data.coreBranch y.1.plain (y.2 j).blk.b).toNode =
      sourceLayer a (a.prime.data.coreBranch a.prime.prime.1
        (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma j).lower).toNode
    rw [hlow j]
    exact member_core_layer a y M hr _

/-- **The weighted R-SLOT**: the outer frontier-weighted slot kernels of a class member are the representative's. -/
theorem sourceShape_slotFW {R : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (hG : a.fullProfile.piece.gap.garden.IsPlain)
    (f : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin (2 * R) → Mom d → ℂ)
    (s : ReplacementSlot a.fullProfile.piece.gap.garden) :
    slotFW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ f pw g
        ((sourceShape a y hy).iota y.1.plain hG s) =
      slotFW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) L γ δ f pw g
        ((profileShape a).iota a.prime.prime.1 hG s) := by
  funext ts k
  rw [slotFW_eq_kerQ, slotFW_eq_kerQ]
  have hw : (fun i => wLay pw (fun b => stateLayer y.1 (y.1.data.coreBranch y.1.plain b).toNode)
        (argSrc y.1.plain ((sourceShape a y hy).iota y.1.plain hG s) i)) =
      fun i => wLay pw (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        (argSrc a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hG s) i) :=
    funext fun i => sourceShape_wLay a y hy hG s i pw
  rw [hw, stateLayer_spec y.1, sourceLayer_reconstructs a]
  exact congrFun (congrFun (congrFun (sourceShape_kerQ a y hy hG f L γ δ pw g s) _) ts) k

end WaveTurbulence.Flower.Stage1WVine
