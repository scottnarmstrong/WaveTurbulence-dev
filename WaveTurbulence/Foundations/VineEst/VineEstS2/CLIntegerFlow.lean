/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLFlowFiber
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalDecorations

/-! # Integer flow fibers from actual local lattice conservation -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed

noncomputable def latticePointAddHom {d : ℕ} (L : ℝ) : (Fin d → ℤ) →+ Mom d where
  toFun := latticePoint L
  map_zero' := by ext j; simp only [latticePoint,Pi.zero_apply,Int.cast_zero,zero_div,PiLp.zero_apply]
  map_add' := latticePoint_add L

theorem map_flow {V D E F : Type*} [DecidableEq V] [Fintype D] [AddCommGroup E] [AddCommGroup F]
    (M : Molecule V D) (S : Finset V) (f : E →+ F) (k : Bond M S → E) (v : V) :
    f (flow M S k v) = flow M S (fun e => f (k e)) v := by
  unfold flow
  rw [map_sum]
  exact Finset.sum_congr rfl (fun e _ => map_zsmul f _ _)

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- The source local lattice equations produce the integer M9 fiber. The
scale is used only through injectivity, so the construction has no diagonal
or nonzero-gap restriction. -/
noncomputable def clIntegerFlowFiber {L : ℝ} (hL : L ≠ 0)
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (κ : GNode G.tree → (Fin d → ℤ))
    (hc : ∀ v ∈ U, κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) :
    FlowFiber G.molecule U a b (Fin d → ℤ) (κ (b.child R.positive)-κ (b.child R.negative)) := by
  let f := latticePointAddHom (d := d) L
  let K : GNode G.tree → Mom d := fun x => f (κ x)
  have hcK : ∀ v ∈ U, K v.toNode = K (v.child 0)-K (v.child 1)+K (v.child 2) := by
    intro v hv
    change f (κ v.toNode) = _
    rw [hc v hv,map_add,map_sub]
  have hpK : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → K ℓ.toNode = K (G.pair ℓ).toNode :=
    fun ℓ hℓ => congrArg f (hp ℓ hℓ)
  let Q := clPhysicalFlowFiber hU R K hcK hpK
  let k : Bond G.molecule U → (Fin d → ℤ) := fun e => Mole.restrictLabels G κ e.1
  have hf : Function.Injective f := latticePoint_injective_of_ne_zero hL
  refine ⟨k,?_,?_,?_⟩
  · apply hf
    rw [map_flow,map_neg,map_sub]
    exact Q.2.1
  · apply hf
    rw [map_flow,map_sub]
    exact Q.2.2.1
  · intro v hv ha hb
    apply hf
    rw [map_flow,map_zero]
    exact Q.2.2.2 v hv ha hb

/-- This is the actual regional decoration carrier produced in V3, with its
literal extended indices. All fiber equations above are consumed directly. -/
noncomputable def clLocalIntegerFlowFiber {L : ℝ} (hL : L ≠ 0)
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (base : Mom d) (boundary : Fin 4 → Mom d) (κ : CLLocalDecoration R L base boundary) :
    FlowFiber G.molecule U a b (Fin d → ℤ)
      (clExtendIndices R κ.1 (b.child R.positive)-clExtendIndices R κ.1 (b.child R.negative)) :=
  clIntegerFlowFiber hL hU R (clExtendIndices R κ.1) κ.2.1 κ.2.2.1

end WaveTurbulence.VineEstS2
