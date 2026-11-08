/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.RootPin
public import WaveTurbulence.Foundations.Flower.MkSlotsO.RootTraceHyp

/-! # RT-GATE (i): the clock of a root-pinned tree

Clause (i) of `MkSlotsO.RootTraceBoundAt` pins the root of a paired tree at `s` (`rootPins (fun _ => True) s`, which is
D2c's `rootFix s`) and gives every free branch the upper clock `ts 0`. On the R189 box (`s ≤ ts 0`) every free branch
lies below the pinned root, so the clock may be lowered to `s` (D3's `protTime_rootFix_up`): the kernel is a function
of the port clock `ts 1` alone. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin

/-- On a tree, pinning every root is pinning the root. -/
theorem rt_rootPins_tree {T : Fin 1 → TTree} (s : ℝ) :
    (MkSlotsO.rootPins (fun _ => True) s : GBranch T → Option ℝ) = rootFix s := by
  funext b
  unfold MkSlotsO.rootPins rootFix
  simp

/-- **The clock of a root-pinned tree may be lowered to the pin.** -/
theorem rt_kernel_up {LG : LayeredGarden 1} (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 1 d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (s' σ T : ℝ) (hσT : σ ≤ T) (k : Mom d)
    (nroot : Fin 1 → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelProt L γ δ LG H m (fun _ => T) s' (rootFix σ) k nroot nfl =
      kernelProt L γ δ LG H m (fun _ => σ) s' (rootFix σ) k nroot nfl := by
  rw [kernelProt_eq_tsum, kernelProt_eq_tsum]
  congr 1
  refine tsum_congr fun κ => ?_
  unfold protSummand
  rw [protTime_rootFix_up L γ δ s' _ hσT]

/-- The R189 box of clause (i). -/
def rtBox (p q' s : ℝ) : Set (Fin 2 → ℝ) := timeBoxGt p q' ∩ {ts | ts 1 < s ∧ s ≤ ts 0}

theorem rtBox_sub (p q' s : ℝ) : rtBox p q' s ⊆ timeBox p q' := fun _ h => h.1.1

/-- **The kernel of clause (i) on its box**, as a function of the port clock. -/
theorem rt_tree_onBox {LG : LayeredGarden 1} (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 1 d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (p q' s : ℝ) (k : Mom d) :
    ∀ ts ∈ rtBox p q' s,
      kernelProt L γ δ LG H m (fun _ => ts 0) (ts 1) (MkSlotsO.rootPins (fun _ => True) s) k (fun _ => 0) 0 =
        kernelProt L γ δ LG H m (fun _ => s) (ts 1) (rootFix s) k (fun _ => 0) 0 := by
  intro ts hts
  rw [rt_rootPins_tree s, rt_kernel_up L γ δ H m (ts 1) s (ts 0) hts.2.2]

/-- **The restricted norm of clause (i) by the port norm**: on its box the kernel reads only the port clock. -/
theorem rt_tree_rn_le {θ : ℝ} (hθ : 0 ≤ θ) {LG : LayeredGarden 1} (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 1 d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (p q' s : ℝ) (k : Mom d) :
    rn θ (rtBox p q' s) (fun ts => kernelProt L γ δ LG H m (fun _ => ts 0) (ts 1)
        (MkSlotsO.rootPins (fun _ => True) s) k (fun _ => 0) 0) ≤
      cutNorm θ * rn θ (win q') (fun y => kernelProt L γ δ LG H m (fun _ => s) (y 0) (rootFix s) k (fun _ => 0) 0) := by
  rw [rn_congr θ (rt_tree_onBox L γ δ H m p q' s k)]
  exact rn_lift2 hθ p q' (rtBox_sub p q' s)
    (fun y => kernelProt L γ δ LG H m (fun _ => s) (y 0) (rootFix s) k (fun _ => 0) 0)

end WaveTurbulence.Flower.ProtRT
