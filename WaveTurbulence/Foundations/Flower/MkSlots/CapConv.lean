/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.PRedNode
public import WaveTurbulence.Foundations.Flower.ProtWhole.RegWeight

/-! # B3s MK-SLOTS (cap slots): the pinned native kernel is the protected kernel of a paired tree

1. `kernelNodeWF_eq_kernelProt`: the pinned weighted kernel `kernelNodeWF` (the UNPINNED domain `kDomain`
   integrated against `fixMeasure fix`) is D2a's protected kernel `kernelProt` (the frozen `kDomainFix` and the
   lone-port constraint, integrated over the free times) when every pinned value lies in its layer window and below
   the upper time of a FREE parent (`CapPins`): on the pinned slice the two domains agree (the constraint
   `τ_b < up b` of a pinned `b` follows from `τ_b < τ_parent < up parent ≤ up b`), for every upper time.
2. `kernelProt_capG_T1`: on a width-2 cap couple (D6b's `CapG`), `kernelProt` is the protected kernel of the paired
   tree `T1` (D2b's `objTree`), the cap pair's leaf factors moving into the multiplier (`capPairFactor`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
  WaveTurbulence.Flower.ProtWhole

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ}

theorem capExtendFix_eq (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) : G.extendFix fix τ = extendFixI fix τ := by
  funext b
  unfold Garden.extendFix extendFixI
  rfl

/-- The leaf profiles of a node function (`0` off the nodes). -/
def capProfiles (LG : LayeredGarden w) (A : GNode LG.garden.tree → Mom d → ℝ) : LeafProfiles w d :=
  fun z => if h : z.2 ∈ (LG.garden.tree z.1).nodes then A ⟨z, h⟩ else 0

theorem capProfiles_leaf (LG : LayeredGarden w) (A : GNode LG.garden.tree → Mom d → ℝ) (ℓ : GLeaf LG.garden.tree) :
    capProfiles LG A ℓ.1 = A ℓ.toNode := by
  unfold capProfiles
  rw [dif_pos (show ℓ.1.2 ∈ (LG.garden.tree ℓ.1.1).nodes from ℓ.toNode.2)]
  rfl

/-! ### The cap couple and its paired tree -/

namespace CapG

variable {LG : LayeredGarden 2} {j0 c : Fin 2} {X : RegChain} {ζ : ℤˣ}

/-- The cap pair of a cap couple. -/
abbrev IsCapPairLeaf (c : Fin 2) (ℓ : GLeaf LG.garden.tree) : Prop :=
  ℓ.1.1 ∈ ({c} : Finset (Fin 2)) ∨ (LG.garden.pair ℓ).1.1 ∈ ({c} : Finset (Fin 2))

/-- The leaf factors of the cap pair, read on the paired tree. -/
def capPairFactor (D : CapG LG j0 c X ζ) (H : LeafProfiles 2 d) (K : GNode D.T1.garden.tree → Mom d) : ℂ :=
  ∏ ℓ ∈ (inputLeaves LG.garden).filter (IsCapPairLeaf c), (H ℓ.1 (K (D.ρ ℓ.toNode)) : ℂ)

/-- The leaf profiles of the paired tree. -/
def capH1 (j0 : Fin 2) (H : LeafProfiles 2 d) : LeafProfiles 1 d := fun z => H (j0, z.2)

/-- **A cap couple's protected kernel is that of its paired tree.** -/
theorem kernelProt_capG_T1 (D : CapG LG j0 c X ζ) (L γ δ : ℝ) (H : LeafProfiles 2 d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) :
    kernelProt L γ δ LG H m up 0 fix k₀ (fun _ => 0) 0 =
      kernelProt L γ δ D.T1 (capH1 j0 H) (fun K => m (fun a => K (D.ρ a)) * capPairFactor D H K)
        (fun b => up (D.βc b)) 0 (fun b => fix (D.βc b)) k₀ (fun _ => 0) 0 := by
  rw [kernelProt_eq_tsum, kernelProt_eq_tsum, D.order_eq, D.zeta_eq]
  congr 1
  rw [← (D.decEquiv d).tsum_eq]
  refine tsum_congr fun κ => ?_
  have he : D.decEquiv d κ = D.decFwd κ := rfl
  rw [he]
  unfold protSummand
  rw [D.protTime_capG L γ δ up 0 fix, D.epsDec_eq κ, D.coset_ρ L k₀ κ]
  have hι : (fun a => cosetDecoration D.T1.garden L k₀ (D.decFwd κ).1 (D.ρ (D.ι a))) =
      cosetDecoration D.T1.garden L k₀ (D.decFwd κ).1 := by
    funext a; rw [D.ρ_ι]
  rw [hι]
  rw [← Finset.prod_filter_not_mul_prod_filter (inputLeaves LG.garden) (IsCapPairLeaf c)]
  have hsplit : (inputLeaves LG.garden).filter (fun ℓ => ¬ IsCapPairLeaf c ℓ) =
      (inputLeaves D.T1.garden).map ⟨D.ιL, D.ιL_injective⟩ := by
    convert D.inputLeaves_filter using 1
  rw [hsplit, Finset.prod_map]
  have hT : ∀ ℓ : GLeaf D.T1.garden.tree,
      (H (D.ιL ℓ).1 (cosetDecoration D.T1.garden L k₀ (D.decFwd κ).1 (D.ρ (D.ιL ℓ).toNode)) : ℂ) =
        (capH1 j0 H ℓ.1 (cosetDecoration D.T1.garden L k₀ (D.decFwd κ).1 ℓ.toNode) : ℂ) := fun ℓ => by
    rw [D.ιL_toNode, D.ρ_ι]
    rfl
  simp only [Function.Embedding.coeFn_mk, hT]
  unfold capPairFactor
  ring

end CapG

end WaveTurbulence.Flower.MkSlots
