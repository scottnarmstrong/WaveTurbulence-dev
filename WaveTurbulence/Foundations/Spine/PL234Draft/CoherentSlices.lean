/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueLayer

/-!
# The same-layer blocks of a chain (TARGET L1236)

TARGET L1236: "for each `q' ≤ r ≤ q`, consider all the nodes `𝔫_a^+` … such that `𝔏_{𝔫_a^+} = r`. All
these branching nodes are linked to each other, and they are precisely all the branching nodes of some
regular tree `𝒯_{[r]}`". At the code level:

* `takeLayer LG a r X`: the top block of top-level pairs of `X` (rooted at `a`) in layer `r`;
  `dropLayer LG a r X`: the rest; `appendChain_take_drop`: `X` is their concatenation;
* `chainSlice_take_drop`: for `r' ≠ r`, the spine's slice `SourceApp.chainSlice … r' X` is the slice of
  the rest;
* `SpineMono`: the top layers along the spine do not increase (`spineMono_of_chainEmb`, from the layering);
  under it, the slice in the top layer is the top block (`chainSlice_eq_take`), and the slice in a
  layer above all the spine layers is empty (`chainSlice_eq_nil`).
-/

@[expose] public section
open WaveTurbulence.Induct

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine

variable {w : ℕ}

/-- The address of the continuation of a chain pair. -/
def nextAddr (a : Fin w × Path) (m : MiniTreeCode) (inner : RegChain) : Fin w × Path :=
  addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])

/-- The top block of top-level pairs in layer `r`. -/
def takeLayer (LG : LayeredGarden w) (a : Fin w × Path) (r : ℕ) : RegChain → RegChain
  | .nil => .nil
  | .pair m Qr Qg inner rest =>
    if layerAt LG a = r then .pair m Qr Qg inner (takeLayer LG (nextAddr a m inner) r rest) else .nil

/-- The chain below the top block in layer `r`. -/
def dropLayer (LG : LayeredGarden w) (a : Fin w × Path) (r : ℕ) : RegChain → RegChain
  | .nil => .nil
  | .pair m Qr Qg inner rest =>
    if layerAt LG a = r then dropLayer LG (nextAddr a m inner) r rest else .pair m Qr Qg inner rest

theorem appendChain_take_drop (LG : LayeredGarden w) (a : Fin w × Path) (r : ℕ) :
    ∀ X : RegChain, appendChain (takeLayer LG a r X) (dropLayer LG a r X) = X
  | .nil => rfl
  | .pair m Qr Qg inner rest => by
    unfold takeLayer dropLayer
    split_ifs
    · simp only [appendChain, appendChain_take_drop LG _ r rest]
    · rfl

theorem chainSlice_pair (LG : LayeredGarden w) (a : Fin w × Path) (r : ℕ) (m : MiniTreeCode)
    (Qr Qg : RegCpl) (inner rest : RegChain) :
    SourceApp.chainSlice LG a r (.pair m Qr Qg inner rest) =
      if layerAt LG a = r then .pair m Qr Qg inner (SourceApp.chainSlice LG (nextAddr a m inner) r rest)
      else SourceApp.chainSlice LG (nextAddr a m inner) r rest := rfl

/-- **Slices in other layers are slices of the rest.** -/
theorem chainSlice_take_drop (LG : LayeredGarden w) {r r' : ℕ} (hr : r' ≠ r) :
    ∀ (a : Fin w × Path) (X : RegChain), SourceApp.chainSlice LG a r' X =
      SourceApp.chainSlice LG (addrExt a (takeLayer LG a r X).lonePath) r' (dropLayer LG a r X)
  | a, .nil => by simp [takeLayer, dropLayer, RegChain.lonePath, addrExt]
  | a, .pair m Qr Qg inner rest => by
    rw [chainSlice_pair]
    unfold takeLayer dropLayer
    by_cases ha : layerAt LG a = r
    · rw [ite_eq_right (fun h' => hr (h'.symm.trans ha)), ite_eq_left ha, ite_eq_left ha,
        chainSlice_take_drop LG hr]
      simp only [RegChain.lonePath, nextAddr, addrExt_append, List.append_assoc]
    · rw [ite_eq_right ha, ite_eq_right ha]
      simp only [RegChain.lonePath, addrExt, List.append_nil]
      rw [chainSlice_pair]

/-- The top layers along the spine of a chain do not increase. -/
def SpineMono (LG : LayeredGarden w) : (Fin w × Path) → RegChain → Prop
  | _, .nil => True
  | a, .pair m _ _ inner rest =>
    (∀ m' Qr' Qg' inner' rest', rest = .pair m' Qr' Qg' inner' rest' →
      layerAt LG (nextAddr a m inner) ≤ layerAt LG a) ∧ SpineMono LG (nextAddr a m inner) rest

/-- The top layer of a chain (`0` for the empty chain). -/
def topLayer' (LG : LayeredGarden w) (a : Fin w × Path) : RegChain → ℕ
  | .nil => 0
  | .pair .. => layerAt LG a

theorem chainSlice_eq_nil (LG : LayeredGarden w) {r : ℕ} :
    ∀ (a : Fin w × Path) (X : RegChain), SpineMono LG a X → (X ≠ .nil → layerAt LG a < r) →
      SourceApp.chainSlice LG a r X = .nil
  | _, .nil, _, _ => rfl
  | a, .pair m Qr Qg inner rest, hm, hlt => by
    have ha := hlt (by simp)
    rw [chainSlice_pair, ite_eq_right (Nat.ne_of_lt ha)]
    refine chainSlice_eq_nil LG _ rest hm.2 fun hne => ?_
    cases rest with
    | nil => exact absurd rfl hne
    | pair m' Qr' Qg' inner' rest' => exact lt_of_le_of_lt (hm.1 _ _ _ _ _ rfl) ha

/-- **The slice in the top layer is the top block.** -/
theorem chainSlice_eq_take (LG : LayeredGarden w) {r : ℕ} :
    ∀ (a : Fin w × Path) (X : RegChain), SpineMono LG a X → (X ≠ .nil → layerAt LG a ≤ r) →
      SourceApp.chainSlice LG a r X = takeLayer LG a r X
  | _, .nil, _, _ => rfl
  | a, .pair m Qr Qg inner rest, hm, hle => by
    have ha := hle (by simp)
    rw [chainSlice_pair]
    unfold takeLayer
    by_cases he : layerAt LG a = r
    · rw [ite_eq_left he, ite_eq_left he, chainSlice_eq_take LG _ rest hm.2 fun hne => ?_]
      cases rest with
      | nil => exact absurd rfl hne
      | pair m' Qr' Qg' inner' rest' => exact (hm.1 _ _ _ _ _ rfl).trans he.le
    · rw [ite_eq_right he, ite_eq_right he]
      refine chainSlice_eq_nil LG _ rest hm.2 fun hne => ?_
      cases rest with
      | nil => exact absurd rfl hne
      | pair m' Qr' Qg' inner' rest' =>
        exact lt_of_le_of_lt (hm.1 _ _ _ _ _ rfl) (lt_of_le_of_ne ha he)

/-- **The spine layers of an embedded chain do not increase.** -/
theorem spineMono_of_chainEmb {LG : LayeredGarden w} :
    ∀ {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}, ChainEmb LG.garden X ζ a h →
      SpineMono LG a X
  | .nil, _, _, _, _ => trivial
  | .pair m Qr Qg inner rest, ζ, a, h, hC => by
    obtain ⟨-, -, -, hR⟩ := hC.parts
    refine ⟨fun m' Qr' Qg' inner' rest' hrest => ?_, spineMono_of_chainEmb hR⟩
    have hn : (nextAddr a m inner).2 ∈ (LG.garden.tree (nextAddr a m inner).1).nodes := hR.node
    exact layerAt_le_of_under LG hC.node hn ⟨rfl, ⟨_, rfl⟩⟩

end WaveTurbulence.PL234
