/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueC8
import Mathlib.Tactic

/-!
# Chain pair layers under a root-respecting relabelling of layers
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

theorem orientedNodes_map (P : Prop) [Decidable P] (Q : RegCpl) (f : (Fin w × Path) → (Fin w × Path))
    (x y : Fin w × Path) (hx : RespectsAt f x) (hy : RespectsAt f y) :
    orientedNodes P Q (f x) (f y) = (orientedNodes P Q x y).image f := by
  unfold orientedNodes
  split_ifs
  · exact cplNodes_map Q f x y hx hy
  · exact cplNodes_map Q f y x hy hx

theorem orientedNodes_under (P : Prop) [Decidable P] (Q : RegCpl) {r x y z : Fin w × Path}
    (hx : Under r x) (hy : Under r y) (hz : z ∈ orientedNodes P Q x y) : Under r z := by
  unfold orientedNodes at hz
  split_ifs at hz
  · rcases cplNodes_region hz with h | h
    · exact under_trans hx h
    · exact under_trans hy h
  · rcases cplNodes_region hz with h | h
    · exact under_trans hy h
    · exact under_trans hx h

theorem chainPairLayers_map {LG LG' : LayeredGarden w} (f : (Fin w × Path) → (Fin w × Path)) :
    ∀ (X : RegChain) (ζ : ℤˣ) (r : Fin w × Path), RespectsAt f r →
    (∀ x, Under r x → layerAt LG' x = layerAt LG (f x)) →
    ChainPairLayers LG X ζ (f r) → ChainPairLayers LG' X ζ r
  | .nil, _, _, _, _, _ => trivial
  | .pair m Qr Qg inner rest, ζ, r, hr, hlay, h => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hf : ∀ q, f (addrExt r q) = addrExt (f r) q := hr
    have hfr : layerAt LG' r = layerAt LG (f r) := hlay r (under_refl r)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hlay _ (under_ext r _), hf, h1, hfr]
    · intro z hz
      have hu := orientedNodes_under _ Qr (under_ext r _) (under_ext r _) hz
      rw [hlay z hu, hfr]
      have hz' : f z ∈ orientedNodes (slotSign ζ m.red.1 = 1) Qr (addrExt (f r) [m.red.1])
          (addrExt (f r) ([m.c] ++ inner.lonePath ++ [m.red.2])) := by
        rw [← hf, ← hf, orientedNodes_map _ _ f _ _ (hr.child _) (hr.child _)]
        exact Finset.mem_image_of_mem f hz
      exact h2 _ hz'
    · intro z hz
      have hu := orientedNodes_under _ Qg (under_ext r _) (under_ext r _) hz
      rw [hlay z hu, hfr]
      have hz' : f z ∈ orientedNodes (slotSign ζ m.green.1 = 1) Qg (addrExt (f r) [m.green.1])
          (addrExt (f r) ([m.c] ++ inner.lonePath ++ [m.green.2])) := by
        rw [← hf, ← hf, orientedNodes_map _ _ f _ _ (hr.child _) (hr.child _)]
        exact Finset.mem_image_of_mem f hz
      exact h3 _ hz'
    · refine chainPairLayers_map f inner _ _ (hr.child _)
        (fun x hx => hlay x (under_trans (under_ext r _) hx)) ?_
      rw [hf]; exact h4
    · refine chainPairLayers_map f rest _ _ (hr.child _)
        (fun x hx => hlay x (under_trans (under_ext r _) hx)) ?_
      rw [hf]; exact h5
termination_by X => X

end WaveTurbulence.Stage1
