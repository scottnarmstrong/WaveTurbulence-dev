/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueT4
import Mathlib.Tactic

/-!
# Chain pair layers under a relabelling known only on the chain nodes and the lone position
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

theorem mem_chainNodesSet_pair_iff {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain}
    {ζ : ℤˣ} {a z : Fin w × Path} :
    z ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a ↔
      z = a ∨ z = addrExt a ([m.c] ++ inner.lonePath) ∨
      z ∈ orientedNodes (slotSign ζ m.red.1 = 1) Qr (addrExt a [m.red.1])
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) ∨
      z ∈ orientedNodes (slotSign ζ m.green.1 = 1) Qg (addrExt a [m.green.1])
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) ∨
      z ∈ chainNodesSet inner (slotSign ζ m.c) (addrExt a [m.c]) ∨
      z ∈ chainNodesSet rest (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) := by
  constructor
  · exact mem_chainNodesSet_pair
  · intro h
    have key : ∀ (P : Prop) [Decidable P] (Q : RegCpl) (x y : Fin w × Path),
        z ∈ orientedNodes P Q x y → z ∈ pairEndpoints (if P then Q.linksAt x y else Q.linksAt y x) ∨
          z ∈ pairEndpoints (if P then Q.pairsAt x y else Q.pairsAt y x) := by
      intro P _ Q x y hz
      unfold orientedNodes cplNodes at hz
      split_ifs at hz ⊢ <;> simpa using hz
    unfold chainNodesSet
    rw [Finset.mem_union, RegChain.linksAt, RegChain.pairsAt, pairEndpoints_cons, pairEndpoints_append,
      pairEndpoints_append, pairEndpoints_append, pairEndpoints_append, pairEndpoints_append,
      pairEndpoints_append]
    simp only [Finset.mem_union, Finset.mem_singleton]
    unfold chainNodesSet at h
    rcases h with h | h | h | h | h | h
    · tauto
    · tauto
    · rcases key _ _ _ _ h with h | h <;> tauto
    · rcases key _ _ _ _ h with h | h <;> tauto
    · simp only [Finset.mem_union] at h; tauto
    · simp only [Finset.mem_union] at h; tauto

theorem chainPairLayers_map' {LG LG' : LayeredGarden w} (f : (Fin w × Path) → (Fin w × Path)) :
    ∀ (X : RegChain) (ζ : ℤˣ) (r : Fin w × Path), RespectsAt f r →
    (∀ x, x ∈ chainNodesSet X ζ r ∨ x = addrExt r X.lonePath → layerAt LG' x = layerAt LG (f x)) →
    ChainPairLayers LG X ζ (f r) → ChainPairLayers LG' X ζ r
  | .nil, _, _, _, _, _ => trivial
  | .pair m Qr Qg inner rest, ζ, r, hr, hlay, h => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hf : ∀ q, f (addrExt r q) = addrExt (f r) q := hr
    have hmem := fun z => (mem_chainNodesSet_pair_iff (m := m) (Qr := Qr) (Qg := Qg) (inner := inner)
      (rest := rest) (ζ := ζ) (a := r) (z := z)).mpr
    have hrN : r ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ r := hmem _ (Or.inl rfl)
    have hcN : addrExt r ([m.c] ++ inner.lonePath) ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ r :=
      hmem _ (Or.inr (Or.inl rfl))
    have hfr : layerAt LG' r = layerAt LG (f r) := hlay r (Or.inl hrN)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hlay _ (Or.inl hcN), hf, h1, hfr]
    · intro z hz
      have hzN : z ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ r := hmem _ (Or.inr (Or.inr (Or.inl hz)))
      rw [hlay z (Or.inl hzN), hfr]
      have hz' : f z ∈ orientedNodes (slotSign ζ m.red.1 = 1) Qr (addrExt (f r) [m.red.1])
          (addrExt (f r) ([m.c] ++ inner.lonePath ++ [m.red.2])) := by
        rw [← hf, ← hf, orientedNodes_map _ _ f _ _ (hr.child _) (hr.child _)]
        exact Finset.mem_image_of_mem f hz
      exact h2 _ hz'
    · intro z hz
      have hzN : z ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ r :=
        hmem _ (Or.inr (Or.inr (Or.inr (Or.inl hz))))
      rw [hlay z (Or.inl hzN), hfr]
      have hz' : f z ∈ orientedNodes (slotSign ζ m.green.1 = 1) Qg (addrExt (f r) [m.green.1])
          (addrExt (f r) ([m.c] ++ inner.lonePath ++ [m.green.2])) := by
        rw [← hf, ← hf, orientedNodes_map _ _ f _ _ (hr.child _) (hr.child _)]
        exact Finset.mem_image_of_mem f hz
      exact h3 _ hz'
    · refine chainPairLayers_map' f inner _ _ (hr.child _) (fun x hx => hlay x ?_) ?_
      · rcases hx with hx | hx
        · exact Or.inl (hmem _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))))
        · left
          rw [hx]
          have := hcN
          rwa [← addrExt_append] at this
      · rw [hf]; exact h4
    · refine chainPairLayers_map' f rest _ _ (hr.child _) (fun x hx => hlay x ?_) ?_
      · rcases hx with hx | hx
        · exact Or.inl (hmem _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hx))))))
        · right
          rw [hx]
          simp [RegChain.lonePath, addrExt, List.append_assoc]
      · rw [hf]; exact h5
termination_by X => X

end WaveTurbulence.Stage1
