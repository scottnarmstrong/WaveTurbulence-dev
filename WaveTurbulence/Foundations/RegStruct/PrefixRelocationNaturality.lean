/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.GraftFrames

/-! # Literal source relocation under injective rooted address embeddings -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- An injective extension-respecting address map both preserves and reflects ancestry. -/
theorem below_map_iff {w v : ℕ} (f : (Fin w × Path) → (Fin v × Path))
    (hi : Function.Injective f) (hf : ∀ a p, f (addrExt a p) = addrExt (f a) p)
    (a z : Fin w × Path) : Below (f a) (f z) ↔ Below a z := by
  constructor
  · intro h
    obtain ⟨r,hr⟩ := h.2
    have he : f z = addrExt (f a) r := Prod.ext h.1 hr.symm
    have hz : z = addrExt a r := hi (he.trans (hf a r).symm)
    rw [hz]
    exact below_extend _ _
  · intro h
    obtain ⟨r,hr⟩ := h.2
    have hz : z = addrExt a r := Prod.ext h.1 hr.symm
    rw [hz,hf a r]
    exact below_extend _ _

/-- The source relocation commutes with every injective extension-respecting frame map. -/
theorem relocate_map (f : (Fin 2 × Path) → (Fin 2 × Path))
    (hi : Function.Injective f) (hf : ∀ a p, f (addrExt a p) = addrExt (f a) p)
    (a z : Fin 2 × Path) (c l : Fin 3) :
    RawCpl.relocate (f a) c l (f z) = f (RawCpl.relocate a c l z) := by
  by_cases hb : Below a z
  · obtain ⟨r,hr⟩ := hb.2
    have hz : z = addrExt a r := Prod.ext hb.1 hr.symm
    subst z
    have hlocal := relocate_respects_desc a a c l ⟨rfl,List.prefix_refl _⟩
    have hglobal := relocate_respects_desc (f a) (f a) c l ⟨rfl,List.prefix_refl _⟩
    rw [hf a r,hglobal r,relocate_self,hlocal r,relocate_self,
      hf (addrExt a [c,l]) r,hf a [c,l]]
  · have hnot : ¬ Below (f a) (f z) := fun h => hb ((below_map_iff f hi hf a z).mp h)
    rw [relocate_eq_of_not_below _ _ _ _ hnot,relocate_eq_of_not_below _ _ _ _ hb]

/-- Incomparable couple-root frames commute with the literal source B relocation. -/
theorem relocate_frameAddress (x y a z : Fin 2 × Path) (hxy : IncompAddr x y) (c l : Fin 3) :
    RawCpl.relocate (frameAddress x y a) c l (frameAddress x y z) =
      frameAddress x y (RawCpl.relocate a c l z) :=
  relocate_map (frameAddress x y) (frameAddress_injective x y hxy) (frameAddress_respects x y) a z c l

/-- Global frame transport preserves the canonical positive/negative couple node signs. -/
theorem nodeSign_frameAddress (σ : Fin 2 → ℤˣ) (x y z : Fin 2 × Path)
    (hx : nodeSign σ x = 1) (hy : nodeSign σ y = -1) :
    nodeSign σ (frameAddress x y z) = nodeSign ![1,-1] z := by
  obtain ⟨j,p⟩ := z
  fin_cases j
  · have hh := nodeSign_addrExt σ x p
    rw [hx] at hh
    simpa [frameAddress,nodeSign] using hh
  · have hh := nodeSign_addrExt σ y p
    rw [hy] at hh
    simpa [frameAddress,nodeSign] using hh

end WaveTurbulence.Reg
