/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DeletionFibers
import Mathlib.Tactic

/-! # Literal finite-image comparisons for local molecular label encodings -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem card_image_le_of_kernel_inclusion {A B C : Type*} [DecidableEq B] [DecidableEq C]
    (S : Finset A) (f : A → B) (g : A → C)
    (hker : ∀ x ∈ S, ∀ y ∈ S, g x = g y → f x = f y) :
    (S.image f).card ≤ (S.image g).card := by
  classical
  let T := S.image (fun x => (f x,g x))
  have hF : T.image Prod.fst = S.image f := by rw [image_image]; rfl
  have hG : T.image Prod.snd = S.image g := by rw [image_image]; rfl
  have hi : Set.InjOn Prod.snd (T : Set (B × C)) := by
    intro p hp q hq h
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hq
    exact Prod.ext (hker x hx y hy h) h
  calc
    _ = (T.image Prod.fst).card := congrArg Finset.card hF.symm
    _ ≤ T.card := card_image_le
    _ = (T.image Prod.snd).card := (card_image_of_injOn hi).symm
    _ = _ := congrArg Finset.card hG

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

@[expose] def localLabels (M : Molecule V D) {r : ℕ} (e : Fin r → D) {K : Type*}
    (κ : D → K) : Fin r → K := fun i => κ (e i)

/-- A graph-theoretic enumeration of the removed bonds bounds the actual
deleted-label image. Consistency at both darts is proved for each source
member and no independent mate choice is introduced. -/
theorem card_deletedLabels_image_le_localLabels_image (M : Molecule V D) (Y : Finset V)
    {r : ℕ} (e : Fin r → D)
    (hcover : ∀ x : DeletedDart M Y, ∃ i, x.val = e i ∨ x.val = M.mate (e i))
    {K : Type*} [DecidableEq K] (S : Finset (D → K))
    (hb : ∀ κ ∈ S, ∀ x, κ (M.mate x) = κ x) :
    (S.image (deletedLabels M Y)).card ≤ (S.image (localLabels M e)).card := by
  apply card_image_le_of_kernel_inclusion
  intro κ hκ κ' hκ' he
  funext x
  obtain ⟨i,hx | hx⟩ := hcover x
  · have h := congrFun he i
    change κ (e i) = κ' (e i) at h
    simpa only [deletedLabels,hx] using h
  · have h := congrFun he i
    change κ (e i) = κ' (e i) at h
    simpa only [deletedLabels,hx,hb κ hκ,hb κ' hκ'] using h

end WaveTurbulence.MoleProp
