/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Twin4

/-! # ZP-SURJ: conjugation along an involution is an involution -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.LGSpine WaveTurbulence.ConjCoh WaveTurbulence.Stage1

variable {w : ℕ}

theorem garden_ext' {G H : Garden w} (ht : G.tree = H.tree) (hs : G.sig = H.sig)
    (hp : ∀ ℓ : GLeaf G.tree, (G.pair ℓ).1 = (H.pair ⟨ℓ.1, ht ▸ ℓ.2⟩).1)
    (hm : ∀ ℓ : GLeaf G.tree, G.mark ℓ = H.mark ⟨ℓ.1, ht ▸ ℓ.2⟩) : G = H := by
  cases G with
  | mk sig tree pair mark pp pe ps =>
    cases H with
    | mk sig' tree' pair' mark' pp' pe' ps' =>
      simp only at ht hs
      subst ht hs
      simp only [Garden.mk.injEq, true_and]
      refine ⟨heq_of_eq (funext fun ℓ => Subtype.ext (hp ℓ)), heq_of_eq (funext fun ℓ => hm ℓ)⟩

theorem conjGarden_invol (e : Fin w ≃ Fin w) (he : ∀ x, e (e x) = x) (G : Garden w) :
    conjGarden (conjGarden G e) e = G := by
  have hs : e.symm = e := Equiv.ext fun x => e.symm_apply_eq.2 (he x).symm
  refine garden_ext' ?_ ?_ ?_ ?_
  · funext j; simp only [conjGarden, hs, he]
  · funext j; simp only [conjGarden, hs, he, neg_neg]
  · intro ℓ
    simp only [conjGarden, leafFwd, leafBack, hs, he]
  · intro ℓ
    simp only [conjGarden, leafBack, hs, he]

theorem conjLayered_invol (e : Fin w ≃ Fin w) (he : ∀ x, e (e x) = x) (L : LayeredGarden w) :
    conjLayered (conjLayered L e) e = L := by
  refine layered_ext (conjGarden_invol e he L.garden) (fun x => ?_)
  have h1 := layerAt_conj (conjLayered_isConjugateBy (conjLayered L e) e) (phi e x)
  have h2 := layerAt_conj (conjLayered_isConjugateBy L e) x
  have h3 : phi e (phi e x) = x := by simp [phi, he]
  rw [h3] at h1
  exact h1.trans h2

end WaveTurbulence.ZpSurj
