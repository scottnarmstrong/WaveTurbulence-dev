/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceSurvMK3
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: o75 Lemma 3 with the added bond of the 75-W1 HV

`survivor_imageMK'` / `survivorsMk_imageMK'`: B2a's `survivor_imageMK` / `survivorsMk_imageMK` (same proof), with
one more fact in the 75-W1 case: the added bond `e*` of the HV image is not a bond of the survivor (its ends are the
two outer joints of the HVC, which are not both in one ingredient).  So a bond of the survivor is a bond of its HV
image (`Object.ContainsDart`), which the gap entry and the 75-F1 pair of a one-survivor HVC need.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- **o75 Lemma 3 (ii), with 75-W1**: the image of a survivor of a marked SG group in `G_sb`. -/
theorem survivor_imageMK' {σ : Prescription G} {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG) (h : markedGroup G Mk S)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ (markedUnitsOfMK h).surv) :
    ∃ O : Object (stSt G σ Mk).G.molecule,
      O.atoms = t.1.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) ∧
      O.upper = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1 ∧
      O.lower = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.2 ∧
      Set.InjOn ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) t.1 ∧
      (∀ c, (stSt G σ Mk).cls ((stSt G σ Mk).M.ob c) ≠ none → c ∈ O.atoms → c = O.upper ∨ c = O.lower) ∧
      (∀ z ∈ t.1, z ≠ t.2.1 → z ≠ t.2.2 → (stSt G σ Mk).cls z = none) ∧
      ((Vine.IsSomeVine (stSt G σ Mk).G.molecule O.atoms O.upper O.lower ∧
          ∃ hvc, O.shape = VineLikeObject.vc hvc) ∨
        (AllowedCollectionObject (stSt G σ Mk).G O ∧
          (∃ R, O.shape = VineLikeObject.hyper R ∧ ¬ G.molecule.InGroup t.1 ((stSt G σ Mk).M.od R.added)) ∧
          ∀ t' ∈ (markedUnitsOfMK h).surv, t'.1 = t.1)) := by
  classical
  have hM : G.molecule.IsMolecule := Mole.garden_isMolecule G
  have hvt : Vine.IsSomeVine G.molecule t.1 t.2.1 t.2.2 := ((markedUnitsOfMK h).surv_spec t ht).1
  -- the common conclusion from a decomposition in the garden molecule
  have fromVine : ∀ (UR L0 R0 : Finset (GBranch G.tree)) (a' b' : GBranch G.tree),
      SDecomp G.molecule (stSt G σ Mk).cls UR t.1 L0 R0 a' b' t.2.1 t.2.2 → ∃ O : Object (stSt G σ Mk).G.molecule,
      O.atoms = t.1.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) ∧
      O.upper = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1 ∧
      O.lower = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.2 ∧
      Set.InjOn ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) t.1 ∧
      (∀ c, (stSt G σ Mk).cls ((stSt G σ Mk).M.ob c) ≠ none → c ∈ O.atoms → c = O.upper ∨ c = O.lower) ∧
      (∀ z ∈ t.1, z ≠ t.2.1 → z ≠ t.2.2 → (stSt G σ Mk).cls z = none) ∧
      ((Vine.IsSomeVine (stSt G σ Mk).G.molecule O.atoms O.upper O.lower ∧
          ∃ hvc, O.shape = VineLikeObject.vc hvc) ∨
        (AllowedCollectionObject (stSt G σ Mk).G O ∧
          (∃ R, O.shape = VineLikeObject.hyper R ∧ ¬ G.molecule.InGroup t.1 ((stSt G σ Mk).M.od R.added)) ∧
          ∀ t' ∈ (markedUnitsOfMK h).surv, t'.1 = t.1)) := by
    intro UR L0 R0 a' b' H
    obtain ⟨O, hOa, hOu, hOl, hOv, hOs⟩ := vine_objectStMK (stSt G σ Mk) H hvt
    refine ⟨O, hOa, hOu, hOl, H.injOn_piMK _, fun c hcn hcO => ?_, H.interior_noneMK, Or.inl ⟨hOv, hOs⟩⟩
    rw [hOu, hOl]
    exact H.hinge_imageMK _ c hcn (hOa ▸ hcO)
  have h' := h
  obtain ⟨c, -, -, hci⟩ := h'
  rcases hci with ⟨a, b, n, x, y, hB, hI⟩ | ⟨a, b, e, n, x, y, hends, hn2, hBe, hI⟩
  · -- a VC
    obtain ⟨L, hs⟩ := Spine.of_chain (Vine.chainIngredient_spec hI).1
    obtain ⟨UR, L0, R0, a', b', H, -, -⟩ := surv_sdecompMK hM hs hB (fun t ht => (hs.mem_vine'MK ht).1)
      (fun t ht => Or.inl ⟨a, b, L.length, t.2.1, t.2.2, hB, hs.ingredient_of_mem ht⟩)
      (fun T hT => isIngredient_vc hM hB hs hT) hS hσ h ht
    exact fromVine UR L0 R0 a' b' H
  · -- an HVC
    have hab : a ≠ b := hBe.2.2.2.1
    have hne : G.molecule.atom e ≠ G.molecule.atom (G.molecule.mate e) := by
      intro h0
      unfold Molecule.ends at hends
      rw [h0] at hends
      rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hab (h1.symm.trans h2)
      · exact hab (h2.symm.trans h1)
    have hN := Vine.eraseBond_isMolecule G.molecule hM e hne
    obtain ⟨L, hs, hlen⟩ := Spine.of_chain_len (Vine.chainIngredient_spec hI).1
    have hlen2 : 2 ≤ L.length := hlen ▸ hn2
    have hmemb : ∀ T, IsIngredient G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L :=
      fun T hT => isIngredient_hvc hM hends hBe hs hlen2 hT
    obtain ⟨UR, L0, R0, a', b', H, hURS, hfin⟩ := surv_sdecompMK hN hs hBe
      (fun t ht => (vine_transfer G.molecule hends (hs.not_both hlen2 ht) t.2.1 t.2.2).mp (hs.mem_vine'MK ht).1)
      (fun t ht => Or.inr ⟨a, b, e, L.length, t.2.1, t.2.2, hends, hlen2, hBe, hs.ingredient_of_mem ht⟩)
      hmemb hS hσ h ht
    by_cases hab' : a ∈ UR ∧ b ∈ UR
    · -- 75-W1: the only survivor of an HVC; its image is an HV
      obtain ⟨-, hab'', hsame⟩ := hfin hab'
      have hnot : ¬ (a ∈ t.1 ∧ b ∈ t.1) := by
        obtain ⟨p, q, hm | hm⟩ := hmemb _ ((markedUnitsOfMK h).surv_spec t ht).2.1
        · exact hs.not_both hlen2 hm
        · exact hs.not_both hlen2 hm
      have hvN : Vine.IsSomeVine (Mole.eraseBond G.molecule e) t.1 t.2.1 t.2.2 :=
        (vine_transfer G.molecule hends hnot t.2.1 t.2.2).mpr hvt
      obtain ⟨O, hOA, hOa, hOu, hOl, R, hR, hod⟩ :=
        hyper_objectStMK (stSt G σ Mk) H (hends.trans hab''.symm) hvN
      have hnin : ¬ G.molecule.InGroup t.1 ((stSt G σ Mk).M.od R.added) := by
        rw [hod]
        rintro ⟨h1, h2⟩
        unfold Molecule.ends at hends
        rcases Sym2.eq_iff.mp hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact hnot ⟨e1 ▸ h1, e2 ▸ h2⟩
        · exact hnot ⟨e2 ▸ h2, e1 ▸ h1⟩
      refine ⟨O, hOa, hOu, hOl, H.injOn_piMK _, fun c hcn hcO => ?_, H.interior_noneMK,
        Or.inr ⟨hOA, ⟨R, hR, hnin⟩, hsame⟩⟩
      rw [hOu, hOl]
      exact H.hinge_imageMK _ c hcn (hOa ▸ hcO)
    · -- the decomposition lives in the garden molecule
      have htr : ∀ X x' y', X ⊆ UR → (Mole.eraseBond G.molecule e).IsBlock X x' y' → G.molecule.IsBlock X x' y' :=
        fun X x' y' hX hb => (block_transfer G.molecule hends (fun hh => hab' ⟨hX hh.1, hX hh.2⟩) x' y').mp hb
      exact fromVine UR L0 R0 a' b'
        { toSkelDecomp := H.toSkelDecomp.transferMK hM htr
          hcls := H.hcls
          hLcl := H.hLcl
          hRcl := H.hRcl
          hLc := H.hLc
          hRc := H.hRc
          hNone := H.hNone }

/-- **o75 Lemma 3 for the survivor list `𝒞_E`** (`survivorsMk`): every survivor has its residual image in `G_sb`,
a vine or (75-W1) an HV. -/
theorem survivorsMk_imageMK' {σ : Prescription G} {Mk : Set (CLVine G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ survivorsMk G σ Mk) :
    ∃ O : Object (stSt G σ Mk).G.molecule,
      O.atoms = t.1.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) ∧
      O.upper = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1 ∧
      O.lower = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.2 ∧
      Set.InjOn ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) t.1 ∧
      (∀ c, (stSt G σ Mk).cls ((stSt G σ Mk).M.ob c) ≠ none → c ∈ O.atoms → c = O.upper ∨ c = O.lower) ∧
      (∀ z ∈ t.1, z ≠ t.2.1 → z ≠ t.2.2 → (stSt G σ Mk).cls z = none) ∧
      ((Vine.IsSomeVine (stSt G σ Mk).G.molecule O.atoms O.upper O.lower ∧
          ∃ hvc, O.shape = VineLikeObject.vc hvc) ∨
        (AllowedCollectionObject (stSt G σ Mk).G O ∧
          ∃ R, O.shape = VineLikeObject.hyper R ∧ ¬ G.molecule.InGroup t.1 ((stSt G σ Mk).M.od R.added))) := by
  obtain ⟨S, hS, hσ, h, ht'⟩ := mem_survivorsMk_iffMK.mp ht
  obtain ⟨O, h1, h2, h3, h4, h5, h6, h7⟩ := survivor_imageMK' hS hσ h ht'
  exact ⟨O, h1, h2, h3, h4, h5, h6, h7.imp id fun hh => ⟨hh.1, hh.2.1⟩⟩

end WaveTurbulence.RedSplice
