/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceSurvMK2
import Mathlib.Tactic

/-!
# B2a MK-RUNS: o75 Lemma 3 — the images of the survivors in `G_sb`

`survivor_imageMK`: for a survivor `t = (A, x, y)` of a marked SG group, the image `A.image π` in the splice
`G_sb = stSt G σ Mk` is an object with joints `π x`, `π y`, `π` is injective on `A`, a merged atom of the image is
one of its joints (a hinge), the other atoms of `A` are unmerged, and either
* the image is a vine of `G_sb` (of the same type, `.vc` shape), or
* [75-W1] the group is an HVC whose only survivor is `t`, and the image is an HV of `G_sb` (an allowed `.hyper`
  object: the survivor plus the added bond `e*`).
This is main's construction of the residual objects of `𝒞₁` (`vc_object`, `hyper_object` through `skip_sdecomp`),
applied once per survivor with its at most two adjacent runs (`surv_sdecompMK`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

section core
variable {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
  {S A L0 R0 : Finset (GBranch G.tree)} {a b x y : GBranch G.tree}
  {cls : GBranch G.tree → Option (GBranch G.tree)}

/-- The splice is injective on a decomposed vine. -/
theorem SDecomp.injOn_piMK (st : SpState G) (H : SDecomp N st.cls S A L0 R0 a b x y) :
    Set.InjOn (st.M.pi st.hcls) A := by
  intro u hu v hv huv
  have h := congrArg st.M.ob huv
  rw [st.M.ob_pi, st.M.ob_pi] at h
  exact H.H1 u hu v hv h

/-- A merged atom of the image of a decomposed vine is one of its two joints. -/
theorem SDecomp.hinge_imageMK (st : SpState G) (H : SDecomp N st.cls S A L0 R0 a b x y) :
    ∀ c, st.cls (st.M.ob c) ≠ none → c ∈ A.image (st.M.pi st.hcls) →
      c = st.M.pi st.hcls x ∨ c = st.M.pi st.hcls y := by
  intro c hcn hcA
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hcA
  rw [st.M.ob_pi] at hcn
  rcases H.hinge_cases hz hcn with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The atoms of a decomposed vine other than its joints are not merged. -/
theorem SDecomp.interior_noneMK (H : SDecomp N cls S A L0 R0 a b x y) :
    ∀ z ∈ A, z ≠ x → z ≠ y → cls z = none := by
  intro z hz hzx hzy
  refine H.hNone z (H.hAsub hz) (fun hzL => ?_) (fun hzR => ?_)
  · rcases H.hL with ⟨h0, -⟩ | ⟨-, -, hi⟩
    · rw [h0] at hzL; simp at hzL
    · exact hzx (mem_inter_singletonMK hi hzL hz)
  · rcases H.hR with ⟨h0, -⟩ | ⟨-, -, hi⟩
    · rw [h0] at hzR; simp at hzR
    · exact hzy (mem_inter_singletonMK hi hzR hz)

/-- **The vine residual** of a vine decomposed in the garden molecule, in any splice state. -/
theorem vine_objectStMK (st : SpState G) (H : SDecomp G.molecule st.cls S A L0 R0 a b x y)
    (hv : Vine.IsSomeVine G.molecule A x y) :
    ∃ O : Object st.G.molecule, O.atoms = A.image (st.M.pi st.hcls) ∧ O.upper = st.M.pi st.hcls x ∧
      O.lower = st.M.pi st.hcls y ∧ Vine.IsSomeVine st.G.molecule O.atoms O.upper O.lower ∧
      ∃ h, O.shape = VineLikeObject.vc h := by
  let I := H.inducedIso (st.M.toMol st.hcls)
  obtain ⟨X, hX⟩ := hv
  have hv' : Vine.IsSomeVine st.G.molecule (A.image (st.M.pi st.hcls)) (st.M.pi st.hcls x)
      (st.M.pi st.hcls y) := ⟨X, I.isVine hX⟩
  exact ⟨⟨_, _, _, .vc ⟨hv'.choose_spec.1, 1, Chain.single hv'⟩⟩, rfl, rfl, rfl, hv', _, rfl⟩

end core

/-- **The HV residual** (75-W1) of a vine of the adjoint `eraseBond M e` of a decomposed group, in any splice
state: the image of the vine with the image of the added bond `e` (main's `hyper_object`, for every splice). -/
theorem hyper_objectStMK (st : SpState G) {S A L0 R0 : Finset (GBranch G.tree)} {a b x y : GBranch G.tree}
    {e : GardenDart G} (H : SDecomp (Mole.eraseBond G.molecule e) st.cls S A L0 R0 a b x y)
    (hends : G.molecule.ends e = s(a, b)) (hvine : Vine.IsSomeVine (Mole.eraseBond G.molecule e) A x y) :
    ∃ O : Object st.G.molecule, AllowedCollectionObject st.G O ∧
      O.atoms = A.image (st.M.pi st.hcls) ∧ O.upper = st.M.pi st.hcls x ∧ O.lower = st.M.pi st.hcls y ∧
      ∃ R : HyperLikeRealization st.G.molecule O.atoms O.upper O.lower,
        O.shape = VineLikeObject.hyper R ∧ st.M.od R.added = e := by
  have hnc : ¬ ∃ a', st.cls (G.molecule.atom e) = some a' ∧
      st.cls (G.molecule.atom (G.molecule.mate e)) = some a' := by
    unfold Molecule.ends at hends
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact H.ends_not_class
    · rw [h1, h2]
      rintro ⟨r, ha, hb⟩
      exact H.ends_not_class ⟨r, hb, ha⟩
  obtain ⟨e', rfl⟩ := (st.M.od_range e).mpr hnc
  have hc := st.hcls
  let I := H.inducedIso (st.M.eraseMol hc e')
  obtain ⟨X, hX⟩ := hvine
  have hv : Vine.IsSomeVine (Mole.eraseBond st.G.molecule e')
      (A.image (st.M.pi hc)) (st.M.pi hc x) (st.M.pi hc y) := ⟨X, I.isVine hX⟩
  have hobx : st.M.ob (st.M.pi hc x) = (st.cls x).getD x := st.M.ob_pi hc x
  have hoby : st.M.ob (st.M.pi hc y) = (st.cls y).getD y := st.M.ob_pi hc y
  have hends' : st.G.molecule.ends e' = s(st.M.pi hc x, st.M.pi hc y) := by
    unfold Molecule.ends at hends ⊢
    have hm : st.M.ob (st.G.molecule.atom (st.G.molecule.mate e')) =
        (st.cls (G.molecule.atom (G.molecule.mate (st.M.od e')))).getD
          (G.molecule.atom (G.molecule.mate (st.M.od e'))) := by
      rw [st.M.ob_atom, st.M.od_mate]; rfl
    have h0 : st.M.ob (st.G.molecule.atom e') =
        (st.cls (G.molecule.atom (st.M.od e'))).getD (G.molecule.atom (st.M.od e')) :=
      st.M.ob_atom e'
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at h0; rw [h2] at hm
      have e1 : st.G.molecule.atom e' = st.M.pi hc x := st.M.ob_inj (h0.trans (H.rc_a.trans hobx.symm))
      have e2 : st.G.molecule.atom (st.G.molecule.mate e') = st.M.pi hc y :=
        st.M.ob_inj (hm.trans (H.rc_b.trans hoby.symm))
      rw [e1, e2]
    · rw [h1] at h0; rw [h2] at hm
      have e1 : st.G.molecule.atom e' = st.M.pi hc y := st.M.ob_inj (h0.trans (H.rc_b.trans hoby.symm))
      have e2 : st.G.molecule.atom (st.G.molecule.mate e') = st.M.pi hc x :=
        st.M.ob_inj (hm.trans (H.rc_a.trans hobx.symm))
      rw [e1, e2, Sym2.eq_swap]
  exact ⟨⟨_, _, _, .hyper ⟨e', hends', ⟨hv.choose_spec.1, 1, Chain.single hv⟩⟩⟩, hv, rfl, rfl, rfl, _, rfl,
    rfl⟩

/-- **o75 Lemma 3 (ii), with 75-W1**: the image of a survivor of a marked SG group in `G_sb`. -/
theorem survivor_imageMK {σ : Prescription G} {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)}
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
        (AllowedCollectionObject (stSt G σ Mk).G O ∧ (∃ R, O.shape = VineLikeObject.hyper R) ∧
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
        (AllowedCollectionObject (stSt G σ Mk).G O ∧ (∃ R, O.shape = VineLikeObject.hyper R) ∧
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
      obtain ⟨O, hOA, hOa, hOu, hOl, R, hR, -⟩ :=
        hyper_objectStMK (stSt G σ Mk) H (hends.trans hab''.symm) hvN
      refine ⟨O, hOa, hOu, hOl, H.injOn_piMK _, fun c hcn hcO => ?_, H.interior_noneMK,
        Or.inr ⟨hOA, ⟨R, hR⟩, hsame⟩⟩
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
theorem survivorsMk_imageMK {σ : Prescription G} {Mk : Set (CLVine G)}
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
        (AllowedCollectionObject (stSt G σ Mk).G O ∧ ∃ R, O.shape = VineLikeObject.hyper R)) := by
  obtain ⟨S, hS, hσ, h, ht'⟩ := mem_survivorsMk_iffMK.mp ht
  obtain ⟨O, h1, h2, h3, h4, h5, h6, h7⟩ := survivor_imageMK hS hσ h ht'
  exact ⟨O, h1, h2, h3, h4, h5, h6, h7.imp id fun hh => ⟨hh.1, hh.2.1⟩⟩

end WaveTurbulence.RedSplice
