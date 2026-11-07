/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2Second
import Mathlib.Tactic

/-! # `ylem2` for a bond `ℓ` not removed by the sequence (case-4 note, Lemma 4.1)

If neither end of `ℓ` is a chain atom, the chain and its (Y2) ending are unchanged in `𝕄 ∖ {ℓ}`, so the first
statement applies to `𝕄 ∖ {ℓ}`; its post molecule is `𝕄′ ∖ {ℓ}`. "Repeat the proof of the first statement with
`𝕄 ∖ ℓ` in place of `𝕄`" (case-4 note, L1954), word for word.

The cells through the new bond are good automatically: `𝕄′ ∖ {ℓ}` is connected and the ends of `ℓ` have degree `≤ 3`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- In a connected molecule with an atom of degree `≤ 3`, every cell is good. -/
theorem goodCell_of_connected_low {M : Molecule V D} (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    {z : V} (hz : z ∈ M.atoms) (hz3 : M.deg z ≤ 3) {S : Finset V} (hS : S ∈ MoleProp.ladderCells M) :
    GoodCell M S := by
  classical
  obtain ⟨hsub, u, v, hL, rfl⟩ := mem_filter.mp hS
  rw [mem_powerset] at hsub
  by_cases hlt : (Molecule.ladderAtoms u v).card < M.atoms.card
  · exact Or.inl (openSet_of_connected hconn hsub ⟨u 0, mem_union_left _ (mem_image_of_mem _ (mem_univ 0))⟩ hlt)
  · have heq : Molecule.ladderAtoms u v = M.atoms := eq_of_subset_of_card_le hsub (by omega)
    exact Or.inr ⟨z, heq ▸ hz, hz3⟩

namespace TwoExit
variable {M : Molecule V D} (T : TwoExit M)

/-- **`post(𝕄 ∖ {ℓ}) ≅ post(𝕄) ∖ {ℓ}`** for `ℓ` away from `Y`. -/
def postEraseBondEquiv (e : D) (heY : M.atom e ∉ T.Y ∧ M.atom (M.mate e) ∉ T.Y)
    (T' : TwoExit (MoleProp.eraseBond M e)) (hY : T'.Y = T.Y) :
    Degen.RetainedDart (MoleProp.eraseBond M e) T'.Y ⊕ Bool ≃
      MoleProp.WithoutBondDart T.post (Sum.inl ⟨e, heY.1, heY.2⟩) where
  toFun z := match z with
    | Sum.inl w => ⟨Sum.inl ⟨w.val.val, by rw [← hY]; exact w.property.1, by rw [← hY]; exact w.property.2⟩,
        fun h => w.val.property.1 (congrArg Subtype.val (Sum.inl_injective h)),
        fun h => w.val.property.2 (congrArg Subtype.val (Sum.inl_injective h))⟩
    | Sum.inr bo => ⟨Sum.inr bo, Sum.inr_ne_inl, Sum.inr_ne_inl⟩
  invFun z := match z with
    | ⟨Sum.inl w, h⟩ => Sum.inl ⟨⟨w.val, fun h' => h.1 (congrArg Sum.inl (Subtype.ext h')),
        fun h' => h.2 (congrArg Sum.inl (Subtype.ext h'))⟩,
        by rw [hY]; exact w.property.1, by rw [hY]; exact w.property.2⟩
    | ⟨Sum.inr bo, _⟩ => Sum.inr bo
  left_inv z := by
    rcases z with w | bo
    · rfl
    · rfl
  right_inv z := by
    obtain ⟨w | bo, h⟩ := z
    · rfl
    · rfl

/-- The relaxed count of `post(𝕄 ∖ {ℓ})` is that of `post(𝕄) ∖ {ℓ}`. -/
theorem afreeSup_post_eraseBond_le (e : D) (heY : M.atom e ∉ T.Y ∧ M.atom (M.mate e) ∉ T.Y)
    (T' : TwoExit (MoleProp.eraseBond M e)) (hY : T'.Y = T.Y) (hc : T'.c = T.c) (hd : T'.d = T.d) {d : ℕ}
    (L γ δ η C1 : ℝ) :
    AFreeSup T'.post d L γ δ η C1 ≤
      AFreeSup (MoleProp.eraseBond T.post (Sum.inl ⟨e, heY.1, heY.2⟩)) d L γ δ η C1 := by
  refine afreeSup_le_of_dart_equiv _ _ (T.postEraseBondEquiv e heY T' hY) ?_ ?_ ?_ ?_ L γ δ η C1
  · change T'.post.atoms = T.post.atoms
    rw [T'.post_atoms, T.post_atoms, hY]; rfl
  · rintro (w | bo)
    · rfl
    · cases bo
      · change T.c = T'.c; exact hc.symm
      · change T.d = T'.d; exact hd.symm
  · rintro (w | bo)
    · rfl
    · rfl
  · rintro (w | bo)
    · rfl
    · rfl

end TwoExit

namespace YChain
variable {M : Molecule V D} (C : YChain M) (e : D) (hu : M.atom e ∉ C.set) (hw : M.atom (M.mate e) ∉ C.set)
include hu hw

omit [DecidableEq D] in
theorem ends_ne_of_out {p q : V} (hp : p ∈ C.set) : M.ends e ≠ s(p, q) := by
  change s(M.atom e, M.atom (M.mate e)) ≠ _
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact hu (h1 ▸ hp)
  · exact hw (h2 ▸ hp)

/-- The chain on `𝕄 ∖ {ℓ}`. -/
def outChain : YChain (MoleProp.eraseBond M e) :=
  C.onErase e (fun _ hp _ _ => C.ends_ne_of_out e hu hw hp)
    (fun _ hi => ⟨fun h => hu (h ▸ C.a_mem hi.le), fun h => hu (h ▸ C.b_mem hi.le),
      fun h => hw (h ▸ C.a_mem hi.le), fun h => hw (h ▸ C.b_mem hi.le)⟩)

end YChain

namespace Y2End
variable {M : Molecule V D} {C : YChain M} (E : Y2End C)

section
variable (e : D) (hu : M.atom e ∉ C.set) (hw : M.atom (M.mate e) ∉ C.set)
include hu hw

omit [DecidableEq D] in
theorem ends_x_ne : M.ends E.x ≠ M.ends e := by
  rw [E.ends_x]; exact fun h => C.ends_ne_of_out e hu hw (C.a_mem le_rfl) h.symm

omit [DecidableEq D] in
theorem ends_y_ne : M.ends E.y ≠ M.ends e := by
  rw [E.ends_y]; exact fun h => C.ends_ne_of_out e hu hw (C.b_mem le_rfl) h.symm

/-- The (Y2) ending on `𝕄 ∖ {ℓ}`. -/
def outEnd : Y2End (C.outChain e hu hw) where
  x := ⟨E.x, ne_of_ends_ne M e (E.ends_x_ne e hu hw)⟩
  y := ⟨E.y, ne_of_ends_ne M e (E.ends_y_ne e hu hw)⟩
  hx := E.hx
  hy := E.hy
  hxo := E.hxo
  hyo := E.hyo
  far := E.far
  deg_a := by
    change (MoleProp.eraseBond M e).deg (C.a C.n) = 4
    rw [deg_eraseBond_of_ne M e (fun h => hu (h ▸ C.a_mem le_rfl)) (fun h => hw (h ▸ C.a_mem le_rfl))]
    exact E.deg_a
  deg_b := by
    change (MoleProp.eraseBond M e).deg (C.b C.n) = 4
    rw [deg_eraseBond_of_ne M e (fun h => hu (h ▸ C.b_mem le_rfl)) (fun h => hw (h ▸ C.b_mem le_rfl))]
    exact E.deg_b

theorem outEnd_toTwoExit (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2)
    (hcapN : ∀ v ∈ (MoleProp.eraseBond M e).atoms, (MoleProp.eraseBond M e).outdeg v ≤ 2 ∧
      (MoleProp.eraseBond M e).indeg v ≤ 2) :
    ((E.outEnd e hu hw).toTwoExit hcapN).Y = (E.toTwoExit hcap).Y ∧
      ((E.outEnd e hu hw).toTwoExit hcapN).c = (E.toTwoExit hcap).c ∧
      ((E.outEnd e hu hw).toTwoExit hcapN).d = (E.toTwoExit hcap).d := by
  unfold toTwoExit
  by_cases h : M.out E.x = true
  · have h' : (MoleProp.eraseBond M e).out (E.outEnd e hu hw).x = true := h
    rw [dite_eq_left_of_eq_true (eq_true h), dite_eq_left_of_eq_true (eq_true h')]
    exact ⟨rfl, rfl, rfl⟩
  · have h' : ¬ (MoleProp.eraseBond M e).out (E.outEnd e hu hw).x = true := h
    rw [dite_eq_right_of_eq_false (eq_false h), dite_eq_right_of_eq_false (eq_false h')]
    exact ⟨rfl, rfl, rfl⟩

end
end Y2End

/-- **`ylem2` with `ℓ` not removed** (case-4 note, Lemma 4.1): for `ℓ` with no end in the chain,
`𝔄(𝕄 ∖ {ℓ}) ≲ (log L)^C 𝔄(𝕄′ ∖ {ℓ})`, with LG parameter `η/2` on the right. -/
theorem ylem2_notRemoved (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ 2 * Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) (C : YChain M) (E : Y2End C) (e : D)
      (heY : M.atom e ∉ (E.toTwoExit hcap).Y ∧ M.atom (M.mate e) ∉ (E.toTwoExit hcap).Y),
      (∀ u ∈ M.atoms, ∀ w ∈ M.atoms, (MoleProp.eraseBond M e).SameComponent u w) →
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S) →
        AFree (MoleProp.eraseBond M e) d L γ δ η C1 P ≤
          ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) *
            AFreeSup (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inl ⟨e, heY.1, heY.2⟩)) d L γ δ (η / 2) C1 := by
  obtain ⟨Cstar, hCstar, h2⟩ := ylem2_Y2 d hd γ hγ η hη hηmax
  refine ⟨Cstar, hCstar, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := h2 C1 hC1 δ hδ
  refine ⟨R, fun L hL => ?_⟩
  intro V D _ _ _ M hcap C E e heY hconn P hP
  classical
  have hY := E.toTwoExit_Y hcap
  have hu : M.atom e ∉ C.set := by rw [← hY]; exact heY.1
  have hw : M.atom (M.mate e) ∉ C.set := by rw [← hY]; exact heY.2
  have hcapN := caps_eraseBond M e hcap
  set E' := E.outEnd e hu hw
  set T' := E'.toTwoExit hcapN
  obtain ⟨hTY, hTc, hTd⟩ := E.outEnd_toTwoExit e hu hw hcap hcapN
  -- the cells of `𝕄′ ∖ {ℓ}` are good
  have hgood : ∀ S ∈ MoleProp.ladderCells T'.post, T'.c ∈ S → GoodCell T'.post S := by
    intro S hS _
    have hY' : T'.Y = C.set := by rw [hTY, hY]
    have hz : M.atom e ∈ T'.post.atoms := by
      rw [T'.post_atoms, hY']; exact mem_sdiff.mpr ⟨M.atom_mem e, hu⟩
    refine goodCell_of_connected_low (T'.post_connected hconn) hz ?_ hS
    rw [T'.post_deg (by rw [hY']; exact hu)]
    have h1 := deg_eraseBond_add M e (M.atom e)
    have h2 := hcap _ (M.atom_mem e)
    have h3 := Mole.outdeg_add_indeg M (M.atom e)
    rw [ite_of_pos rfl] at h1
    omega
  refine (hR L hL (MoleProp.eraseBond M e) hcapN _ E' hgood P hP).trans (mul_le_mul' le_rfl ?_)
  exact (E.toTwoExit hcap).afreeSup_post_eraseBond_le e heY T' hTY hTc hTd L γ δ (η / 2) C1

end WaveTurbulence.MoleProp4
