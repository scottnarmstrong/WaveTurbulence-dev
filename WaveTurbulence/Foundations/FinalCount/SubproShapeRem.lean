/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.SubproShapeDC
import Mathlib.Tactic

/-!
# S4-SHAPE: simultaneous removal with two-double-bond pieces

`subsetvc_simultaneous_removal_connected` (universe) needs ordinary pieces that are single vines. `removal_connected_dc` extends it to
pieces that are chains of two double bonds `a = x = b` (TARGET Lemma `subsetvc`, "two double bonds"): the piece is replaced by its
first double bond `{a, x}`; then `x` survives, but it is pendant (its only kept bonds go to `b`), so the connectivity statement
contracts along `x ↦ b` (`sameComponent_contract`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.Vine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The adjacency of the molecule left by a removal, on the atoms of the ambient molecule. -/
def KeepAdj (M : Molecule V D) (S : Finset V) (L : List (RemovalPiece V D)) (s t : V) : Prop :=
  ∃ y, KeepDart M S L y ∧ M.atom y = s ∧ M.atom (M.mate y) = t

theorem sameComponent_iff_eqvGen (M : Molecule V D) (S : Finset V) (L : List (RemovalPiece V D)) (u v : V) :
    (removeBlocks M S L).SameComponent u v ↔ Relation.EqvGen (KeepAdj M S L) u v := by
  have hrel : (removeBlocks M S L).Adj = KeepAdj M S L := by
    funext s t
    apply propext
    constructor
    · rintro ⟨x, hx1, hx2⟩
      exact ⟨x.1, x.2, hx1, hx2⟩
    · rintro ⟨y, hy, h1, h2⟩
      exact ⟨⟨y, hy⟩, h1, h2⟩
  unfold Molecule.SameComponent
  rw [hrel]

/-- Contracting along a map `φ` that fixes the surviving atoms of `L` and sends each kept dart of `L'` to a connected pair of `L`. -/
theorem sameComponent_contract {M : Molecule V D} {S : Finset V} {L L' : List (RemovalPiece V D)} (φ : V → V)
    (hφ : ∀ v ∈ remainingAtoms S L, φ v = v)
    (h : ∀ z, KeepDart M S L' z → Relation.EqvGen (KeepAdj M S L) (φ (M.atom z)) (φ (M.atom (M.mate z))))
    {u v : V} (hu : u ∈ remainingAtoms S L) (hv : v ∈ remainingAtoms S L)
    (huv : (removeBlocks M S L').SameComponent u v) : (removeBlocks M S L).SameComponent u v := by
  rw [sameComponent_iff_eqvGen] at huv ⊢
  have key : ∀ s t, Relation.EqvGen (KeepAdj M S L') s t → Relation.EqvGen (KeepAdj M S L) (φ s) (φ t) := by
    intro s t hst
    induction hst with
    | rel s t hst =>
      obtain ⟨y, hy, rfl, rfl⟩ := hst
      exact h y hy
    | refl s => exact Relation.EqvGen.refl _
    | symm s t _ ih => exact ih.symm
    | trans s t r _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have := key u v huv
  rwa [hφ u hu, hφ v hv] at this

/-- A removal piece that is a block formed by a chain of two double bonds `a = x = b`. -/
def DblPiece (M : Molecule V D) (P : RemovalPiece V D) : Prop :=
  M.IsBlock P.atoms P.left P.right ∧ DoubleChain M P.atoms P.left P.right 2

open Classical in
/-- The middle atom of a two-double-bond piece. -/
noncomputable def midOf (M : Molecule V D) (P : RemovalPiece V D) : V :=
  if h : DblPiece M P then Classical.choose (doubleChain_two_split h.2) else P.left

open Classical in
/-- The first double bond of a two-double-bond piece (other pieces are unchanged). -/
noncomputable def halfPiece (M : Molecule V D) (P : RemovalPiece V D) : RemovalPiece V D :=
  if DblPiece M P then ⟨{P.left, midOf M P}, P.left, midOf M P, univ.filter (M.InGroup {P.left, midOf M P})⟩ else P

theorem halfPiece_of_not {M : Molecule V D} {P : RemovalPiece V D} (h : ¬ DblPiece M P) : halfPiece M P = P := by
  simp [halfPiece, h]

theorem halfPiece_of_dbl {M : Molecule V D} {P : RemovalPiece V D} (h : DblPiece M P) :
    halfPiece M P = ⟨{P.left, midOf M P}, P.left, midOf M P, univ.filter (M.InGroup {P.left, midOf M P})⟩ := by
  simp [halfPiece, h]

theorem DblPiece.spec {M : Molecule V D} {P : RemovalPiece V D} (h : DblPiece M P) :
    P.atoms = {P.left, midOf M P, P.right} ∧ M.IsVine .I {P.left, midOf M P} P.left (midOf M P) ∧
      M.IsVine .I {midOf M P, P.right} (midOf M P) P.right ∧ P.left ≠ P.right := by
  unfold midOf
  simp only [h, dite_true]
  exact Classical.choose_spec (doubleChain_two_split h.2)

theorem DblPiece.mid_ne {M : Molecule V D} {P : RemovalPiece V D} (h : DblPiece M P) :
    midOf M P ≠ P.left ∧ midOf M P ≠ P.right := by
  obtain ⟨_, h1, h2, _⟩ := h.spec
  exact ⟨fun e => h1.1.2.2.2.1 e.symm, fun e => h2.1.2.2.2.1 e⟩

theorem DblPiece.mid_mem_interior {M : Molecule V D} {P : RemovalPiece V D} (h : DblPiece M P) :
    midOf M P ∈ P.interior := by
  obtain ⟨he, _, _, _⟩ := h.spec
  obtain ⟨n1, n2⟩ := h.mid_ne
  unfold RemovalPiece.interior
  rw [he]
  simp [n1, n2]

theorem DblPiece.interior_eq {M : Molecule V D} {P : RemovalPiece V D} (h : DblPiece M P) :
    P.interior = {midOf M P} := by
  obtain ⟨he, _, _, hab⟩ := h.spec
  obtain ⟨n1, n2⟩ := h.mid_ne
  unfold RemovalPiece.interior
  rw [he]
  ext v
  simp only [mem_sdiff, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hv | hv | hv, hn⟩
    · exact absurd (Or.inl hv) hn
    · exact hv
    · exact absurd (Or.inr hv) hn
  · rintro rfl
    exact ⟨Or.inr (Or.inl rfl), by tauto⟩

theorem halfPiece_atoms_subset (M : Molecule V D) (P : RemovalPiece V D) : (halfPiece M P).atoms ⊆ P.atoms := by
  by_cases h : DblPiece M P
  · rw [halfPiece_of_dbl h]
    obtain ⟨he, _⟩ := h.spec
    intro v hv
    rw [he]
    simp only [mem_insert, mem_singleton] at hv ⊢
    tauto
  · rw [halfPiece_of_not h]

theorem halfPiece_interior (M : Molecule V D) (P : RemovalPiece V D) :
    (halfPiece M P).interior ⊆ P.interior := by
  by_cases h : DblPiece M P
  · rw [halfPiece_of_dbl h]
    unfold RemovalPiece.interior
    intro v hv
    simp at hv
  · rw [halfPiece_of_not h]

/-- A dart of the group of `P` at a joint of a two-double-bond piece ends at the middle atom. -/
theorem DblPiece.dart_at_joint {M : Molecule V D} {P : RemovalPiece V D} (h : DblPiece M P) {w : D}
    (hw : M.atom w = P.left ∨ M.atom w = P.right) (hg : M.InGroup P.atoms w) : M.atom (M.mate w) = midOf M P := by
  obtain ⟨he, h1, h2, _⟩ := h.spec
  rcases hw with hw | hw
  · exact (joint_darts_pair h.1 h1.1 (by rw [he]; intro v hv; simp at hv ⊢; tauto) hw hg).2
  · have hB := Mole.block_swap_joints M h.1
    have hA := Mole.block_swap_joints M h2.1
    rw [Finset.pair_comm] at hA
    exact (joint_darts_pair hB hA (by rw [he]; intro v hv; simp at hv ⊢; tauto) hw hg).2

/-- **TARGET Lemma `subsetvc`, simultaneous removal, with two-double-bond pieces.** The universe's
`subsetvc_simultaneous_removal_connected`, where each ordinary piece is a single vine or a block that is a chain of two double
bonds. -/
theorem removal_connected_dc (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b : V} (ps : List (RemovalPiece V D)) (qs : List (AdjointPiece M))
    (hvine : ∀ P ∈ ps, IsSomeVine M P.atoms P.left P.right ∨ DblPiece M P)
    (hsub : ∀ P ∈ ps, P.atoms ⊆ U)
    (hD : ∀ P ∈ ps, P.darts = univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps, ∀ Q ∈ ps, P ≠ Q → Disjoint P.atoms Q.atoms)
    (hQsub : ∀ Q ∈ qs, Q.atoms ⊆ U)
    (hQdis : ∀ P ∈ qs, ∀ Q ∈ qs, P ≠ Q → Disjoint P.atoms Q.atoms)
    (hcross : ∀ P ∈ ps, ∀ Q ∈ qs, Disjoint P.atoms Q.atoms)
    (L γ η : ℝ) (w : Mom d) (z : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w z κ) (hz : ∀ v ∈ M.atoms, M.deg v = 4 → z v = 0)
    (hSG : ∀ P ∈ ps, ∃ r' : Mom d, M.IsBlockGap L w κ P.atoms P.left r' ∧ Molecule.gapKind L γ η r' = .SG)
    (houter : IsDV M U a b ∨ ∃ C : VineLikeObject M U a b, ∃ r : Mom d,
      C.IsGap L w κ r ∧ (Molecule.gapKind L γ η r = .LG ∨ Molecule.gapKind L γ η r = .ZG)) :
    ∀ u ∈ remainingAtoms U (ps ++ qs.map AdjointPiece.toRemoval),
      ∀ v ∈ remainingAtoms U (ps ++ qs.map AdjointPiece.toRemoval),
      (removeBlocks M U (ps ++ qs.map AdjointPiece.toRemoval)).SameComponent u v := by
  classical
  intro u hu v hv
  set ps' := ps.map (halfPiece M) with hps'
  set Q := qs.map AdjointPiece.toRemoval with hQ
  have hmem' : ∀ P' ∈ ps', ∃ P ∈ ps, P' = halfPiece M P := fun P' h => by
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp h
    exact ⟨P, hP, rfl⟩
  -- the primed family satisfies the hypotheses of the universe lemma
  have hU' := subsetvc_simultaneous_removal_connected M hM ps' qs
    (by
      intro P' hP'
      obtain ⟨P, hP, rfl⟩ := hmem' P' hP'
      by_cases h : DblPiece M P
      · rw [halfPiece_of_dbl h]
        obtain ⟨_, h1, _, _⟩ := h.spec
        exact ⟨.I, h1⟩
      · rw [halfPiece_of_not h]
        exact (hvine P hP).resolve_right h)
    (by
      intro P' hP'
      obtain ⟨P, hP, rfl⟩ := hmem' P' hP'
      exact (halfPiece_atoms_subset M P).trans (hsub P hP))
    (by
      intro P' hP'
      obtain ⟨P, hP, rfl⟩ := hmem' P' hP'
      by_cases h : DblPiece M P
      · rw [halfPiece_of_dbl h]
      · rw [halfPiece_of_not h]; exact hD P hP)
    (by
      intro P' hP' Q' hQ' hne
      obtain ⟨P, hP, rfl⟩ := hmem' P' hP'
      obtain ⟨Q, hQ, rfl⟩ := hmem' Q' hQ'
      have hPQ : P ≠ Q := fun e => hne (e ▸ rfl)
      exact Finset.disjoint_of_subset_left (halfPiece_atoms_subset M P)
        (Finset.disjoint_of_subset_right (halfPiece_atoms_subset M Q) (hdis P hP Q hQ hPQ)))
    hQsub hQdis
    (by
      intro P' hP' Q' hQ'
      obtain ⟨P, hP, rfl⟩ := hmem' P' hP'
      exact Finset.disjoint_of_subset_left (halfPiece_atoms_subset M P) (hcross P hP Q' hQ'))
    L γ η w z κ hκ hz
    (by
      intro P' hP'
      obtain ⟨P, hP, rfl⟩ := hmem' P' hP'
      obtain ⟨r', hr', hk⟩ := hSG P hP
      refine ⟨r', ?_, hk⟩
      by_cases h : DblPiece M P
      · rw [halfPiece_of_dbl h]
        obtain ⟨he, h1, h2, _⟩ := h.spec
        obtain ⟨x₁, x₂, e1, e2, g1, g2, o1, o2, rfl⟩ := hr'
        have hsubA : ({P.left, midOf M P} : Finset V) ⊆ P.atoms := by
          rw [he]; intro v hv; simp at hv ⊢; tauto
        exact ⟨x₁, x₂, e1, e2, (joint_darts_pair h.1 h1.1 hsubA e1 g1).1, (joint_darts_pair h.1 h1.1 hsubA e2 g2).1,
          o1, o2, rfl⟩
      · rw [halfPiece_of_not h]; exact hr')
    houter
  -- contraction along `mid ↦ right`
  have hmid_uniq : ∀ P ∈ ps, ∀ P2 ∈ ps, DblPiece M P → DblPiece M P2 → midOf M P = midOf M P2 → P = P2 := by
    intro P hP P2 hP2 h h2 he
    by_contra hne
    have hd := hdis P hP P2 hP2 hne
    have m1 : midOf M P ∈ P.atoms := by rw [h.spec.1]; simp
    have m2 : midOf M P ∈ P2.atoms := by rw [he, h2.spec.1]; simp
    exact Finset.disjoint_left.mp hd m1 m2
  let φ : V → V := fun w => if hh : ∃ P ∈ ps, DblPiece M P ∧ midOf M P = w then (Classical.choose hh).right else w
  have hφmid : ∀ P ∈ ps, DblPiece M P → φ (midOf M P) = P.right := by
    intro P hP h
    have hh : ∃ P2 ∈ ps, DblPiece M P2 ∧ midOf M P2 = midOf M P := ⟨P, hP, h, rfl⟩
    simp only [φ, hh, dite_true]
    obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hh
    rw [hmid_uniq _ h1 P hP h2 h h3]
  have hφright : ∀ P ∈ ps, DblPiece M P → φ P.right = P.right := by
    intro P hP h
    have hh : ¬ ∃ P2 ∈ ps, DblPiece M P2 ∧ midOf M P2 = P.right := by
      rintro ⟨P2, hP2, h2, he⟩
      by_cases hPP : P2 = P
      · subst hPP; exact h2.mid_ne.2 he
      · have hd := hdis P2 hP2 P hP hPP
        have m1 : midOf M P2 ∈ P2.atoms := by rw [h2.spec.1]; simp
        have m2 : midOf M P2 ∈ P.atoms := by rw [he, h.spec.1]; simp
        exact Finset.disjoint_left.mp hd m1 m2
    simp only [φ, hh, dite_false]
  have hR'R : ∀ v ∈ remainingAtoms U (ps' ++ Q), v ∉ remainingAtoms U (ps ++ Q) →
      ∃ P ∈ ps, DblPiece M P ∧ v = midOf M P := by
    intro v h1 h2
    unfold remainingAtoms at h1 h2
    rw [mem_filter] at h1 h2
    push Not at h2
    obtain ⟨hvU, hv1⟩ := h1
    obtain ⟨P, hP, hvP⟩ := h2 hvU
    rcases List.mem_append.mp hP with hP | hP
    · by_cases h : DblPiece M P
      · exact ⟨P, hP, h, by rw [h.interior_eq] at hvP; exact mem_singleton.mp hvP⟩
      · exfalso
        exact hv1 (halfPiece M P) (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨P, hP, rfl⟩)))
          (by rw [halfPiece_of_not h]; exact hvP)
    · exact (hv1 P (List.mem_append.mpr (Or.inr hP)) hvP).elim
  have hRR' : ∀ v ∈ remainingAtoms U (ps ++ Q), v ∈ remainingAtoms U (ps' ++ Q) := by
    intro v hv
    unfold remainingAtoms at hv ⊢
    rw [mem_filter] at hv ⊢
    refine ⟨hv.1, fun P hP => ?_⟩
    rcases List.mem_append.mp hP with hP | hP
    · obtain ⟨P0, hP0, rfl⟩ := List.mem_map.mp hP
      exact fun h => hv.2 P0 (List.mem_append.mpr (Or.inl hP0)) (halfPiece_interior M P0 h)
    · exact hv.2 P (List.mem_append.mpr (Or.inr hP))
  have hφid : ∀ v ∈ remainingAtoms U (ps ++ Q), φ v = v := by
    intro v hv
    have hh : ¬ ∃ P ∈ ps, DblPiece M P ∧ midOf M P = v := by
      rintro ⟨P, hP, h, he⟩
      unfold remainingAtoms at hv
      rw [mem_filter] at hv
      exact hv.2 P (List.mem_append.mpr (Or.inl hP)) (he ▸ h.mid_mem_interior)
    simp only [φ, hh, dite_false]
  have kept_mid : ∀ y, KeepDart M U (ps' ++ Q) y → M.atom y ∉ remainingAtoms U (ps ++ Q) →
      φ (M.atom y) = φ (M.atom (M.mate y)) := by
    intro y hy hnR
    obtain ⟨P, hP, h, he⟩ := hR'R _ hy.1 hnR
    obtain ⟨_, h1, h2, hab⟩ := h.spec
    rcases dart_at_mid hM hab h1 h2 (he ▸ rfl : M.atom y = midOf M P) with ⟨hg, _⟩ | ⟨_, hpb⟩
    · exfalso
      have hP' : halfPiece M P ∈ ps' ++ Q := List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨P, hP, rfl⟩))
      apply (hy.2.2 _ hP').1
      rw [halfPiece_of_dbl h]
      exact mem_filter.mpr ⟨mem_univ _, hg⟩
    · rw [he, hpb, hφmid P hP h, hφright P hP h]
  refine sameComponent_contract (L := ps ++ Q) (L' := ps' ++ Q) φ hφid ?_ hu hv
    (hU' u (hRR' u hu) v (hRR' v hv))
  intro y hy
  by_cases hs : M.atom y ∈ remainingAtoms U (ps ++ Q)
  · by_cases ht : M.atom (M.mate y) ∈ remainingAtoms U (ps ++ Q)
    · rw [hφid _ hs, hφid _ ht]
      refine Relation.EqvGen.rel _ _ ⟨y, ⟨hs, ht, ?_⟩, rfl, rfl⟩
      intro P hP
      rcases List.mem_append.mp hP with hP | hP
      · by_cases h : DblPiece M P
        · have hinR : ∀ w : D, M.atom w ∈ remainingAtoms U (ps ++ Q) → M.atom (M.mate w) ∈ remainingAtoms U (ps ++ Q) →
              w ∉ P.darts := by
            intro w hw1 hw2 hwd
            rw [hD P hP, mem_filter] at hwd
            have hg : M.InGroup P.atoms w := hwd.2
            have hnint : M.atom w ∉ P.interior := by
              unfold remainingAtoms at hw1
              exact (mem_filter.mp hw1).2 P (List.mem_append.mpr (Or.inl hP))
            have hnm : M.atom w ≠ midOf M P := by
              intro e; apply hnint; rw [h.interior_eq]; exact mem_singleton.mpr e
            have hj : M.atom w = P.left ∨ M.atom w = P.right := by
              have := hg.1
              rw [h.spec.1] at this
              simp only [mem_insert, mem_singleton] at this
              rcases this with h' | h' | h'
              · exact Or.inl h'
              · exact absurd h' hnm
              · exact Or.inr h'
            have hm := h.dart_at_joint hj hg
            have hint : M.atom (M.mate w) ∈ P.interior := hm ▸ h.mid_mem_interior
            unfold remainingAtoms at hw2
            exact (mem_filter.mp hw2).2 P (List.mem_append.mpr (Or.inl hP)) hint
          refine ⟨hinR y hs ht, ?_⟩
          apply hinR (M.mate y) ht
          rw [M.mate_mate]; exact hs
        · have := hy.2.2 (halfPiece M P) (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨P, hP, rfl⟩)))
          rwa [halfPiece_of_not h] at this
      · exact hy.2.2 P (List.mem_append.mpr (Or.inr hP))
    · have hy2 : KeepDart M U (ps' ++ Q) (M.mate y) := keepDart_mate M U _ hy
      have := kept_mid (M.mate y) hy2 ht
      rw [M.mate_mate] at this
      rw [this]
      exact Relation.EqvGen.refl _
  · rw [kept_mid y hy hs]
    exact Relation.EqvGen.refl _

end WaveTurbulence.Subpro
