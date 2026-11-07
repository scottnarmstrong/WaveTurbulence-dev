/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceUnits
import Mathlib.Tactic

/-!
# B2a MK-RUNS: segments of a spine

Generic facts about the spine `L` of a block chain (`Spine M L U a b`), used to cut a marked group into runs and
survivors (o75 §2.5):
* `Spine.split_appMK`: a spine splits at any list boundary into two spines meeting in one joint;
* `Spine.sepMK`: members on the two sides of a third member are disjoint;
* `Spine.segMK`: a non-empty segment `R` of `L = P ++ R ++ Q` is a block, meeting its neighbours in one joint;
* `Spine.pairwise_interMK`: two members share at most one atom;
* `Spine.monoMK`: a spine whose members are vines of another molecule is a spine there.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole

section generic
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem mem_inter_singletonMK {U T : Finset V} {b v : V} (h : U ∩ T = {b}) (hU : v ∈ U) (hT : v ∈ T) : v = b := by
  have : v ∈ U ∩ T := mem_inter.mpr ⟨hU, hT⟩
  rw [h, mem_singleton] at this
  exact this

namespace Spine

theorem ne_nilMK {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (h : Spine M L U a b) : L ≠ [] := by
  cases h with
  | one _ => simp
  | snoc _ _ _ _ => simp

/-- A one-member spine is its member. -/
theorem singletonMK {s : Finset V × V × V} {U : Finset V} {a b : V} (h : Spine M [s] U a b) :
    s = (U, a, b) ∧ IsSomeVine M U a b := by
  rcases h.inv with ⟨T, hL, hU, hv⟩ | ⟨L', U', T, b', hL, _, hs', _, _, _⟩
  · simp only [List.cons.injEq, and_true] at hL
    subst hU
    exact ⟨hL, hv⟩
  · exfalso
    have hlen := congrArg List.length hL
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    have : L' = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact hs'.ne_nilMK this

/-- The right joint of the last member is the right end. -/
theorem last_sndMK {L : List (Finset V × V × V)} {t : Finset V × V × V} {U : Finset V} {a b : V}
    (h : Spine M (L ++ [t]) U a b) : t.2.2 = b := by
  rcases h.inv with ⟨T, hL, _, _⟩ | ⟨L', U', T, b', hL, _, _, _, _, _⟩
  · have := List.append_inj' (s₁ := L) (s₂ := []) (t₁ := [t]) (t₂ := [(T, a, b)]) (by simpa using hL) rfl
    simp only [List.cons.injEq, and_true] at this
    rw [this.2]
  · have := List.append_inj' hL rfl
    simp only [List.cons.injEq, and_true] at this
    rw [this.2]

/-- The left joint of the first member is the left end. -/
theorem head_fstMK {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (h : Spine M L U a b) :
    ∀ t ∈ L.head?, t.2.1 = a := by
  induction h with
  | one _ => intro t ht; simp at ht; rw [← ht]
  | @snoc L' U' T a' b' c' hs' _ _ _ ih =>
    intro t ht
    obtain ⟨t0, L0, rfl⟩ := List.exists_cons_of_ne_nil hs'.ne_nilMK
    simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at ht
    subst ht
    exact ih _ (by simp)

theorem cons_fstMK {t : Finset V × V × V} {L : List (Finset V × V × V)} {U : Finset V} {a b : V}
    (h : Spine M (t :: L) U a b) : t.2.1 = a := h.head_fstMK t (by simp)

/-- **Splitting a spine** at a list boundary. -/
theorem split_appMK {L1 L2 : List (Finset V × V × V)} {U : Finset V} {a b : V}
    (h : Spine M (L1 ++ L2) U a b) (h1 : L1 ≠ []) (h2 : L2 ≠ []) :
    ∃ U1 U2 p, Spine M L1 U1 a p ∧ Spine M L2 U2 p b ∧ U = U1 ∪ U2 ∧ U1 ∩ U2 = {p} := by
  induction L2 using List.reverseRecOn generalizing U b with
  | nil => exact absurd rfl h2
  | append_singleton L2' t ih =>
    rw [← List.append_assoc] at h
    rcases h.inv with ⟨T, hL, _, _⟩ | ⟨L', U', T, b', hL, hU, hs', hT, hi, hne⟩
    · exfalso
      have hlen := congrArg List.length hL
      simp only [List.length_append, List.length_singleton] at hlen
      exact h1 (List.eq_nil_of_length_eq_zero (by omega))
    · obtain ⟨hL1, ht⟩ := List.append_inj' hL rfl
      simp only [List.cons.injEq, and_true] at ht
      subst ht
      have hTe := isSomeVine_ends hT
      by_cases hL2 : L2' = []
      · subst hL2
        simp only [List.append_nil] at hL1
        subst hL1
        exact ⟨U', T, b', hs', Spine.one hT, hU, hi⟩
      · obtain ⟨U1, U2, p, hs1, hs2, hU', hi'⟩ := ih (hL1 ▸ hs') hL2
        have hb2 : b' ∈ U2 := hs2.ends.2.1
        have hp1 : p ∈ U1 := hs1.ends.2.1
        have hi2 : U2 ∩ T = {b'} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_inter.mpr ⟨hb2, hTe.1⟩, fun v hv => ?_⟩
          obtain ⟨hv1, hv2⟩ := mem_inter.mp hv
          exact mem_inter_singletonMK hi (hU' ▸ mem_union_right _ hv1) hv2
        have hpb : p ≠ b := by
          intro hpb
          subst hpb
          exact hTe.2.2 (mem_inter_singletonMK hi (hU' ▸ mem_union_left _ hp1) hTe.2.1).symm
        refine ⟨U1, U2 ∪ T, p, hs1, Spine.snoc hs2 hT hi2 hpb, by rw [hU, hU', union_assoc], ?_⟩
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_inter.mpr ⟨hp1, mem_union_left _ hs2.ends.1⟩,
          fun v hv => ?_⟩
        obtain ⟨hv1, hv2⟩ := mem_inter.mp hv
        rcases mem_union.mp hv2 with hv2 | hv2
        · exact mem_inter_singletonMK hi' hv1 hv2
        · have hvb : v = b' := mem_inter_singletonMK hi (hU' ▸ mem_union_left _ hv1) hv2
          subst hvb
          exact mem_inter_singletonMK hi' hv1 hb2

/-- **Separation**: members on the two sides of a third member share no atom. -/
theorem sepMK {A B : List (Finset V × V × V)} {s : Finset V × V × V} {U : Finset V} {a b : V}
    (h : Spine M (A ++ s :: B) U a b) {t t' : Finset V × V × V} (ht : t ∈ A) (ht' : t' ∈ B) :
    Disjoint t.1 t'.1 := by
  have hA : A ≠ [] := List.ne_nil_of_mem ht
  have hB : B ≠ [] := List.ne_nil_of_mem ht'
  rw [show A ++ s :: B = (A ++ [s]) ++ B by simp] at h
  obtain ⟨U1, U2, p, hs1, hs2, _, hi⟩ := h.split_appMK (by simp) hB
  obtain ⟨U0, Us, q, hs0, hss, hU1, hi0⟩ := hs1.split_appMK hA (by simp)
  obtain ⟨rfl, hsv⟩ := hss.singletonMK
  have hse := isSomeVine_ends hsv
  rw [Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨T, p', q'⟩ := t
  obtain ⟨T', p'', q''⟩ := t'
  have hv0 : v ∈ U0 := (hs0.mem_vine ht).2 hv
  have hv2 : v ∈ U2 := (hs2.mem_vine ht').2 hv'
  have hvp : v = p := mem_inter_singletonMK hi (hU1 ▸ mem_union_left _ hv0) hv2
  subst hvp
  exact hse.2.2 (mem_inter_singletonMK hi0 hv0 hse.2.1).symm

/-- Two members of a spine share at most one atom. -/
theorem pairwise_interMK {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (h : Spine M L U a b) :
    L.Pairwise (fun t t' => (t.1 ∩ t'.1).card ≤ 1) := by
  induction h with
  | one _ => exact List.pairwise_singleton _ _
  | @snoc L' U' T a' b' c' hs' _ hi _ ih =>
    refine List.pairwise_append.mpr ⟨ih, List.pairwise_singleton _ _, ?_⟩
    intro t ht t' ht'
    rw [List.mem_singleton] at ht'
    subst ht'
    obtain ⟨T0, p, q⟩ := t
    have hsub : T0 ∩ T ⊆ {b'} := by
      rw [← hi]
      exact inter_subset_inter_right (hs'.mem_vine ht).2
    exact (card_le_card hsub).trans (card_singleton b').le

/-- A spine whose members are vines of another molecule is a spine of that molecule. -/
theorem monoMK {D₂ : Type*} [Fintype D₂] [DecidableEq D₂] {N : Molecule V D₂}
    {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (h : Spine N L U a b)
    (hv : ∀ t ∈ L, IsSomeVine M t.1 t.2.1 t.2.2) : Spine M L U a b := by
  induction h with
  | @one T a' b' _ => exact Spine.one (hv (T, a', b') (by simp))
  | @snoc L' U' T a' b' c' _ _ hi hne ih =>
    exact Spine.snoc (ih fun t ht => hv t (List.mem_append_left _ ht))
      (hv (T, b', c') (by simp)) hi hne

/-- **A segment of a block chain is a block**, meeting the member before it and the member after it in exactly
its two end joints. -/
theorem segMK (hM : M.IsMolecule) {P R Q : List (Finset V × V × V)} {S : Finset V} {a b : V}
    (hs : Spine M (P ++ R ++ Q) S a b) (hB : M.IsBlock S a b) (hR : R ≠ []) :
    ∃ UR p q, Spine M R UR p q ∧ M.IsBlock UR p q ∧ UR ⊆ S ∧
      (∀ P' s, P = P' ++ [s] → s.2.2 = p ∧ s.1 ∩ UR = {p} ∧ a ∉ UR) ∧
      (∀ s Q', Q = s :: Q' → s.2.1 = q ∧ UR ∩ s.1 = {q} ∧ b ∉ UR) := by
  -- the suffix `R ++ Q`
  obtain ⟨URQ, p, hRQ, hBRQ, hsubRQ, hPside⟩ : ∃ URQ p, Spine M (R ++ Q) URQ p b ∧ M.IsBlock URQ p b ∧
      URQ ⊆ S ∧ ∀ P' s, P = P' ++ [s] → s.2.2 = p ∧ s.1 ∩ URQ = {p} ∧ a ∉ URQ := by
    by_cases hP : P = []
    · subst hP
      refine ⟨S, a, by simpa using hs, hB, subset_refl _, fun P' s h => ?_⟩
      exact absurd h.symm (by simp)
    · rw [List.append_assoc] at hs
      obtain ⟨UP, URQ, p, hsP, hsRQ, hS, hi⟩ := hs.split_appMK hP (by simp [hR])
      refine ⟨URQ, p, hsRQ, suffix_block_of_prefix_chain hM hsP.chain hsRQ.chain hi hS hB,
        hS ▸ subset_union_right, fun P' s hPs => ?_⟩
      subst hPs
      have hsp : s.2.2 = p := hsP.last_sndMK
      have hsv := hsP.mem_vine (T := s.1) (p := s.2.1) (q := s.2.2) (by simp)
      refine ⟨hsp, Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_inter.mpr
        ⟨hsp ▸ (isSomeVine_ends hsv.1).2.1, hsRQ.ends.1⟩, fun v hv => ?_⟩, fun ha => ?_⟩
      · obtain ⟨hv1, hv2⟩ := mem_inter.mp hv
        exact mem_inter_singletonMK hi (hsv.2 hv1) hv2
      · exact hsP.ends.2.2 (mem_inter_singletonMK hi hsP.ends.1 ha)
  by_cases hQ : Q = []
  · subst hQ
    simp only [List.append_nil] at hRQ
    refine ⟨URQ, p, b, hRQ, hBRQ, hsubRQ, hPside, fun s Q' h => absurd h.symm (by simp)⟩
  · obtain ⟨UR, UQ, q, hsR, hsQ, hU, hi⟩ := hRQ.split_appMK hR hQ
    refine ⟨UR, p, q, hsR, prefix_block_of_suffix_chain hM hsR.chain hsQ.chain hi hU hBRQ,
      (hU ▸ subset_union_left).trans hsubRQ, fun P' s hPs => ?_, fun s Q' hQs => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hPside P' s hPs
      refine ⟨h1, Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_inter.mpr ⟨?_, hsR.ends.1⟩, fun v hv => ?_⟩,
        fun ha => h3 (hU ▸ mem_union_left _ ha)⟩
      · have : p ∈ s.1 ∩ URQ := by rw [h2]; exact mem_singleton_self p
        exact (mem_inter.mp this).1
      · obtain ⟨hv1, hv2⟩ := mem_inter.mp hv
        exact mem_inter_singletonMK h2 hv1 (hU ▸ mem_union_left _ hv2)
    · subst hQs
      have hsq : s.2.1 = q := hsQ.cons_fstMK
      have hsv := hsQ.mem_vine (T := s.1) (p := s.2.1) (q := s.2.2) (by simp)
      refine ⟨hsq, Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_inter.mpr
        ⟨hsR.ends.2.1, hsq ▸ (isSomeVine_ends hsv.1).1⟩, fun v hv => ?_⟩, fun hb => ?_⟩
      · obtain ⟨hv1, hv2⟩ := mem_inter.mp hv
        exact mem_inter_singletonMK hi hv1 (hsv.2 hv2)
      · exact hsQ.ends.2.2.symm (mem_inter_singletonMK hi hb hsQ.ends.2.1)

end Spine

end generic

end WaveTurbulence.RedSplice
