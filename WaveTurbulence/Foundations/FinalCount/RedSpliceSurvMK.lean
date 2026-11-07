/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceRunsMK3
import Mathlib.Tactic

/-!
# B2a MK-RUNS: the canonical form of the runs and survivors of a marked group

For *any* `U : MarkedGroupUnits G S Mk` (in particular the one chosen by `groupUnitsMk`) and any spine `L` of the
group `S`:
* `MarkedGroupUnits.run_canonMK`: every run is the union of a maximal segment of unmarked-`𝒱` members of `L`
  (by the walk lemma `Spine.walkMK`: a chain of members of a spine is a segment of it);
* `MarkedGroupUnits.surv_localMK`: every survivor is a member `m` of `L` that is not unmarked-`𝒱`, and
  `L = P ++ RL ++ m :: RR ++ Q` where `RL` (resp. `RR`) is the run at the left (resp. right) joint of `m`, or empty
  when no run contains that joint; a run meets `m` only inside `RL` or `RR`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1

/-- In a list without duplicates an element splits the list in one way only. -/
theorem app_cons_inj_of_nodupMK {α : Type*} {x : α} :
    ∀ {s1 t1 s2 t2 : List α}, (s1 ++ x :: t1).Nodup → s1 ++ x :: t1 = s2 ++ x :: t2 → s1 = s2 ∧ t1 = t2
  | [], t1, [], t2, _, h => by simpa using h
  | [], t1, y :: s2, t2, hn, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp at hn
  | y :: s1, t1, [], t2, hn, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp at hn
  | y :: s1, t1, z :: s2, t2, hn, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨h1, h2⟩ := app_cons_inj_of_nodupMK (List.nodup_cons.mp hn).2 h
    exact ⟨by rw [h1], h2⟩

section generic
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

namespace Spine

theorem mem_vine'MK {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (hs : Spine M L U a b)
    {t : Finset V × V × V} (ht : t ∈ L) : IsSomeVine M t.1 t.2.1 t.2.2 ∧ t.1 ⊆ U :=
  hs.mem_vine (T := t.1) (p := t.2.1) (q := t.2.2) ht

/-- The members of a spine are pairwise distinct. -/
theorem nodupMK {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (hs : Spine M L U a b) : L.Nodup := by
  refine List.Pairwise.imp_of_mem ?_ hs.pairwise_interMK
  intro t t' ht _ hle heq
  subst heq
  have he := isSomeVine_ends (hs.mem_vine'MK ht).1
  have hsub : ({t.2.1, t.2.2} : Finset V) ⊆ t.1 ∩ t.1 := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact mem_inter.mpr ⟨he.1, he.1⟩
    · rw [mem_singleton] at hv; subst hv; exact mem_inter.mpr ⟨he.2.1, he.2.1⟩
  have := card_le_card hsub
  rw [card_pair he.2.2] at this
  omega

/-- An atom shared by a member `m` and a member `r` before (resp. after) it is the left (resp. right) joint of
`m`. -/
theorem joint_leftMK {P Q : List (Finset V × V × V)} {m r : Finset V × V × V} {U : Finset V} {a b : V}
    (hs : Spine M (P ++ m :: Q) U a b) (hr : r ∈ P) {v : V} (hvr : v ∈ r.1) (hvm : v ∈ m.1) : v = m.2.1 := by
  obtain ⟨UP, UQ, p, hsP, hsQ, _, hi⟩ := hs.split_appMK (List.ne_nil_of_mem hr) (by simp)
  rw [hsQ.cons_fstMK]
  exact mem_inter_singletonMK hi ((hsP.mem_vine'MK hr).2 hvr)
    ((hsQ.mem_vine'MK (t := m) (by simp)).2 hvm)

theorem joint_rightMK {P Q : List (Finset V × V × V)} {m r : Finset V × V × V} {U : Finset V} {a b : V}
    (hs : Spine M (P ++ m :: Q) U a b) (hr : r ∈ Q) {v : V} (hvr : v ∈ r.1) (hvm : v ∈ m.1) : v = m.2.2 := by
  rw [show P ++ m :: Q = (P ++ [m]) ++ Q by simp] at hs
  obtain ⟨UP, UQ, q, hsP, hsQ, _, hi⟩ := hs.split_appMK (by simp) (List.ne_nil_of_mem hr)
  rw [hsP.last_sndMK]
  exact mem_inter_singletonMK hi ((hsP.mem_vine'MK (t := m) (by simp)).2 hvm) ((hsQ.mem_vine'MK hr).2 hvr)

/-- **The walk lemma**: a chain whose members are (by atoms) members of a spine `L` is, as a set of atoms, the union
of a segment of `L`. -/
theorem walkMK {D₂ : Type*} [Fintype D₂] [DecidableEq D₂] {N : Molecule V D₂}
    {L : List (Finset V × V × V)} {S : Finset V} {a b : V} (hs : Spine M L S a b)
    {Lu : List (Finset V × V × V)} {U : Finset V} {p q : V} (hu : Spine N Lu U p q)
    (hmem : ∀ t ∈ Lu, ∃ t0 ∈ L, t0.1 = t.1) :
    ∃ P R Q, L = P ++ R ++ Q ∧ R ≠ [] ∧ (∀ v, v ∈ U ↔ ∃ t ∈ R, v ∈ t.1) ∧ ∀ t ∈ R, ∃ t' ∈ Lu, t'.1 = t.1 := by
  induction hu with
  | @one T p' q' hv =>
    obtain ⟨t0, ht0, hT⟩ := hmem (T, p', q') (by simp)
    obtain ⟨P, Q, hPQ⟩ := List.append_of_mem ht0
    refine ⟨P, [t0], Q, by simpa using hPQ, by simp, fun v => ?_, fun t ht => ?_⟩
    · simp [hT]
    · rw [List.mem_singleton] at ht
      subst ht
      exact ⟨(T, p', q'), by simp, hT.symm⟩
  | @snoc Lu' U' T p' q' c' hu' hT hi hne ih =>
    obtain ⟨P, R, Q, hL, hR, hU, hRm⟩ := ih fun t ht => hmem t (List.mem_append_left _ ht)
    obtain ⟨t0, ht0, hT0⟩ := hmem (T, q', c') (by simp)
    have hTe := isSomeVine_ends hT
    -- `t0` is not in `R`
    have ht0R : t0 ∉ R := by
      intro h
      have hc : c' ∈ U' := (hU c').mpr ⟨t0, h, by rw [hT0]; exact hTe.2.1⟩
      exact hTe.2.2 (mem_inter_singletonMK hi hc hTe.2.1).symm
    -- `t0` meets `R` in `q'`
    obtain ⟨r, hr, hqr⟩ := (hU q').mp hu'.ends.2.1
    have hqt0 : q' ∈ t0.1 := by rw [hT0]; exact hTe.1
    have hmem' : ∀ t ∈ t0 :: R ++ [t0], ∃ t' ∈ Lu' ++ [(T, q', c')], t'.1 = t.1 := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨(T, q', c'), by simp, hT0.symm⟩
        · obtain ⟨t', ht', h'⟩ := hRm t ht
          exact ⟨t', List.mem_append_left _ ht', h'⟩
      · rw [List.mem_singleton] at ht
        subst ht
        exact ⟨(T, q', c'), by simp, hT0.symm⟩
    have hUnion : ∀ R' : List (Finset V × V × V), (∀ t, t ∈ R' ↔ t ∈ R ∨ t = t0) →
        ∀ v, v ∈ U' ∪ T ↔ ∃ t ∈ R', v ∈ t.1 := by
      intro R' hR' v
      rw [mem_union, hU v]
      constructor
      · rintro (⟨t, ht, hv⟩ | hv)
        · exact ⟨t, (hR' t).mpr (Or.inl ht), hv⟩
        · exact ⟨t0, (hR' t0).mpr (Or.inr rfl), by rw [hT0]; exact hv⟩
      · rintro ⟨t, ht, hv⟩
        rcases (hR' t).mp ht with ht | ht
        · exact Or.inl ⟨t, ht, hv⟩
        · subst ht
          have h0 : t.1 = T := hT0
          exact Or.inr (h0 ▸ hv)
    rw [hL] at ht0
    rcases List.mem_append.mp ht0 with ht0 | ht0
    · rcases List.mem_append.mp ht0 with ht0 | ht0
      · -- `t0` lies before `R`: it is the last member before it
        obtain ⟨P1, P2, rfl⟩ := List.append_of_mem ht0
        cases P2 with
        | nil =>
          refine ⟨P1, t0 :: R, Q, by rw [hL]; simp, by simp, hUnion _ (fun t => by simp [or_comm]), ?_⟩
          intro t ht
          exact hmem' t (List.mem_append_left _ ht)
        | cons s P3 =>
          exfalso
          have hs' : Spine M ((P1 ++ [t0]) ++ s :: (P3 ++ R ++ Q)) S a b := by rw [hL] at hs; simpa using hs
          exact Finset.disjoint_left.mp (hs'.sepMK (by simp) (by simp [hr])) hqt0 hqr
      · exact absurd ht0 ht0R
    · -- `t0` lies after `R`: it is the first member after it
      obtain ⟨Q1, Q2, rfl⟩ := List.append_of_mem ht0
      cases Q1 with
      | nil =>
        refine ⟨P, R ++ [t0], Q2, by rw [hL]; simp, by simp, hUnion _ (fun t => by simp), ?_⟩
        intro t ht
        exact hmem' t (by simp only [List.mem_append, List.mem_cons] at ht ⊢; tauto)
      | cons s Q3 =>
        exfalso
        have hs' : Spine M ((P ++ R) ++ s :: (Q3 ++ t0 :: Q2)) S a b := by rw [hL] at hs; simpa using hs
        exact Finset.disjoint_left.mp (hs'.sepMK (by simp [hr]) (by simp)) hqr hqt0

end Spine

end generic

variable {w : ℕ} {G : Garden w}

section canon
variable {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
  {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} {S : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {Mk : Set (CLVine G)}

/-- **The runs are the maximal segments of unmarked-`𝒱` members** of any spine of the group. -/
theorem MarkedGroupUnits.run_canonMK (U : MarkedGroupUnits G S Mk) (hs : Spine N L S a b)
    (hvineM : ∀ t ∈ L, IsSomeVine G.molecule t.1 t.2.1 t.2.2)
    (hingr : ∀ t ∈ L, IsIngredient G.molecule S t.1)
    (hmemb : ∀ T, IsIngredient G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L)
    {u : CLBlock G} (hu : u ∈ U.runs) :
    ∃ P R Q, L = P ++ R ++ Q ∧ R ≠ [] ∧ (∀ t ∈ R, UnmMemMK G Mk t) ∧ (∀ v, v ∈ u.atoms ↔ ∃ t ∈ R, v ∈ t.1) ∧
      (∀ P1 s, P = P1 ++ [s] → ¬ UnmMemMK G Mk s) ∧ (∀ s Q1, Q = s :: Q1 → ¬ UnmMemMK G Mk s) := by
  obtain ⟨Lu, hsu, hLu⟩ := U.spine u hu
  have hmem : ∀ t ∈ Lu, ∃ t0 ∈ L, t0.1 = t.1 := by
    intro t ht
    obtain ⟨c, -, -, hci, hct⟩ := hLu t ht
    obtain ⟨p, q, h | h⟩ := hmemb _ hci
    · exact ⟨_, h, hct⟩
    · exact ⟨_, h, hct⟩
  obtain ⟨P, R, Q, hL, hR, hiff, hRm⟩ := hs.walkMK hsu hmem
  have hRg : ∀ t ∈ R, UnmMemMK G Mk t := by
    intro t ht
    obtain ⟨t', ht', h'⟩ := hRm t ht
    obtain ⟨c, hcV, hcMk, -, hct⟩ := hLu t' ht'
    exact ⟨c, hcV, hcMk, hct.trans h'⟩
  -- a neighbouring unmarked member meeting the run lies in it (`maximal`)
  have hin : ∀ s ∈ L, UnmMemMK G Mk s → ∀ v ∈ s.1, v ∈ u.atoms → s.1 ⊆ u.atoms := by
    intro s hsL hsg v hvs hvu
    obtain ⟨c, hcV, hcMk, hcs⟩ := hsg
    have hci : IsIngredient G.molecule S c.atoms := hcs ▸ hingr s hsL
    have hnd : ¬ Disjoint c.atoms u.atoms := Finset.not_disjoint_iff.mpr ⟨v, hcs ▸ hvs, hvu⟩
    exact hcs ▸ U.maximal u hu c hcV hcMk hci hnd
  have hRsub : ∀ U2 p' b', Spine N (R ++ Q) U2 p' b' → u.atoms ⊆ U2 := by
    intro U2 p' b' h2 v hv
    obtain ⟨t, ht, hvt⟩ := (hiff v).mp hv
    exact (h2.mem_vine'MK (List.mem_append_left _ ht)).2 hvt
  obtain ⟨r0, R', rfl⟩ := List.exists_cons_of_ne_nil hR
  refine ⟨P, r0 :: R', Q, hL, hR, hRg, hiff, fun P1 s hPs => ?_, fun s Q1 hQs => ?_⟩
  · intro hsg
    subst hPs
    have hs' : Spine N ((P1 ++ [s]) ++ (r0 :: R' ++ Q)) S a b := by rw [hL] at hs; simpa using hs
    obtain ⟨U1, U2, p', hs1, hs2, _, hi⟩ := hs'.split_appMK (by simp) (by simp)
    have hsp : s.2.2 = p' := hs1.last_sndMK
    have hr0 : r0.2.1 = p' := hs2.cons_fstMK
    have he := isSomeVine_ends (hvineM s (by rw [hL]; simp))
    have hp'u : p' ∈ u.atoms :=
      (hiff p').mpr ⟨r0, by simp, hr0 ▸ (isSomeVine_ends (hvineM r0 (by rw [hL]; simp))).1⟩
    have hsu := hin s (by rw [hL]; simp) hsg p' (hsp ▸ he.2.1) hp'u
    have h1 : s.2.1 = p' := mem_inter_singletonMK hi ((hs1.mem_vine'MK (t := s) (by simp)).2 he.1)
      (hRsub U2 p' b hs2 (hsu he.1))
    exact he.2.2 (h1.trans hsp.symm)
  · intro hsg
    subst hQs
    obtain ⟨R'', rl, hRl⟩ := List.eq_nil_or_concat (r0 :: R') |>.resolve_left (by simp)
    have hs' : Spine N ((P ++ r0 :: R') ++ s :: Q1) S a b := by rw [hL] at hs; simpa using hs
    obtain ⟨U1, U2, q', hs1, hs2, _, hi⟩ := hs'.split_appMK (by simp) (by simp)
    have hsq : s.2.1 = q' := hs2.cons_fstMK
    have hrl : rl.2.2 = q' := by
      rw [hRl] at hs1
      exact (show Spine N ((P ++ R'') ++ [rl]) U1 a q' by simpa using hs1).last_sndMK
    have hrlR : rl ∈ r0 :: R' := by rw [hRl]; simp
    have he := isSomeVine_ends (hvineM s (by rw [hL]; simp))
    have hq'u : q' ∈ u.atoms :=
      (hiff q').mpr ⟨rl, hrlR, hrl ▸ (isSomeVine_ends (hvineM rl (by
        rw [hL]; exact List.mem_append_left _ (List.mem_append_right _ hrlR)))).2.1⟩
    have hsu := hin s (by rw [hL]; simp) hsg q' (hsq ▸ he.1) hq'u
    have hu1 : u.atoms ⊆ U1 := by
      intro v hv
      obtain ⟨t, ht, hvt⟩ := (hiff v).mp hv
      exact (hs1.mem_vine'MK (List.mem_append_right _ ht)).2 hvt
    have h2 : s.2.2 = q' := mem_inter_singletonMK hi (hu1 (hsu he.2.1))
      ((hs2.mem_vine'MK (t := s) (by simp)).2 he.2.1)
    exact he.2.2 (hsq.trans h2.symm)

/-- A run meeting the left joint of a member `m` that is not unmarked-`𝒱` is the segment just before `m`. -/
theorem run_adj_leftMK (hs : Spine N L S a b) (hvineM : ∀ t ∈ L, IsSomeVine G.molecule t.1 t.2.1 t.2.2)
    {P0 Q0 Pu Ru Qu : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {m r : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (hL : L = P0 ++ m :: Q0)
    (hLu : L = Pu ++ Ru ++ Qu) (hmR : m ∉ Ru) (hr : r ∈ Ru) (hxr : m.2.1 ∈ r.1) :
    P0 = Pu ++ Ru ∧ Q0 = Qu.tail := by
  have hmL : m ∈ L := by rw [hL]; simp
  have he := isSomeVine_ends (hvineM m hmL)
  have hmL' : m ∈ Pu ++ Ru ++ Qu := hLu ▸ hmL
  rcases List.mem_append.mp hmL' with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · exfalso
      obtain ⟨Pa, Pb, rfl⟩ := List.append_of_mem hm
      cases Pb with
      | nil =>
        have hs' : Spine N (Pa ++ m :: (Ru ++ Qu)) S a b := by rw [hLu] at hs; simpa using hs
        exact he.2.2 (hs'.joint_rightMK (List.mem_append_left _ hr) hxr he.1)
      | cons s Pc =>
        have hs' : Spine N ((Pa ++ [m]) ++ s :: (Pc ++ Ru ++ Qu)) S a b := by rw [hLu] at hs; simpa using hs
        exact Finset.disjoint_left.mp (hs'.sepMK (by simp) (by simp [hr])) he.1 hxr
    · exact absurd hm hmR
  · obtain ⟨Qa, Qb, rfl⟩ := List.append_of_mem hm
    cases Qa with
    | nil =>
      have h2 : P0 ++ m :: Q0 = (Pu ++ Ru) ++ m :: Qb := by rw [← hL, hLu]; simp
      obtain ⟨h1, h3⟩ := app_cons_inj_of_nodupMK (hL ▸ hs.nodupMK) h2
      exact ⟨h1, by simp [h3]⟩
    | cons s Qc =>
      exfalso
      have hs' : Spine N ((Pu ++ Ru) ++ s :: (Qc ++ m :: Qb)) S a b := by rw [hLu] at hs; simpa using hs
      exact Finset.disjoint_left.mp (hs'.sepMK (by simp [hr]) (by simp)) hxr he.1

/-- A run meeting the right joint of a member `m` that is not unmarked-`𝒱` is the segment just after `m`. -/
theorem run_adj_rightMK (hs : Spine N L S a b) (hvineM : ∀ t ∈ L, IsSomeVine G.molecule t.1 t.2.1 t.2.2)
    {P0 Q0 Pu Ru Qu : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {m r : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (hL : L = P0 ++ m :: Q0)
    (hLu : L = Pu ++ Ru ++ Qu) (hmR : m ∉ Ru) (hr : r ∈ Ru) (hyr : m.2.2 ∈ r.1) :
    Q0 = Ru ++ Qu ∧ Pu = P0 ++ [m] := by
  have hmL : m ∈ L := by rw [hL]; simp
  have he := isSomeVine_ends (hvineM m hmL)
  have hmL' : m ∈ Pu ++ Ru ++ Qu := hLu ▸ hmL
  rcases List.mem_append.mp hmL' with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨Pa, Pb, rfl⟩ := List.append_of_mem hm
      cases Pb with
      | nil =>
        have h2 : P0 ++ m :: Q0 = Pa ++ m :: (Ru ++ Qu) := by rw [← hL, hLu]; simp
        obtain ⟨h1, h3⟩ := app_cons_inj_of_nodupMK (hL ▸ hs.nodupMK) h2
        exact ⟨h3, by rw [h1]⟩
      | cons s Pc =>
        exfalso
        have hs' : Spine N ((Pa ++ [m]) ++ s :: (Pc ++ Ru ++ Qu)) S a b := by rw [hLu] at hs; simpa using hs
        exact Finset.disjoint_left.mp (hs'.sepMK (by simp) (by simp [hr])) he.2.1 hyr
    · exact absurd hm hmR
  · exfalso
    obtain ⟨Qa, Qb, rfl⟩ := List.append_of_mem hm
    cases Qa with
    | nil =>
      have hs' : Spine N ((Pu ++ Ru) ++ m :: Qb) S a b := by rw [hLu] at hs; simpa using hs
      exact he.2.2 (hs'.joint_leftMK (List.mem_append_right _ hr) hyr he.2.1).symm
    | cons s Qc =>
      have hs' : Spine N ((Pu ++ Ru) ++ s :: (Qc ++ m :: Qb)) S a b := by rw [hLu] at hs; simpa using hs
      exact Finset.disjoint_left.mp (hs'.sepMK (by simp [hr]) (by simp)) hyr he.2.1

/-- **The local form of a survivor**: its member `m` of the spine, flanked by the run at each joint (or nothing,
when no run contains that joint); a run meets `m` only through these two runs. -/
theorem MarkedGroupUnits.surv_localMK (U : MarkedGroupUnits G S Mk) (hs : Spine N L S a b)
    (hvineM : ∀ t ∈ L, IsSomeVine G.molecule t.1 t.2.1 t.2.2)
    (hingr : ∀ t ∈ L, IsIngredient G.molecule S t.1)
    (hmemb : ∀ T, IsIngredient G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ U.surv) :
    ∃ P RL m RR Q, L = P ++ RL ++ m :: (RR ++ Q) ∧ m.1 = t.1 ∧ ¬ UnmMemMK G Mk m ∧
      (∀ r ∈ RL, UnmMemMK G Mk r) ∧ (∀ r ∈ RR, UnmMemMK G Mk r) ∧
      (RL = [] ∧ (∀ u ∈ U.runs, m.2.1 ∉ u.atoms) ∨
        RL ≠ [] ∧ ∃ u ∈ U.runs, m.2.1 ∈ u.atoms ∧ ∀ v, v ∈ u.atoms ↔ ∃ r ∈ RL, v ∈ r.1) ∧
      (RR = [] ∧ (∀ u ∈ U.runs, m.2.2 ∉ u.atoms) ∨
        RR ≠ [] ∧ ∃ u ∈ U.runs, m.2.2 ∈ u.atoms ∧ ∀ v, v ∈ u.atoms ↔ ∃ r ∈ RR, v ∈ r.1) ∧
      ∀ u ∈ U.runs, ∀ v ∈ u.atoms, v ∈ m.1 → (∃ r ∈ RL, v ∈ r.1) ∨ (∃ r ∈ RR, v ∈ r.1) := by
  classical
  obtain ⟨-, hit, hmk⟩ := U.surv_spec t ht
  obtain ⟨m, hmL, hm1⟩ : ∃ m ∈ L, m.1 = t.1 := by
    obtain ⟨p, q, h | h⟩ := hmemb _ hit
    · exact ⟨_, h, rfl⟩
    · exact ⟨_, h, rfl⟩
  have hmg : ¬ UnmMemMK G Mk m := by
    rintro ⟨c, hcV, hcMk, hcm⟩
    rcases hmk with ⟨c', hc'Mk, -, hc't⟩ | hno
    · exact hcMk ((clvine_eq_of_atomsMK (hcm.trans (hm1.trans hc't.symm))) ▸ hc'Mk)
    · exact hno c hcV (hcm.trans hm1)
  obtain ⟨P0, Q0, hL⟩ := List.append_of_mem hmL
  have hcanon := fun u (hu : u ∈ U.runs) => U.run_canonMK hs hvineM hingr hmemb hu
  -- the left side
  obtain ⟨P, RL, hP0, hRLg, hleft⟩ : ∃ P RL, P0 = P ++ RL ∧ (∀ r ∈ RL, UnmMemMK G Mk r) ∧ (RL = [] ∧ (∀ u ∈ U.runs, m.2.1 ∉ u.atoms) ∨
      RL ≠ [] ∧ ∃ u ∈ U.runs, m.2.1 ∈ u.atoms ∧ ∀ v, v ∈ u.atoms ↔ ∃ r ∈ RL, v ∈ r.1) := by
    by_cases hx : ∃ u ∈ U.runs, m.2.1 ∈ u.atoms
    · obtain ⟨u, hu, hxu⟩ := hx
      obtain ⟨Pu, Ru, Qu, hLu, hRu, hRg, hiff, -, -⟩ := hcanon u hu
      obtain ⟨r, hr, hxr⟩ := (hiff _).mp hxu
      have hmR : m ∉ Ru := fun h => hmg (hRg m h)
      obtain ⟨h1, -⟩ := run_adj_leftMK hs hvineM hL hLu hmR hr hxr
      exact ⟨Pu, Ru, h1, hRg, Or.inr ⟨hRu, u, hu, hxu, hiff⟩⟩
    · push Not at hx
      exact ⟨P0, [], by simp, by simp, Or.inl ⟨rfl, hx⟩⟩
  -- the right side
  obtain ⟨RR, Q, hQ0, hRRg, hright⟩ : ∃ RR Q, Q0 = RR ++ Q ∧ (∀ r ∈ RR, UnmMemMK G Mk r) ∧ (RR = [] ∧ (∀ u ∈ U.runs, m.2.2 ∉ u.atoms) ∨
      RR ≠ [] ∧ ∃ u ∈ U.runs, m.2.2 ∈ u.atoms ∧ ∀ v, v ∈ u.atoms ↔ ∃ r ∈ RR, v ∈ r.1) := by
    by_cases hy : ∃ u ∈ U.runs, m.2.2 ∈ u.atoms
    · obtain ⟨u, hu, hyu⟩ := hy
      obtain ⟨Pu, Ru, Qu, hLu, hRu, hRg, hiff, -, -⟩ := hcanon u hu
      obtain ⟨r, hr, hyr⟩ := (hiff _).mp hyu
      have hmR : m ∉ Ru := fun h => hmg (hRg m h)
      obtain ⟨h1, -⟩ := run_adj_rightMK hs hvineM hL hLu hmR hr hyr
      exact ⟨Ru, Qu, h1, hRg, Or.inr ⟨hRu, u, hu, hyu, hiff⟩⟩
    · push Not at hy
      exact ⟨[], Q0, by simp, by simp, Or.inl ⟨rfl, hy⟩⟩
  refine ⟨P, RL, m, RR, Q, by rw [hL, hP0, hQ0], hm1, hmg, hRLg, hRRg, hleft, hright, ?_⟩
  intro u hu v hvu hvm
  obtain ⟨Pu, Ru, Qu, hLu, hRu, hRg, hiff, -, -⟩ := hcanon u hu
  obtain ⟨r, hr, hvr⟩ := (hiff v).mp hvu
  have hrm : r ≠ m := fun h => hmg (h ▸ hRg r hr)
  have hrL : r ∈ P0 ++ m :: Q0 := by rw [← hL, hLu]; simp [hr]
  have hs' : Spine N (P0 ++ m :: Q0) S a b := hL ▸ hs
  have hdj : ∀ u'' ∈ U.runs, u ≠ u'' → Disjoint u.atoms u''.atoms := fun u'' hu'' huu =>
    pairwise_symm_forallMK (fun x y h => Disjoint.symm h) U.disj hu hu'' huu
  rcases List.mem_append.mp hrL with hrP | hrQ
  · have hv1 : v = m.2.1 := hs'.joint_leftMK hrP hvr hvm
    left
    rcases hleft with ⟨-, hno⟩ | ⟨-, u'', hu'', hxu'', hiff''⟩
    · exact absurd (hv1 ▸ hvu) (hno u hu)
    · by_cases huu : u = u''
      · subst huu
        exact (hiff'' v).mp hvu
      · exact absurd (hdj u'' hu'' huu) (Finset.not_disjoint_iff.mpr ⟨v, hvu, hv1 ▸ hxu''⟩)
  · rcases List.mem_cons.mp hrQ with h | hrQ
    · exact absurd h hrm
    · have hv2 : v = m.2.2 := hs'.joint_rightMK hrQ hvr hvm
      right
      rcases hright with ⟨-, hno⟩ | ⟨-, u'', hu'', hyu'', hiff''⟩
      · exact absurd (hv2 ▸ hvu) (hno u hu)
      · by_cases huu : u = u''
        · subst huu
          exact (hiff'' v).mp hvu
        · exact absurd (hdj u'' hu'' huu) (Finset.not_disjoint_iff.mpr ⟨v, hvu, hv2 ▸ hyu''⟩)

end canon

end WaveTurbulence.RedSplice
