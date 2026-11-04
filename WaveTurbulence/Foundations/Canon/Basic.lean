/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.Lemmas

/-!
# Canonical layered gardens — basic facts (packet D3 CANON, pre-freeze)

Forest order facts (antisymmetry and comparability of ancestors, parents), parity (a subtree has an
odd number of leaves; a completely paired set of leaves is even), and the notions relative to a set
`S` of pairwise incomparable nodes at level `q`: the parent layer `rpl` (`q` at `S`), the criterion
`RelCrit`, the attachment nodes `relAttach` and their linking relation `RelLinked`. At `S = roots`
these are `parentLayer`, `CanonCriterion`, `attachNodes`, `AttachLinkedOn`.
-/

@[expose] public section

open Finset

namespace WaveTurbulence.Canon

open TTree

/-! ### Forest order -/

section Forest

variable {w : ℕ} {tree : Fin w → TTree}

theorem isDesc_antisymm {a b : GNode tree} (h₁ : a.IsDesc b) (h₂ : b.IsDesc a) : a = b :=
  Subtype.ext (Prod.ext h₁.1 (h₁.2.eq_of_length (le_antisymm h₁.2.length_le h₂.2.length_le)))

theorem isDesc_total {a b c : GNode tree} (ha : a.IsDesc c) (hb : b.IsDesc c) :
    a.IsDesc b ∨ b.IsDesc a := by
  rcases List.prefix_or_prefix_of_prefix ha.2 hb.2 with h | h
  · exact Or.inl ⟨ha.1.trans hb.1.symm, h⟩
  · exact Or.inr ⟨hb.1.trans ha.1.symm, h⟩

/-- The parent of a node (the node itself for a root). -/
def par (a : GNode tree) : GNode tree := ⟨(a.1.1, a.1.2.dropLast), TTree.dropLast_mem_nodes _ a.2⟩

theorem par_isDesc (a : GNode tree) : (par a).IsDesc a := ⟨rfl, List.dropLast_prefix _⟩

theorem prefix_dropLast_of_prefix_of_ne {l₁ l₂ : List (Fin 3)} (h : l₁ <+: l₂) (hne : l₁ ≠ l₂) :
    l₁ <+: l₂.dropLast := by
  obtain ⟨t, rfl⟩ := h
  have ht : t ≠ [] := by
    rintro rfl
    simp at hne
  rw [List.dropLast_append_of_ne_nil ht]
  exact List.prefix_append _ _

/-- A strict ancestor of `a` is an ancestor of the parent of `a`. -/
theorem isDesc_par_of_isDesc_of_ne {u a : GNode tree} (h : u.IsDesc a) (hne : u ≠ a) :
    u.IsDesc (par a) := by
  refine ⟨h.1, prefix_dropLast_of_prefix_of_ne h.2 fun h' => hne ?_⟩
  exact Subtype.ext (Prod.ext h.1 h')

theorem path_ne_nil_of_isDesc_of_ne {u a : GNode tree} (h : u.IsDesc a) (hne : u ≠ a) :
    a.1.2 ≠ [] := by
  intro ha
  apply hne
  have : u.1.2 = [] := List.prefix_nil.1 (ha ▸ h.2)
  exact Subtype.ext (Prod.ext h.1 (this.trans ha.symm))

theorem par_ne {a : GNode tree} (ha : a.1.2 ≠ []) : par a ≠ a := by
  intro h
  have h1 : (par a).1.2.length = a.1.2.length := by rw [h]
  simp only [par, List.length_dropLast] at h1
  have : 0 < a.1.2.length := List.length_pos_iff.2 ha
  omega

theorem length_par_lt {a : GNode tree} (ha : a.1.2 ≠ []) : (par a).1.2.length < a.1.2.length := by
  simp only [par, List.length_dropLast]
  have : 0 < a.1.2.length := List.length_pos_iff.2 ha
  omega

/-! ### Parity -/

/-- A subtree has an odd number of leaves (sum rule modulo 2). -/
theorem odd_card_leavesBelow (a : GNode tree) : Odd a.leavesBelow.card := by
  have hs := sum_rule (fun _ => (1 : ℤˣ)) (fun _ => (1 : ZMod 2)) (fun _ => by ring) a
  have hone : ∀ u : ℤˣ, ((u : ℤ) • (1 : ZMod 2)) = 1 := by
    intro u
    rcases Int.units_eq_one_or u with h | h
    · simp [h]
    · rw [h]
      decide
  simp only [hone, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  exact (ZMod.natCast_eq_one_iff_odd).1 hs.symm

/-- Leaves below incomparable nodes are disjoint. -/
theorem disjoint_leavesBelow {a b : GNode tree} (hinc : a.Incomparable b) :
    Disjoint a.leavesBelow b.leavesBelow := by
  rw [Finset.disjoint_left]
  intro ℓ ha hb
  simp only [GNode.leavesBelow, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  rcases isDesc_total ha hb with h | h
  · exact hinc.1 h
  · exact hinc.2 h

end Forest

section Paired

variable {w : ℕ} (G : Garden w)

/-- A completely paired set of leaves has an even number of elements. -/
theorem even_card_of_completelyPaired :
    ∀ (n : ℕ) (T : Finset (GLeaf G.tree)), T.card = n → G.CompletelyPaired T → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hT hP
    rcases T.eq_empty_or_nonempty with rfl | ⟨ℓ, hℓ⟩
    · simp at hT
      subst hT
      exact ⟨0, rfl⟩
    · obtain ⟨hne, hmem⟩ := hP ℓ hℓ
      set T' := (T.erase ℓ).erase (G.pair ℓ) with hT'
      have hmem' : G.pair ℓ ∈ T.erase ℓ := Finset.mem_erase.2 ⟨hne, hmem⟩
      have hcard : T'.card + 2 = n := by
        rw [hT', Finset.card_erase_of_mem hmem', Finset.card_erase_of_mem hℓ, ← hT]
        have : 2 ≤ T.card := by
          have := Finset.card_le_card (Finset.insert_subset hℓ (Finset.singleton_subset_iff.2 hmem))
          rwa [Finset.card_pair hne.symm] at this
        omega
      have hP' : G.CompletelyPaired T' := by
        intro x hx
        simp only [hT', Finset.mem_erase] at hx
        obtain ⟨hx1, hx2, hx3⟩ := hx
        obtain ⟨hpx, hpxT⟩ := hP x hx3
        refine ⟨hpx, ?_⟩
        simp only [hT', Finset.mem_erase]
        refine ⟨fun h => hx2 ?_, fun h => hx1 ?_, hpxT⟩
        · rw [← G.pair_pair x, h, G.pair_pair]
        · rw [← G.pair_pair x, h]
      have := ih T'.card (by omega) T' rfl hP'
      rw [← hcard]
      exact this.add even_two

end Paired

/-! ### Notions relative to a set of incomparable nodes -/

namespace Rel

variable {w : ℕ} (LG : LayeredGarden w)

/-- The nodes of `S` are pairwise incomparable. -/
def Antichain (S : Finset (GNode LG.garden.tree)) : Prop :=
  ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → s.Incomparable s'

/-- The parent layer relative to `S` at level `q`: `q` at the nodes of `S`, the layer of the parent
elsewhere. -/
def rpl (S : Finset (GNode LG.garden.tree)) (q : ℕ) (a : GNode LG.garden.tree) : ℕ :=
  if a ∈ S then q else LG.parentLayer q a

/-- **The canonicity criterion relative to `S` at level `q`** (T Prop `canonequiv` (i)–(ii) for the
sub-garden rooted at `S`, root parent layers read as `q`). -/
def RelCrit (S : Finset (GNode LG.garden.tree)) (q : ℕ) : Prop :=
  (∀ a, LG.BelowSet S a → LG.layer a ≤ q) ∧
    ∀ a a', LG.BelowSet S a → LG.BelowSet S a' → a.Incomparable a' →
      LG.garden.CompletelyPaired (a.leavesBelow ∪ a'.leavesBelow) →
        min (rpl LG S q a) (rpl LG S q a') ≤ max (LG.layer a) (LG.layer a')

/-- The attachment nodes relative to `S` at level `q`: below `S`, layer `< q`, relative parent layer
`q`. -/
noncomputable def relAttach (S : Finset (GNode LG.garden.tree)) (q : ℕ) :
    Finset (GNode LG.garden.tree) := by
  classical
  exact Finset.univ.filter fun a => LG.BelowSet S a ∧ LG.layer a < q ∧ rpl LG S q a = q

theorem mem_relAttach {S : Finset (GNode LG.garden.tree)} {q : ℕ} {a : GNode LG.garden.tree} :
    a ∈ relAttach LG S q ↔ LG.BelowSet S a ∧ LG.layer a < q ∧ rpl LG S q a = q := by
  classical
  simp [relAttach]

/-- Linking of relative attachment nodes. -/
def RelLinked (S : Finset (GNode LG.garden.tree)) (q : ℕ) (u u' : GNode LG.garden.tree) : Prop :=
  u ∈ relAttach LG S q ∧ u' ∈ relAttach LG S q ∧ LG.AttachLinked u u'

variable {LG}

theorem eq_of_isDesc_of_antichain {S : Finset (GNode LG.garden.tree)} (hS : Antichain LG S)
    {s s' : GNode LG.garden.tree} (hs : s ∈ S) (hs' : s' ∈ S) (h : s.IsDesc s') : s = s' := by
  by_contra hne
  exact (hS s hs s' hs' hne).1 h

theorem belowSet_of_isDesc {S : Finset (GNode LG.garden.tree)} {a c : GNode LG.garden.tree}
    (ha : LG.BelowSet S a) (h : a.IsDesc c) : LG.BelowSet S c := by
  obtain ⟨s, hs, hsa⟩ := ha
  exact ⟨s, hs, hsa.trans h⟩

/-- Below `S` and not in `S`: the parent is below `S` and is the relative parent. -/
theorem below_par {S : Finset (GNode LG.garden.tree)} (_hS : Antichain LG S) {q : ℕ}
    {a : GNode LG.garden.tree} (ha : LG.BelowSet S a) (haS : a ∉ S) :
    a.1.2 ≠ [] ∧ LG.BelowSet S (par a) ∧ rpl LG S q a = LG.layer (par a) := by
  obtain ⟨s, hs, hsa⟩ := ha
  have hne : s ≠ a := fun h => haS (h ▸ hs)
  have hpath := path_ne_nil_of_isDesc_of_ne hsa hne
  refine ⟨hpath, ⟨s, hs, isDesc_par_of_isDesc_of_ne hsa hne⟩, ?_⟩
  simp only [rpl, haS, ↓reduceIte, LayeredGarden.parentLayer, hpath]
  rfl

/-- A node below `S` that is an ancestor of a node of `S` is that node. -/
theorem eq_of_below_isDesc_mem {S : Finset (GNode LG.garden.tree)} (hS : Antichain LG S)
    {a s : GNode LG.garden.tree} (ha : LG.BelowSet S a) (hs : s ∈ S) (h : a.IsDesc s) : a = s := by
  obtain ⟨s', hs', hs'a⟩ := ha
  have := eq_of_isDesc_of_antichain hS hs' hs (hs'a.trans h)
  subst this
  exact isDesc_antisymm h hs'a

/-- **Walk-up**: a node below `S` of layer `< q` (all layers below `S` being `≤ q`) lies below a
relative attachment node. -/
theorem exists_relAttach_isDesc {S : Finset (GNode LG.garden.tree)} (hS : Antichain LG S) {q : ℕ}
    (hle : ∀ a, LG.BelowSet S a → LG.layer a ≤ q) {a : GNode LG.garden.tree}
    (ha : LG.BelowSet S a) (hlt : LG.layer a < q) : ∃ u ∈ relAttach LG S q, u.IsDesc a := by
  classical
  set A := Finset.univ.filter fun c : GNode LG.garden.tree =>
    c.IsDesc a ∧ LG.BelowSet S c ∧ LG.layer c < q with hA
  have hAne : A.Nonempty := ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, GNode.isDesc_refl a, ha, hlt⟩⟩
  obtain ⟨c, hcA, hmin⟩ := A.exists_min_image (fun c => c.1.2.length) hAne
  simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hcA
  obtain ⟨hca, hcS, hcq⟩ := hcA
  refine ⟨c, (mem_relAttach LG).2 ⟨hcS, hcq, ?_⟩, hca⟩
  by_cases hcmem : c ∈ S
  · simp [rpl, hcmem]
  · obtain ⟨hpath, hparS, hrpl⟩ := below_par hS hcS hcmem (q := q)
    rw [hrpl]
    refine le_antisymm (hle _ hparS) (not_lt.1 fun hlt' => ?_)
    have := hmin (par c) (by
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(par_isDesc c).trans hca, hparS, hlt'⟩)
    exact absurd this (not_le.2 (length_par_lt hpath))

/-- Relative attachment nodes are pairwise incomparable. -/
theorem eq_of_relAttach_isDesc {S : Finset (GNode LG.garden.tree)} (hS : Antichain LG S) {q : ℕ}
    {u u' : GNode LG.garden.tree} (hu : u ∈ relAttach LG S q) (hu' : u' ∈ relAttach LG S q)
    (h : u.IsDesc u') : u = u' := by
  by_contra hne
  obtain ⟨huS, huq, -⟩ := (mem_relAttach LG).1 hu
  obtain ⟨hu'S, -, hu'r⟩ := (mem_relAttach LG).1 hu'
  have hu'notS : u' ∉ S := by
    intro hu'mem
    exact hne (eq_of_below_isDesc_mem hS huS hu'mem h)
  obtain ⟨-, -, hrpl⟩ := below_par hS hu'S hu'notS (q := q)
  have hle := LG.layer_le_of_isDesc (isDesc_par_of_isDesc_of_ne h hne)
  omega

end Rel

end WaveTurbulence.Canon
