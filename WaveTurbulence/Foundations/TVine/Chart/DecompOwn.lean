/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.GlueChart

/-!
# Ownership of a cell decomposition by counting

`PreDecomp` is a cell decomposition without the ownership fields, together with the count
`Σ_c (nB c − 2) + 2 = #bonds` (every cell has exactly two input bonds; `b` owns its two bonds). Every bond lies at
an atom of `S`, hence is a local bond of a cell or of a joint embedding (completeness), and every input bond is an
output bond of the parent (wiring, induction on rank); so the owned local bonds cover all bonds but `b`'s, and by the
count they do so injectively. This gives the ownership (`PreDecomp.toDecomp`).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

/-- **A cell decomposition without ownership**, with the bond count. -/
structure PreDecomp {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D) (S : Finset V) (a b : V) where
  m : ℕ
  k : ℕ
  nB : Cell m k → ℕ
  cfg : (c : Cell m k) → LocalChart (nAof c) (nCof c) (nB c)
  valid : ∀ c, (cfg c).Valid
  pairOK : ∀ j, PairOK (cfg (.inl j))
  coreOK : CoreOK (cfg Cell.core)
  emb : (c : Cell m k) → LocEmb (cfg c).graph M S
  jb : LocEmb jointGraph M S
  ja : LocEmb jointGraph M S
  jb_atom : jb.atom 0 = b
  ja_atom : ja.atom 0 = a
  rank : Cell m k → ℕ
  parent : Cell m k → Option (Cell m k × Bool)
  parent_rank : ∀ c s w, parent c = some (s, w) → rank s < rank c
  wire_base : ∀ c, parent c = none → (emb c).bond (cfg c).eO = jb.bond 0 ∧
    (emb c).bond (cfg c).eI = jb.bond 1 ∧ (cfg c).locR (cfg c).eO = 1
  wire : ∀ c s w, parent c = some (s, w) → ∃ p, outPair (cfg s) w = some p ∧
    (emb c).bond (cfg c).eO = (emb s).bond p.1 ∧ (emb c).bond (cfg c).eI = (emb s).bond p.2 ∧
    (cfg c).locR (cfg c).eO = (cfg s).locR p.1 - (cfg s).locR p.2
  final : Cell m k
  final_out : ∃ p, (cfg final).outM = some p ∧ ja.bond 0 = (emb final).bond p.2 ∧
    ja.bond 1 = (emb final).bond p.1 ∧ (cfg final).locR p.1 - (cfg final).locR p.2 = 1
  atom_mem : ∀ c u, (emb c).atom u ∈ S
  cover : ∀ v ∈ S, v = a ∨ v = b ∨ ∃ c u, (emb c).atom u = v
  atom_inj : ∀ c c' u u', (emb c).atom u = (emb c').atom u' →
    (⟨c, u⟩ : Σ c : Cell m k, Fin (nAof c)) = ⟨c', u'⟩
  atom_ne_a : ∀ c u, (emb c).atom u ≠ a
  atom_ne_b : ∀ c u, (emb c).atom u ≠ b
  extra : ∀ c x, (emb c).bond ((cfg c).X₁ x) ≠ (emb c).bond ((cfg c).X₂ x) ∧
    ∃ Y ⊆ S, ∀ e, Crosses Y e ↔ e = (emb c).bond ((cfg c).X₁ x) ∨ e = (emb c).bond ((cfg c).X₂ x)
  junction : Option (Fin m)
  junction_mu : ∀ j, (cfg (.inl j)).mu = if junction = some j then 1 else 2
  count : (∑ c, (nB c - 2)) + 2 = Fintype.card (Bond M S)

namespace PreDecomp

variable {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D} {S : Finset V} {a b : V}
variable (P : PreDecomp M S a b)

/-- The owned local bonds. -/
def Owned (x : Σ c : Cell P.m P.k, Fin (P.nB c)) : Prop := ¬ (P.cfg x.1).IsInput x.2

instance (x : Σ c : Cell P.m P.k, Fin (P.nB c)) : Decidable (P.Owned x) := by unfold Owned; infer_instance

/-- The bond of an owned local bond. -/
def ownedBond (x : Σ c : Cell P.m P.k, Fin (P.nB c)) : Bond M S := (P.emb x.1).bond x.2

theorem jb_ne : P.jb.bond 0 ≠ P.jb.bond 1 := fun h => by
  have := P.jb.bond_inj h; exact absurd this (by decide)

/-- Every local bond is owned or one of `b`'s bonds. -/
theorem local_owned (c : Cell P.m P.k) (l : Fin (P.nB c)) :
    (∃ x, P.Owned x ∧ P.ownedBond x = (P.emb c).bond l) ∨ (P.emb c).bond l = P.jb.bond 0 ∨
      (P.emb c).bond l = P.jb.bond 1 := by
  induction hr : P.rank c using Nat.strong_induction_on generalizing c l with
  | _ N ih =>
  by_cases hl : (P.cfg c).IsInput l
  · rcases hl with rfl | rfl
    · cases hp : P.parent c with
      | none => right; left; exact (P.wire_base c hp).1
      | some sw =>
        obtain ⟨s, w⟩ := sw
        obtain ⟨p, -, h1, -, -⟩ := P.wire c s w hp
        rw [h1]; exact ih _ (hr ▸ P.parent_rank c s w hp) s p.1 rfl
    · cases hp : P.parent c with
      | none => right; right; exact (P.wire_base c hp).2.1
      | some sw =>
        obtain ⟨s, w⟩ := sw
        obtain ⟨p, -, -, h2, -⟩ := P.wire c s w hp
        rw [h2]; exact ih _ (hr ▸ P.parent_rank c s w hp) s p.2 rfl
  · left; exact ⟨⟨c, l⟩, hl, rfl⟩

/-- Every bond is owned or one of `b`'s bonds. -/
theorem all_owned (e : Bond M S) :
    (∃ x, P.Owned x ∧ P.ownedBond x = e) ∨ e = P.jb.bond 0 ∨ e = P.jb.bond 1 := by
  rcases P.cover (tl e) (tl_mem e) with h | h | ⟨c, u, h⟩
  · obtain ⟨l, hl⟩ := P.ja.complete 0 e (Or.inl (h.trans P.ja_atom.symm))
    obtain ⟨p, -, h0, h1, -⟩ := P.final_out
    have hfin : ∃ l', e = (P.emb P.final).bond l' := by
      have hl2 : l = 0 ∨ l = 1 := by
        rcases l with ⟨_ | _ | _, hl'⟩
        · left; rfl
        · right; rfl
        · exfalso; have : _ + 1 + 1 < 2 := hl'; omega
      rcases hl2 with rfl | rfl
      · exact ⟨p.2, by rw [← hl, h0]⟩
      · exact ⟨p.1, by rw [← hl, h1]⟩
    obtain ⟨l', rfl⟩ := hfin
    exact P.local_owned _ l'
  · obtain ⟨l, hl⟩ := P.jb.complete 0 e (Or.inl (h.trans P.jb_atom.symm))
    right
    rcases l with ⟨_ | _ | _, hl'⟩
    · left; exact hl.symm
    · right; exact hl.symm
    · exfalso; have : _ + 1 + 1 < 2 := hl'; omega
  · obtain ⟨l, rfl⟩ := (P.emb c).complete u e (Or.inl h.symm)
    exact P.local_owned c l

theorem card_owned : (univ.filter P.Owned).card = ∑ c, (P.nB c - 2) := by
  classical
  rw [Finset.card_filter, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hne := LocalChart.eO_ne_eI (P.valid c)
  rw [← Finset.card_filter]
  have : (univ.filter fun l : Fin (P.nB c) => P.Owned ⟨c, l⟩) = ({(P.cfg c).eO, (P.cfg c).eI} : Finset _)ᶜ := by
    ext l; simp [Owned, LocalChart.IsInput]
  rw [this, card_compl, Fintype.card_fin, card_pair hne]

/-- **The owned local bonds are exactly the bonds other than `b`'s, injectively.** -/
theorem owned_bij : Set.InjOn P.ownedBond (univ.filter P.Owned : Finset _) ∧
    ∀ x, P.Owned x → P.ownedBond x ≠ P.jb.bond 0 ∧ P.ownedBond x ≠ P.jb.bond 1 := by
  classical
  set Dom := (univ.filter P.Owned : Finset (Σ c : Cell P.m P.k, Fin (P.nB c)))
  set T := (univ : Finset (Bond M S)) \ {P.jb.bond 0, P.jb.bond 1}
  have hT : T ⊆ Dom.image P.ownedBond := by
    intro e he
    simp only [T, mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton, not_or] at he
    rcases P.all_owned e with ⟨x, hx, rfl⟩ | h | h
    · exact mem_image.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, hx⟩, rfl⟩
    · exact absurd h he.1
    · exact absurd h he.2
  have hcT : T.card = Dom.card := by
    rw [card_sdiff, Finset.inter_univ, card_univ, card_pair P.jb_ne, P.card_owned, ← P.count]; omega
  have himg : Dom.image P.ownedBond = T :=
    (Finset.eq_of_subset_of_card_le hT (by rw [hcT]; exact card_image_le)).symm
  have hinj : Set.InjOn P.ownedBond Dom := by
    apply Finset.injOn_of_card_image_eq
    rw [himg, hcT]
  refine ⟨hinj, fun x hx => ?_⟩
  have : P.ownedBond x ∈ T := himg ▸ mem_image.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, hx⟩, rfl⟩
  simp only [T, mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton, not_or] at this
  exact this

open Classical in
/-- The ownership function. -/
noncomputable def own (e : Bond M S) : Option (Σ c : Cell P.m P.k, Fin (P.nB c)) :=
  if h : ∃ x, P.Owned x ∧ P.ownedBond x = e then some h.choose else none

/-- **The cell decomposition.** -/
noncomputable def toDecomp : Decomp M S a b where
  m := P.m
  k := P.k
  nB := P.nB
  cfg := P.cfg
  valid := P.valid
  pairOK := P.pairOK
  coreOK := P.coreOK
  emb := P.emb
  jb := P.jb
  ja := P.ja
  jb_atom := P.jb_atom
  ja_atom := P.ja_atom
  rank := P.rank
  parent := P.parent
  parent_rank := P.parent_rank
  wire_base := P.wire_base
  wire := P.wire
  final := P.final
  final_out := P.final_out
  own := P.own
  own_none := by
    intro e he
    unfold own at he
    split_ifs at he with h
    rcases P.all_owned e with h' | h' | h'
    · exact absurd h' h
    · exact Or.inl h'
    · exact Or.inr h'
  own_some := by
    intro e c l he
    unfold own at he
    split_ifs at he with h
    have hs := h.choose_spec
    rw [Option.some_inj] at he
    rw [he] at hs
    exact ⟨hs.2, hs.1⟩
  own_emb := by
    intro c l hl
    unfold own
    have h : ∃ x, P.Owned x ∧ P.ownedBond x = (P.emb c).bond l := ⟨⟨c, l⟩, hl, rfl⟩
    rw [dite_cond_eq_true (eq_true h)]
    congr 1
    have hs := h.choose_spec
    exact P.owned_bij.1 (Finset.mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, hs.1⟩))
      (Finset.mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, hl⟩)) hs.2
  own_jb := by
    intro i
    unfold own
    rw [dite_cond_eq_false (eq_false ?_)]
    rintro ⟨x, hx, he⟩
    have := P.owned_bij.2 x hx
    rcases i with ⟨_ | _ | _, hi⟩
    · exact this.1 he
    · exact this.2 he
    · exfalso; have : _ + 1 + 1 < 2 := hi; omega
  atom_mem := P.atom_mem
  cover := P.cover
  atom_inj := P.atom_inj
  atom_ne_a := P.atom_ne_a
  atom_ne_b := P.atom_ne_b
  extra := P.extra
  junction := P.junction
  junction_mu := P.junction_mu

theorem toDecomp_cellGroups : P.toDecomp.cellGroups =
    (univ.image fun j : Fin P.m =>
      ({(P.emb (.inl j)).atom ⟨1, by show 1 < 2; omega⟩, (P.emb (.inl j)).atom ⟨0, by show 0 < 2; omega⟩} :
        Finset V)) ∪
    {{(P.emb Cell.core).atom ⟨0, by show 0 < 3; omega⟩, (P.emb Cell.core).atom ⟨1, by show 1 < 3; omega⟩,
      (P.emb Cell.core).atom ⟨2, by show 2 < 3; omega⟩}} := rfl

end PreDecomp

end WaveTurbulence.TVine.Chart
