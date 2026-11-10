/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL19
public import WaveTurbulence.Foundations.Spine.SourceVineData
/-! **G3-LOWDEG (R48), part 20: invariance of the group predicates under a dart embedding that is onto the group darts.**
`GEmb M1 M2 ι S`: `ι : D1 → D2` is an injective, `atom/mate/out`-compatible embedding such that every dart of `M2` with both ends in
`S` is in the range (cover).  Then `degIn/outIn/inIn`, `GroupConnected`, `groupBonds`, `IsBlock`, `IsVine`, `IsSomeVine`, `Chain`, `IsVC`
agree on `S` (iff).  Used for `M.unloop ↪ M` (`S` without loop atoms) and `eraseBond (M.unloop) ↪ eraseBond M`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine
variable {V : Type*} [DecidableEq V] {D1 D2 : Type*} [Fintype D1] [DecidableEq D1] [Fintype D2] [DecidableEq D2]

structure GEmb (M1 : Molecule V D1) (M2 : Molecule V D2) (ι : D1 → D2) (S : Finset V) : Prop where
  inj : Function.Injective ι
  atom : ∀ x, M2.atom (ι x) = M1.atom x
  mate : ∀ x, ι (M1.mate x) = M2.mate (ι x)
  out : ∀ x, M2.out (ι x) = M1.out x
  cover : ∀ z, M2.InGroup S z → ∃ x, ι x = z

namespace GEmb
variable {M1 : Molecule V D1} {M2 : Molecule V D2} {ι : D1 → D2} {S : Finset V} (G : GEmb M1 M2 ι S)
include G

theorem inGroup_iff (T : Finset V) (x : D1) : M2.InGroup T (ι x) ↔ M1.InGroup T x := by
  unfold Molecule.InGroup
  rw [G.atom, ← G.mate, G.atom]

theorem mono {T : Finset V} (hT : T ⊆ S) : GEmb M1 M2 ι T :=
  ⟨G.inj, G.atom, G.mate, G.out, fun z hz => G.cover z ⟨hT hz.1, hT hz.2⟩⟩

theorem card_filter (v : V) (Q : D2 → Prop) [DecidablePred Q] :
    ((M2.dartsAt v).filter (fun z => M2.InGroup S z ∧ Q z)).card =
      ((M1.dartsAt v).filter (fun x => M1.InGroup S x ∧ Q (ι x))).card := by
  symm
  refine Finset.card_bij (fun x _ => ι x) ?_ (fun x _ y _ e => G.inj e) ?_
  · intro x hx
    have := Finset.mem_filter.1 hx
    refine Finset.mem_filter.2 ⟨(mem_dartsAt' M2 v _).2 (by rw [G.atom]; exact (mem_dartsAt' M1 v x).1 this.1),
      (G.inGroup_iff S x).2 this.2.1, this.2.2⟩
  · intro z hz
    have := Finset.mem_filter.1 hz
    obtain ⟨x, rfl⟩ := G.cover z this.2.1
    refine ⟨x, Finset.mem_filter.2 ⟨(mem_dartsAt' M1 v x).2 (by rw [← G.atom]; exact (mem_dartsAt' M2 v _).1 this.1),
      (G.inGroup_iff S x).1 this.2.1, this.2.2⟩, rfl⟩

theorem degIn_eq (v : V) : M2.degIn S v = M1.degIn S v := by
  unfold Molecule.degIn
  have := G.card_filter v (fun _ => True)
  simpa using this

theorem outIn_eq (v : V) : M2.outIn S v = M1.outIn S v := by
  unfold Molecule.outIn
  have := G.card_filter v (fun z => M2.out z = true)
  simpa only [G.out] using this

theorem inIn_eq (v : V) : M2.inIn S v = M1.inIn S v := by
  unfold Molecule.inIn
  have := G.card_filter v (fun z => M2.out z = false)
  simpa only [G.out] using this

theorem groupBonds_eq : M2.groupBonds S = M1.groupBonds S := by
  unfold Molecule.groupBonds
  have hf : (Finset.univ.filter fun z : D2 => M2.out z = true ∧ M2.InGroup S z) =
      (Finset.univ.filter fun x : D1 => M1.out x = true ∧ M1.InGroup S x).image ι := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨x, rfl⟩ := G.cover z h2
      exact ⟨x, ⟨by rw [← G.out]; exact h1, (G.inGroup_iff S x).1 h2⟩, rfl⟩
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      exact ⟨by rw [G.out]; exact h1, (G.inGroup_iff S x).2 h2⟩
  rw [hf, Finset.image_val_of_injOn (G.inj.injOn), Multiset.map_map]
  refine Multiset.map_congr rfl (fun x _ => ?_)
  simp [Molecule.ends, G.atom, ← G.mate]

theorem connected_iff : M2.GroupConnected S ↔ M1.GroupConnected S := by
  have rel : ∀ a b, (∃ x, M2.InGroup S x ∧ M2.atom x = a ∧ M2.atom (M2.mate x) = b) ↔
      (∃ x, M1.InGroup S x ∧ M1.atom x = a ∧ M1.atom (M1.mate x) = b) := by
    intro a b
    constructor
    · rintro ⟨z, hz, h1, h2⟩
      obtain ⟨x, rfl⟩ := G.cover z hz
      exact ⟨x, (G.inGroup_iff S x).1 hz, by rw [← G.atom]; exact h1, by rw [← G.atom, G.mate]; exact h2⟩
    · rintro ⟨x, hx, h1, h2⟩
      exact ⟨ι x, (G.inGroup_iff S x).2 hx, by rw [G.atom]; exact h1, by rw [← G.mate, G.atom]; exact h2⟩
  unfold Molecule.GroupConnected
  have key1 : ∀ a b, Relation.EqvGen (fun a b => ∃ x, M2.InGroup S x ∧ M2.atom x = a ∧ M2.atom (M2.mate x) = b) a b →
      Relation.EqvGen (fun a b => ∃ x, M1.InGroup S x ∧ M1.atom x = a ∧ M1.atom (M1.mate x) = b) a b := by
    intro a b h
    induction h with
    | rel a b h => exact Relation.EqvGen.rel _ _ ((rel a b).1 h)
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have key2 : ∀ a b, Relation.EqvGen (fun a b => ∃ x, M1.InGroup S x ∧ M1.atom x = a ∧ M1.atom (M1.mate x) = b) a b →
      Relation.EqvGen (fun a b => ∃ x, M2.InGroup S x ∧ M2.atom x = a ∧ M2.atom (M2.mate x) = b) a b := by
    intro a b h
    induction h with
    | rel a b h => exact Relation.EqvGen.rel _ _ ((rel a b).2 h)
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  constructor
  · intro h u hu v hv; exact key1 u v (h u hu v hv)
  · intro h u hu v hv; exact key2 u v (h u hu v hv)

theorem isBlock_iff (hat : M1.atoms = M2.atoms) {j₁ j₂ : V} : M2.IsBlock S j₁ j₂ ↔ M1.IsBlock S j₁ j₂ := by
  unfold Molecule.IsBlock
  rw [hat, G.outIn_eq, G.outIn_eq, G.inIn_eq, G.inIn_eq, G.connected_iff]
  simp only [G.degIn_eq]

theorem isVine_iff (hat : M1.atoms = M2.atoms) {X : VineType} {j₁ j₂ : V} :
    M2.IsVine X S j₁ j₂ ↔ M1.IsVine X S j₁ j₂ := by
  unfold Molecule.IsVine
  rw [G.isBlock_iff hat, G.groupBonds_eq]

theorem isSomeVine_iff (hat : M1.atoms = M2.atoms) {a b : V} : IsSomeVine M2 S a b ↔ IsSomeVine M1 S a b := by
  unfold IsSomeVine
  simp only [G.isVine_iff hat]

theorem chain_iff (hat : M1.atoms = M2.atoms) {S' : Finset V} (hsub : S' ⊆ S) {a b : V} {n : ℕ} :
    Chain M2 S' a b n ↔ Chain M1 S' a b n := by
  constructor
  · intro h
    revert hsub
    induction h with
    | single h => intro hs; exact Chain.single (((G.mono hs).isSomeVine_iff hat).1 h)
    | append hc hv hinter hne ih =>
      rename_i S₁ T₁ a₁ b₁ c₁ n₁
      intro hs
      exact Chain.append (ih (fun x hx => hs (Finset.mem_union_left _ hx)))
        (((G.mono (fun x hx => hs (Finset.mem_union_right _ hx))).isSomeVine_iff hat).1 hv) hinter hne
  · intro h
    revert hsub
    induction h with
    | single h => intro hs; exact Chain.single (((G.mono hs).isSomeVine_iff hat).2 h)
    | append hc hv hinter hne ih =>
      rename_i S₁ T₁ a₁ b₁ c₁ n₁
      intro hs
      exact Chain.append (ih (fun x hx => hs (Finset.mem_union_left _ hx)))
        (((G.mono (fun x hx => hs (Finset.mem_union_right _ hx))).isSomeVine_iff hat).2 hv) hinter hne

theorem isVC_iff (hat : M1.atoms = M2.atoms) {a b : V} : IsVC M2 S a b ↔ IsVC M1 S a b := by
  unfold IsVC
  rw [G.isBlock_iff hat]
  simp only [G.chain_iff hat (Finset.Subset.refl S)]

theorem isDV_of (hat : M1.atoms = M2.atoms) {a b : V} (h : IsDV M2 S a b) : IsDV M1 S a b := by
  obtain ⟨A, B, hA, hB, hAB, rfl⟩ := h
  exact ⟨A, B, ((G.mono (Finset.subset_union_left)).isVine_iff hat).1 hA,
    ((G.mono (Finset.subset_union_right)).isVine_iff hat).1 hB, hAB, rfl⟩

end GEmb
end WaveTurbulence.FinalCountG3
