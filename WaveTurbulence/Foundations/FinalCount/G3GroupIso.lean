/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3AncJoint
public import WaveTurbulence.Foundations.Spine.SourceVineObjects
/-! **FINALCOUNT-G3: transport of atomic groups along a dart embedding** (E10 part 2).  If `ι : D → D'` embeds all
the darts of `M` (every dart of `M` lies in the group `S`) onto exactly the darts of the group `S'` of `M'`, compatibly with
`mate`, `out` and a renaming `φ` of atoms (injective on `S`, `S' = φ '' S`), then `IsBlock`, `groupBonds` and `IsVine`
transfer from `(M, S)` to `(M', S')`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

/-- A dart embedding of the whole molecule `M` onto the group `S'` of `M'`. -/
structure GroupIso (M : Molecule V D) (S : Finset V) (M' : Molecule V D') (S' : Finset V) (φ : V → V) (ι : D → D') :
    Prop where
  atom : ∀ x, M'.atom (ι x) = φ (M.atom x)
  mate : ∀ x, M'.mate (ι x) = ι (M.mate x)
  out : ∀ x, M'.out (ι x) = M.out x
  inj : Function.Injective ι
  grp : ∀ x, M.InGroup S x
  range : ∀ z, M'.InGroup S' z → ∃ x, ι x = z
  φinj : Set.InjOn φ S
  img : S' = S.image φ

namespace GroupIso
variable {M : Molecule V D} {S : Finset V} {M' : Molecule V D'} {S' : Finset V} {φ : V → V} {ι : D → D'}
  (G : GroupIso M S M' S' φ ι)
include G

theorem inGroup (x : D) : M'.InGroup S' (ι x) := by
  have h := G.grp x
  refine ⟨?_, ?_⟩
  · rw [G.atom, G.img]; exact Finset.mem_image_of_mem _ h.1
  · rw [G.mate, G.atom, G.img]; exact Finset.mem_image_of_mem _ h.2

theorem atom_mem_S (x : D) : M.atom x ∈ S := (G.grp x).1

theorem dartsAt_filter (v : V) (hv : v ∈ S) :
    (M'.dartsAt (φ v)).filter (fun z => M'.InGroup S' z) = (M.dartsAt v).image ι := by
  ext z
  simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨x, rfl⟩ := G.range z h2
    refine ⟨x, ?_, rfl⟩
    rw [G.atom] at h1
    exact G.φinj (G.atom_mem_S x) hv h1
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by rw [G.atom, hx], G.inGroup x⟩

theorem degIn_eq (v : V) (hv : v ∈ S) : M'.degIn S' (φ v) = M.deg v := by
  unfold Molecule.degIn Molecule.deg
  rw [G.dartsAt_filter v hv, Finset.card_image_of_injective _ G.inj]

theorem outIn_eq (v : V) (hv : v ∈ S) : M'.outIn S' (φ v) = M.outdeg v := by
  have : (M'.dartsAt (φ v)).filter (fun z => M'.InGroup S' z ∧ M'.out z = true) =
      ((M.dartsAt v).filter (fun x => M.out x = true)).image ι := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have : z ∈ (M'.dartsAt (φ v)).filter (fun z => M'.InGroup S' z) := Finset.mem_filter.2 ⟨h1, h2⟩
      rw [G.dartsAt_filter v hv] at this
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 this
      exact ⟨x, ⟨hx, by rw [← G.out]; exact h3⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
      have : ι x ∈ (M'.dartsAt (φ v)).filter (fun z => M'.InGroup S' z) := by
        rw [G.dartsAt_filter v hv]; exact Finset.mem_image_of_mem _ hx
      exact ⟨(Finset.mem_filter.1 this).1, G.inGroup x, by rw [G.out]; exact hx2⟩
  unfold Molecule.outIn Molecule.outdeg
  rw [this, Finset.card_image_of_injective _ G.inj]

theorem inIn_eq (v : V) (hv : v ∈ S) : M'.inIn S' (φ v) = M.indeg v := by
  have : (M'.dartsAt (φ v)).filter (fun z => M'.InGroup S' z ∧ M'.out z = false) =
      ((M.dartsAt v).filter (fun x => M.out x = false)).image ι := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have : z ∈ (M'.dartsAt (φ v)).filter (fun z => M'.InGroup S' z) := Finset.mem_filter.2 ⟨h1, h2⟩
      rw [G.dartsAt_filter v hv] at this
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 this
      exact ⟨x, ⟨hx, by rw [← G.out]; exact h3⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
      have : ι x ∈ (M'.dartsAt (φ v)).filter (fun z => M'.InGroup S' z) := by
        rw [G.dartsAt_filter v hv]; exact Finset.mem_image_of_mem _ hx
      exact ⟨(Finset.mem_filter.1 this).1, G.inGroup x, by rw [G.out]; exact hx2⟩
  unfold Molecule.inIn Molecule.indeg
  rw [this, Finset.card_image_of_injective _ G.inj]

theorem groupBonds_eq :
    M'.groupBonds S' = (M.groupBonds S).map (Sym2.map φ) := by
  unfold Molecule.groupBonds
  have hf : (Finset.univ.filter fun z : D' => M'.out z = true ∧ M'.InGroup S' z) =
      (Finset.univ.filter fun x : D => M.out x = true ∧ M.InGroup S x).image ι := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨x, rfl⟩ := G.range z h2
      exact ⟨x, ⟨by rw [← G.out]; exact h1, G.grp x⟩, rfl⟩
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      exact ⟨by rw [G.out]; exact h1, G.inGroup x⟩
  rw [hf, Finset.image_val_of_injOn (G.inj.injOn), Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun x _ => ?_)
  simp [Molecule.ends, G.atom, G.mate, Sym2.map_mk]

theorem outIn_all (v : V) : M.outIn S v = M.outdeg v := by
  unfold Molecule.outIn Molecule.outdeg
  congr 1; ext x
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, G.grp x, h.2⟩⟩

theorem inIn_all (v : V) : M.inIn S v = M.indeg v := by
  unfold Molecule.inIn Molecule.indeg
  congr 1; ext x
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, G.grp x, h.2⟩⟩

theorem degIn_all (v : V) : M.degIn S v = M.deg v := by
  unfold Molecule.degIn Molecule.deg
  congr 1; ext x
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.1, fun h => ⟨h, G.grp x⟩⟩

theorem connected (hc : M.GroupConnected S) : M'.GroupConnected S' := by
  intro u' hu' v' hv'
  rw [G.img] at hu' hv'
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hu'
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hv'
  have key : ∀ a b, Relation.EqvGen (fun a b => ∃ x, M.InGroup S x ∧ M.atom x = a ∧ M.atom (M.mate x) = b) a b →
      Relation.EqvGen (fun a b => ∃ x, M'.InGroup S' x ∧ M'.atom x = a ∧ M'.atom (M'.mate x) = b) (φ a) (φ b) := by
    intro a b h
    induction h with
    | rel a b h =>
      obtain ⟨x, -, hxa, hxb⟩ := h
      exact Relation.EqvGen.rel _ _ ⟨ι x, G.inGroup x, by rw [G.atom, hxa], by rw [G.mate, G.atom, hxb]⟩
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  exact key u v (hc u hu v hv)

theorem isBlock {j₁ j₂ : V} (hS' : S' ⊆ M'.atoms) (hb : M.IsBlock S j₁ j₂) :
    M'.IsBlock S' (φ j₁) (φ j₂) := by
  obtain ⟨-, h1, h2, hne, o1, i1, o2, i2, hd, hc⟩ := hb
  refine ⟨hS', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, G.connected hc⟩
  · rw [G.img]; exact Finset.mem_image_of_mem _ h1
  · rw [G.img]; exact Finset.mem_image_of_mem _ h2
  · exact fun e => hne (G.φinj h1 h2 e)
  · rw [G.outIn_eq _ h1, ← G.outIn_all, o1]
  · rw [G.inIn_eq _ h1, ← G.inIn_all, i1]
  · rw [G.outIn_eq _ h2, ← G.outIn_all, o2]
  · rw [G.inIn_eq _ h2, ← G.inIn_all, i2]
  · intro b hb' n1 n2
    rw [G.img] at hb'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hb'
    rw [G.degIn_eq u hu, ← G.degIn_all]
    exact hd u hu (fun e => n1 (e ▸ rfl)) (fun e => n2 (e ▸ rfl))

theorem isVine {X : VineType} {j₁ j₂ : V} (hS' : S' ⊆ M'.atoms) (hv : M.IsVine X S j₁ j₂) :
    M'.IsVine X S' (φ j₁) (φ j₂) := by
  obtain ⟨hb, k, hk, f, hinj, himg, hj, hbd⟩ := hv
  have : Nonempty V := ⟨j₁⟩
  have h1 := hb.2.1
  have h2 := hb.2.2.1
  have hinv : ∀ u ∈ S, Function.invFunOn φ (S : Set V) (φ u) = u := fun u hu =>
    G.φinj.leftInvOn_invFunOn hu
  have hbd' : ∀ e ∈ M.groupBonds S, ∀ a ∈ e, a ∈ S := by
    intro e he a ha
    unfold Molecule.groupBonds at he
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 he
    have hg := G.grp x
    simp only [Molecule.ends, Sym2.mem_iff] at ha
    rcases ha with rfl | rfl
    · exact hg.1
    · exact hg.2
  refine ⟨G.isBlock hS' hb, k, hk, f ∘ Function.invFunOn φ (S : Set V), ?_, ?_, ?_, ?_⟩
  · intro a ha b hb' e
    rw [G.img] at ha hb'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hb'
    simp only [Function.comp, hinv u hu, hinv v hv] at e
    rw [hinj hu hv e]
  · rw [G.img, Finset.image_image, ← himg]
    refine Finset.image_congr (fun u hu => ?_)
    simp [Function.comp, hinv u hu]
  · simpa [Function.comp, hinv j₁ h1, hinv j₂ h2] using hj
  · rw [G.groupBonds_eq, Multiset.map_map, ← hbd]
    refine Multiset.map_congr rfl (fun e he => ?_)
    unfold Molecule.groupBonds at he
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 he
    have hg := G.grp x
    simp [Function.comp, Molecule.ends, Sym2.map_mk, hinv _ hg.1, hinv _ hg.2]

end GroupIso
end WaveTurbulence.FinalCountG3
