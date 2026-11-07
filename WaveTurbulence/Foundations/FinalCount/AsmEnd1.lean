/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmConn1
/-! **FINALCOUNT-ASSEMBLY (HendAt, part 1): the state after vine removals is the molecule `remMol M₀ ps`.**
`numComponents_rename` (components are invariant under a bijection of darts compatible with an atom renaming injective on the atoms),
`remMol M₀ ps` (the darts of `M₀` outside the kill sets of the pieces `ps`, on the atoms that are not interior to a piece), and
`state_rem_iso`: along a vine-only history (`ConnInv`) the state molecule is `remMol M₀ ps` up to the renaming `anc`
(equal number of components, equal degrees). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section rename
variable {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

theorem numComponents_rename {M : Molecule V D} {N : Molecule V D'} (e : D ≃ D') (π : V → V)
    (hatoms : N.atoms = M.atoms.image π) (hinj : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, π a = π b → a = b)
    (hatom : ∀ x, N.atom (e x) = π (M.atom x)) (hmate : ∀ x, N.mate (e x) = e (M.mate x)) :
    N.numComponents = M.numComponents := by
  unfold Molecule.numComponents
  let f : M.atoms ≃ N.atoms := Equiv.ofBijective
    (fun a => ⟨π a.1, by rw [hatoms]; exact Finset.mem_image_of_mem _ a.2⟩)
    ⟨fun a b hab => Subtype.ext (hinj _ a.2 _ b.2 (congrArg Subtype.val hab)), fun b => by
      have hb : b.1 ∈ M.atoms.image π := hatoms ▸ b.2
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.1 hb
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩⟩
  have hadj : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, N.Adj (π a) (π b) ↔ M.Adj a b := by
    intro a ha b hb
    constructor
    · rintro ⟨y, h1, h2⟩
      refine ⟨e.symm y, ?_, ?_⟩
      · have := hatom (e.symm y)
        rw [Equiv.apply_symm_apply] at this
        exact hinj _ (M.atom_mem _) _ ha (this.symm.trans h1)
      · have := hatom (M.mate (e.symm y))
        rw [← hmate, Equiv.apply_symm_apply] at this
        exact hinj _ (M.atom_mem _) _ hb (this.symm.trans h2)
    · rintro ⟨x, h1, h2⟩
      exact ⟨e x, by rw [hatom, h1], by rw [hmate, hatom, h2]⟩
  exact (Nat.card_congr (Quot.congr f (fun a b => (hadj a.1 a.2 b.1 b.2).symm))).symm

theorem deg_rename {M : Molecule V D} {N : Molecule V D'} (e : D ≃ D') (π : V → V)
    (hinj : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, π a = π b → a = b)
    (hatom : ∀ x, N.atom (e x) = π (M.atom x)) {c : V} (hc : c ∈ M.atoms) : N.deg (π c) = M.deg c := by
  unfold Molecule.deg
  have : (M.dartsAt c).map e.toEmbedding = N.dartsAt (π c) := by
    ext y
    simp only [Finset.mem_map, Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨x, hx, rfl⟩; rw [hatom, hx]
    · intro hy
      refine ⟨e.symm y, ?_, Equiv.apply_symm_apply _ _⟩
      have := hatom (e.symm y)
      rw [Equiv.apply_symm_apply] at this
      exact hinj _ (M.atom_mem _) _ hc (this.symm.trans hy)
  rw [← this, Finset.card_map]

end rename

/-- The killed darts of the pieces `ps`. -/
def KillS {M₀ : Molecule V D₀} (ps : List (Object M₀ × Quad D₀)) : Set D₀ := {z | ∃ p ∈ ps, z ∈ PieceKill p.1 p.2}

/-- The molecule `M₀` with the pieces `ps` removed (the joints stay, with their non-node darts). -/
noncomputable def remMol (M₀ : Molecule V D₀) (ps : List (Object M₀ × Quad D₀)) :
    Molecule V {z : D₀ // z ∉ KillS ps ∧ M₀.mate z ∉ KillS ps} where
  atoms := M₀.atoms.filter (fun v => ∀ p ∈ ps, ¬ PieceInt p.1 v)
  atom z := M₀.atom z.1
  mate z := ⟨M₀.mate z.1, z.2.2, by rw [M₀.mate_mate]; exact z.2.1⟩
  out z := M₀.out z.1
  atom_mem z := by
    refine Finset.mem_filter.2 ⟨M₀.atom_mem z.1, fun p hp hi => z.2.1 ⟨p, hp, hi.1, fun hj => ?_⟩⟩
    rcases hj with hj | hj
    · exact absurd hj hi.2.1
    · exact absurd hj hi.2.2
  mate_mate z := Subtype.ext (M₀.mate_mate z.1)
  mate_ne z h := M₀.mate_ne z.1 (congrArg Subtype.val h)
  out_mate z := M₀.out_mate z.1

/-- **The state is `remMol`**: along a vine-only history the state has the same number of components and the same degrees. -/
theorem state_rem_iso {M₀ : Molecule V D₀} {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s)
    (ps : List (Object M₀ × Quad D₀))
    (hinj : ∀ c ∈ h.s.M.atoms, ∀ b ∈ h.s.M.atoms, h.anc c = h.anc b → c = b)
    (hpres : ∀ z : D₀, (∀ x : h.s.D, h.s.down x ≠ z) → ∃ p ∈ ps, z ∈ PieceKill p.1 p.2)
    (he1 : ∀ x : h.s.D, ∀ p ∈ ps, h.s.down x ∉ PieceKill p.1 p.2)
    (he2 : ∀ v ∈ M₀.atoms, (∀ p ∈ ps, ¬ PieceInt p.1 v) → ∃ c ∈ h.s.M.atoms, h.anc c = v)
    (he3 : ∀ c ∈ h.s.M.atoms, ∀ p ∈ ps, ¬ PieceInt p.1 (h.anc c)) :
    (remMol M₀ ps).numComponents = h.s.M.numComponents ∧
      (∀ c ∈ h.s.M.atoms, (remMol M₀ ps).deg (h.anc c) = h.s.M.deg c) ∧
      (remMol M₀ ps).atoms = h.s.M.atoms.image h.anc := by
  have hmem : ∀ x : h.s.D, h.s.down x ∉ KillS ps ∧ M₀.mate (h.s.down x) ∉ KillS ps := by
    intro x
    refine ⟨fun ⟨p, hp, hk⟩ => he1 x p hp hk, fun ⟨p, hp, hk⟩ => ?_⟩
    rw [hD.mate] at hk
    exact he1 _ p hp hk
  let e : h.s.D ≃ {z : D₀ // z ∉ KillS ps ∧ M₀.mate z ∉ KillS ps} := Equiv.ofBijective (fun x => ⟨h.s.down x, hmem x⟩)
    ⟨fun a b hab => hA.inj (congrArg Subtype.val hab), fun z => by
      by_contra hno
      push Not at hno
      have : ∀ x : h.s.D, h.s.down x ≠ z.1 := fun x hx => hno x (Subtype.ext hx)
      obtain ⟨p, hp, hk⟩ := hpres z.1 this
      exact z.2.1 ⟨p, hp, hk⟩⟩
  have hatoms : (remMol M₀ ps).atoms = h.s.M.atoms.image h.anc := by
    ext v
    simp only [remMol, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hv, hvn⟩
      obtain ⟨c, hc, hcv⟩ := he2 v hv hvn
      exact ⟨c, hc, hcv⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨hA.mem c hc, he3 c hc⟩
  have hatom : ∀ x, (remMol M₀ ps).atom (e x) = h.anc (h.s.M.atom x) := fun x => hA.atom x
  have hmate : ∀ x, (remMol M₀ ps).mate (e x) = e (h.s.M.mate x) := fun x =>
    Subtype.ext (hD.mate x)
  refine ⟨numComponents_rename e h.anc hatoms hinj hatom hmate, fun c hc => deg_rename e h.anc hinj hatom hc, hatoms⟩

end WaveTurbulence.FinalCountAsm
