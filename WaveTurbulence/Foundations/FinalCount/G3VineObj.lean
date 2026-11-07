/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3GroupIso
public import WaveTurbulence.Foundations.FinalCount.G3MapBase
/-! **FINALCOUNT-G3: identification of a final vine component with an object of `M_sub`, part 2**: the closure
argument factored out, and the dart embedding of a component into `M_sub`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀}

/-- A set of atoms of the connected `M_sub` closed under bonds and consisting of atoms of degree `4` cannot exist
(`bonds + R = 2 atoms`, `R ≥ 1`). -/
theorem closed_deg4 {R : ℕ} (hS : SubHyp R M₀) (InS : V → Prop) {a : V} (ha : a ∈ M₀.atoms) (hInS : InS a)
    (hclosed : ∀ z : D₀, InS (M₀.atom z) → InS (M₀.atom (M₀.mate z)))
    (h4 : ∀ b ∈ M₀.atoms, InS b → M₀.deg b = 4) : False := by
  have hiff : ∀ u v, M₀.Adj u v → (InS u ↔ InS v) := by
    rintro u v ⟨z, rfl, rfl⟩
    refine ⟨hclosed z, fun h => ?_⟩
    have := hclosed _ h
    rwa [M₀.mate_mate] at this
  have hall' : ∀ u v, Relation.EqvGen M₀.Adj u v → (InS u ↔ InS v) := by
    intro u v h
    induction h with
    | rel _ _ h => exact hiff _ _ h
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  exact sum_deg_ne_four hS (fun b hb => h4 b hb ((hall' a b (hS.conn a ha b hb)).1 hInS))

/-- The dart embedding of a component of the final molecule into `M_sub`. -/
def compEmb (hf : HSt V D₀) (a₀ : V) : PDart hf.s.M (compP hf.s.M a₀) → D₀ := fun x => hf.s.down x.1

/-- **The component as a group of `M_sub`**: if `anc` is injective on the atoms of the component and every dart of
`M_sub` in the group `anc '' atoms` comes from the component, then the component embeds. -/
theorem comp_groupIso (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s) (a₀ : V)
    (hinj : Set.InjOn hf.anc ↑(compMol hf.s.M a₀).atoms)
    (hrange : ∀ z, M₀.InGroup ((compMol hf.s.M a₀).atoms.image hf.anc) z → ∃ x, compEmb hf a₀ x = z) :
    GroupIso (compMol hf.s.M a₀) (compMol hf.s.M a₀).atoms M₀ ((compMol hf.s.M a₀).atoms.image hf.anc) hf.anc
      (compEmb hf a₀) where
  atom := fun x => hA.atom x.1
  mate := fun x => hD.mate x.1
  out := fun x => hD.out x.1
  inj := fun x y e => Subtype.ext (hA.inj e)
  grp := fun x => ⟨(compMol hf.s.M a₀).atom_mem x, (compMol hf.s.M a₀).atom_mem _⟩
  range := hrange
  φinj := hinj
  img := rfl

end WaveTurbulence.FinalCountG3
