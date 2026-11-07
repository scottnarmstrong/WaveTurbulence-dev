/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GV01
public import WaveTurbulence.Foundations.FinalCount.G3VineObj
public import WaveTurbulence.Foundations.FinalCount.G3GroupIso
public import WaveTurbulence.Foundations.FinalCount.G3MapBase
/-! **G3-LOWDEG port of `G3VineObj`** (only the declarations that change: `SubHypL->SubHypL`, `HRunL->HRunL`, `InvL->InvL`, `FinalStructM->FinalStructM`, `Prop95ConclAtL->Prop95ConclAtL`; names get suffix `L`). -/
@[expose] public section
open WaveTurbulence.VineParamContract

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
theorem closed_deg4L {R : ℕ} (hS : SubHypL R M₀) (InS : V → Prop) {a : V} (ha : a ∈ M₀.atoms) (hInS : InS a)
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
  exact sum_deg_ne_fourL hS (fun b hb => h4 b hb ((hall' a b (hS.conn a ha b hb)).1 hInS))

end WaveTurbulence.FinalCountG3

