/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3CompRun
/-! **FINALCOUNT-G3**: the relation `DartRel M₀ s` between the darts of the current molecule and those of `M_sub`:
the inclusion `down` commutes with `mate` and `out`, and the darts at an `ε`-atom are untouched (the atom of
the dart in `M_sub` is the same). Used to transport the decoration (labels, SG/LG) to the final molecule. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The dart relation. -/
structure DartRel (M₀ : Molecule V D₀) (s : St.{u} V D₀) : Prop where
  mate : ∀ x, M₀.mate (s.down x) = s.down (s.M.mate x)
  out : ∀ x, M₀.out (s.down x) = s.M.out x
  eps : ∀ x, s.cls (s.M.atom x) = .eps → M₀.atom (s.down x) = s.M.atom x

theorem DartRel.init (M₀ : Molecule V D₀) : DartRel M₀ (St.init M₀) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

variable {M₀ : Molecule V D₀} {s : St.{u} V D₀}

theorem DartRel.cutSt (h : DartRel M₀ s) (v v₂ : V) (x₁ x₂ : s.D) (c₁ c₂ : Cls) (h₁ : c₁ ≠ .eps) (h₂ : c₂ ≠ .eps)
    (hv₂ : v₂ ∉ s.M.atoms) :
    DartRel M₀ (s.cutSt v v₂ x₁ x₂ c₁ c₂) := by
  refine ⟨h.mate, h.out, ?_⟩
  intro x hx
  have hmem := s.M.atom_mem x
  have e : (s.cutSt v v₂ x₁ x₂ c₁ c₂).M.atom x = (s.M.cut v v₂ x₁ x₂).atom x := rfl
  rw [e] at hx ⊢
  rw [cut_atom s.M v v₂ x₁ x₂ x] at hx ⊢
  split_ifs at hx ⊢ with hm
  · exfalso
    have : (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls v₂ = c₂ := cutSt_cls_v₂ c₁ c₂
    exact h₂ (this ▸ hx)
  · have hne : s.M.atom x ≠ v₂ := fun e' => hv₂ (e' ▸ hmem)
    have hnv : s.M.atom x ≠ v := by
      intro e'
      have hne' : v₂ ≠ v := fun e'' => hv₂ (e'' ▸ (e' ▸ hmem))
      have := cutSt_cls_v (s := s) (v := v) (v₂ := v₂) (x₁ := x₁) (x₂ := x₂) c₁ c₂ hne'
      rw [e'] at hx
      exact h₁ (this ▸ hx)
    have := cutSt_cls_other (s := s) (v := v) (v₂ := v₂) (x₁ := x₁) (x₂ := x₂) c₁ c₂ hnv hne
    exact h.eps x (this ▸ hx)

theorem DartRel.delSt (h : DartRel M₀ s) (P : V → Prop) [DecidablePred P] (hP : PClosed s.M P) :
    DartRel M₀ (s.delSt P hP) :=
  ⟨fun x => h.mate x.1, fun x => h.out x.1, fun x hx => h.eps x.1 hx⟩

theorem DartRel.withCls (h : DartRel M₀ s) (c : V → Cls) (hc : ∀ a ∈ s.M.atoms, (c a = .eps ↔ s.cls a = .eps)) :
    DartRel M₀ (s.withCls c) :=
  ⟨h.mate, h.out, fun x hx => h.eps x ((hc _ (s.M.atom_mem x)).1 hx)⟩

end WaveTurbulence.FinalCountG3
