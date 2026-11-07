/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm13
public import WaveTurbulence.Foundations.FinalCount.AsmTerm7
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 14a: perfect components of the Operation-5 molecule are tame-free and even.** -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- In a tame-free component Operation 5 does not change degrees. -/
theorem op5_deg_eq {hf : HSt V D₀} {Tm : V → Prop} {a b : V} (hT : TameFree hf Tm a)
    (ha5 : a ∈ (hf.op5 Tm).s.M.atoms) (hsc : hf.s.M.SameComponent a b) :
    (hf.op5 Tm).s.M.deg b = hf.s.M.deg b := by
  obtain ⟨hb5, -⟩ := op5_comp hT ha5 hsc
  have hk : keepS hf.s (tameSet hf Tm) b := (Finset.mem_filter.1 hb5).2
  have hbT : b ∉ tameSet hf Tm := tameFree_notin hT hsc
  rw [show (hf.op5 Tm).s.M.deg b = (eraseSet hf.s.M (tameSet hf Tm)).deg b from eraseSetSt_deg hk]
  have h := eraseSet_deg_card hf.s.M (tameSet hf Tm) hbT
  have hm : multS hf.s.M (tameSet hf Tm) b = 0 := by
    unfold multS
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx hxT
    have hxa : hf.s.M.atom x = b := by simpa [Molecule.dartsAt] using hx
    have hadj : hf.s.M.SameComponent b (hf.s.M.atom (hf.s.M.mate x)) :=
      Relation.EqvGen.rel _ _ ⟨x, hxa, rfl⟩
    exact tameFree_notin hT (Relation.EqvGen.trans _ _ _ hsc hadj) hxT
  omega

/-- A perfect component of the Operation-5 state lies over a tame-free, even component of `hf`. -/
theorem perfect_unt {hf : HSt V D₀} {Tm : V → Prop} {R : ℕ} (hg : Good R hf.s) {a : V}
    (ha : a ∈ (hf.op5 Tm).s.M.atoms)
    (hper : ∀ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b → contrib (hf.op5 Tm).s b = 0) :
    TameFree hf Tm a ∧ ¬ CompOdd hf a := by
  have hT : TameFree hf Tm a := Op5.perfect_tameFree hg ha hper
  refine ⟨hT, ?_⟩
  rintro ⟨b, hb, hodd⟩
  have hb' := (mem_compMol _ _).1 hb
  rw [compMol_deg _ _ hb'.2] at hodd
  have hsc5 : (hf.op5 Tm).s.M.SameComponent a b := by
    have := op5_compAtoms hT ha
    have hb2 : b ∈ compAtoms hf.s.M a := by unfold compAtoms; exact Finset.mem_filter.2 ⟨hb'.1, hb'.2⟩
    rw [← this] at hb2
    exact (Finset.mem_filter.1 hb2).2
  have hb5 : b ∈ (hf.op5 Tm).s.M.atoms := by
    have := op5_compAtoms hT ha
    have hb2 : b ∈ compAtoms hf.s.M a := by unfold compAtoms; exact Finset.mem_filter.2 ⟨hb'.1, hb'.2⟩
    rw [← this] at hb2
    exact (Finset.mem_filter.1 hb2).1
  have h0 := hper b hb5 hsc5
  unfold contrib at h0
  have hd := op5_deg_eq hT ha hb'.2
  have he := Cls.even_base ((hf.op5 Tm).s.cls b)
  have h1 : (((hf.op5 Tm).s.M.deg b : ℕ) : ℤ) = ((hf.op5 Tm).s.cls b).base := by omega
  apply hodd
  rw [← hd]
  have : Even (((hf.op5 Tm).s.M.deg b : ℕ) : ℤ) := by rw [h1]; exact he
  exact (Int.even_coe_nat _).1 this

end WaveTurbulence.FinalCountAsm
