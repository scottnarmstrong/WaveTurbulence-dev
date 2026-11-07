/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Case5
public import WaveTurbulence.Foundations.FinalCount.C5VineH
import Mathlib.Tactic

/-! # Prop 9.6, case (5): the vine input is proved, so case (5) is unconditional -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4

/-- In the two-chain branch of case (5) the post molecule is not a half-closed vine (II): otherwise `M₀` would be a
vine (II) with joints `β, α` (so LG by Prop 9.5), contradicting that the `α`-atom is SG. -/
theorem case5VineS2_proved (d : ℕ) (γ η : ℝ) : Case5VineS2.{u, v} d γ η := by
  intro L V D _ _ _ M cls odd Adm hS hF hA hnodd hfr a₀ b₀ ha₀ hb₀ hab hαa hβb hdeg2a hdeg2b hdeg4 hK hKb T hTY H
  classical
  obtain ⟨κ0, hκ0⟩ := hA
  have hbn : ¬ (cls b₀).IsEps := beta_not_eps hβb
  have hnotadj : ¬ M.Adj a₀ b₀ := fun h => hab (mem_singleton.mp (hK.2.2.2.1 a₀ (mem_singleton_self _) b₀ h hbn)).symm
  have hdirA := hS.dir2 a₀ ha₀ hdeg2a
  have hdirB := hS.dir2 b₀ hb₀ hdeg2b
  have hcmem := T.c_mem
  have hnc : ¬ ∀ a ∈ M.atoms, M.deg a = 2 := by
    intro hall
    rw [hTY] at hcmem
    have h1 : T.c ∈ M.atoms \ {a₀} := (mem_sdiff.mp hcmem).1
    have h2 : T.c ≠ b₀ := by simpa using (mem_sdiff.mp hcmem).2
    have h3 : T.c ≠ a₀ := by simpa using (mem_sdiff.mp h1).2
    have h4 := hdeg4 T.c (mem_sdiff.mp h1).1 h3 h2
    have h5 := hall T.c (mem_sdiff.mp h1).1
    omega
  obtain ⟨y₁, y₂, hcross, hy12, _, _, hne⟩ := hS.chains hnodd hnc {a₀} hK
  have hKA : ({a₀} : Finset V) ⊆ M.atoms := by simpa using ha₀
  obtain ⟨Ta, hTaY, _⟩ := twoExit_of_chain M hKA
    (fun v hv => by rw [mem_singleton.mp hv]; rw [hdirA.1, hdirA.2]) hcross hy12 hne
  have hax : M.atom Ta.x = a₀ := by have := Ta.atom_x; rw [hTaY] at this; exact mem_singleton.mp this
  have hay : M.atom Ta.y = a₀ := by have := Ta.atom_y; rw [hTaY] at this; exact mem_singleton.mp this
  have ha_all : ∀ x, M.atom x = a₀ → x = Ta.x ∨ x = Ta.y := by
    intro x hx
    have hxm : x ∈ crossDarts M Ta.Y := by
      refine mem_crossDarts.mpr ⟨by rw [hTaY, hx]; exact mem_singleton_self _, ?_⟩
      rw [hTaY]
      intro h
      exact hS.noLoop x (by rw [hx, mem_singleton.mp h])
    rw [Ta.cross] at hxm
    simpa using hxm
  have hnadj : Ta.c ≠ b₀ ∧ Ta.d ≠ b₀ := by
    constructor
    · intro h; exact hnotadj ⟨Ta.x, hax, h⟩
    · intro h; exact hnotadj ⟨Ta.y, hay, h⟩
  have hbN : ∀ x : D, M.atom x = b₀ → M.atom x ∉ ({a₀} : Finset V) ∧ M.atom (M.mate x) ∉ ({a₀} : Finset V) := by
    intro x hx
    refine ⟨by rw [hx]; simpa using hab.symm, ?_⟩
    intro h
    have hh : M.atom (M.mate x) = a₀ := mem_singleton.mp h
    exact hnotadj (Mole.adj_symmetric M ⟨x, hx, hh⟩)
  have hb_all : ∀ x : D, M.atom x = b₀ → x = T.x.val ∨ x = T.y.val := by
    intro x hx
    set zr : Degen.RetainedDart M {a₀} := ⟨x, hbN x hx⟩ with hzr
    have hzm : zr ∈ crossDarts (Degen.eraseAtoms M {a₀}) T.Y := by
      refine mem_crossDarts.mpr ⟨by rw [hTY]; exact mem_singleton.mpr hx, ?_⟩
      rw [hTY]
      intro h
      have hh : M.atom (M.mate x) = b₀ := mem_singleton.mp h
      exact hS.noLoop x (by rw [hx, hh])
    rw [T.cross] at hzm
    rcases mem_insert.mp hzm with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val (mem_singleton.mp h))
  have hV := isVine_of_halfClosure hS.noLoop hS.conn hS.noTriple ha₀ hb₀ hab hdirA hdirB hdeg4 Ta hTaY ha_all T hTY
    hb_all hnadj H
  exact vine_contra hS hF hκ0 ha₀ hαa hdeg2a ⟨_, _, _, hV⟩

/-- **Case (5): `V_α = V_β = 1`** (DH23 L1887), unconditional. -/
theorem case_five (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    EvenCaseAt.{u, v} d γ η (fun a b => a = 1 ∧ b = 1) :=
  case_five_of_vine d hd γ hγ η hη hsm hηs (case5VineS2_proved d γ η)

end WaveTurbulence.FinalCountG8
