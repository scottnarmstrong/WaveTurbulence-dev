/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C4Data
public import WaveTurbulence.Foundations.FinalCount.C4Vine2
public import WaveTurbulence.Foundations.FinalCount.C5VineH
import Mathlib.Tactic

/-! # Prop 9.6, case (4): a `Q`-type closure makes `𝕄₀` a vine (II)

If `𝕄₁ = closureTwo` is a `Z_m(Q)` ladder, then `𝕄₁` minus the bond of the first chain is a half-closed vine (II)
(`halfClosure_of_zq`), and `isVine_of_halfClosure` (case (5)) makes `𝕄₀` a vine (II).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem c4_two_vine {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd) {b b' : V}
    {y₁ y₂ y₃ y₄ : D} (D4 : Case4TwoData M cls b b' y₁ y₂ y₃ y₄)
    (hZ : ∃ (m : ℕ) (φ : Bool × ℕ → V), IsZQ (closureTwo M b b' y₁ y₂ y₃ y₄) m φ) :
    M.IsVine VineType.II M.atoms b' b := by
  classical
  obtain ⟨m, φ, hφ⟩ := hZ
  have hdirA := hS.dir2 b D4.hb D4.hdeg2
  have hdirB := hS.dir2 b' D4.hb' D4.hdeg2'
  have hy12 : y₁ ≠ y₂ := fun h => D4.hfar1 (by rw [h])
  have hy34 : y₃ ≠ y₄ := fun h => D4.hfar2 (by rw [h])
  have hyd : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset D), M.atom (M.mate y) ≠ b ∧ M.atom (M.mate y) ≠ b' := fun y hy =>
    ⟨fun h => D4.hnb (h ▸ D4.hendsE y hy), fun h => D4.hnb' (h ▸ D4.hendsE y hy)⟩
  have hat : ∀ {K : Finset V} {y₁ y₂ : D}, crossDarts M K = {y₁, y₂} → M.atom y₁ ∈ K ∧ M.atom y₂ ∈ K := by
    intro K y₁ y₂ h
    exact ⟨(mem_crossDarts.mp (by rw [h]; simp)).1, (mem_crossDarts.mp (by rw [h]; simp)).1⟩
  have hat1 : M.atom y₁ = b := mem_singleton.mp (hat D4.hc1).1
  have hat2 : M.atom y₂ = b := mem_singleton.mp (hat D4.hc1).2
  have hat3 : M.atom y₃ = b' := mem_singleton.mp (hat D4.hc2).1
  have hat4 : M.atom y₄ = b' := mem_singleton.mp (hat D4.hc2).2
  have hall1 : ∀ x, M.atom x = b → x = y₁ ∨ x = y₂ := by
    intro x hx
    have : x ∈ crossDarts M {b} := mem_crossDarts.mpr ⟨by rw [hx]; exact mem_singleton_self _,
      fun h => hS.noLoop x (hx.trans (mem_singleton.mp h).symm)⟩
    rw [D4.hc1] at this; simpa using this
  have hall2 : ∀ x, M.atom x = b' → x = y₃ ∨ x = y₄ := by
    intro x hx
    have : x ∈ crossDarts M {b'} := mem_crossDarts.mpr ⟨by rw [hx]; exact mem_singleton_self _,
      fun h => hS.noLoop x (hx.trans (mem_singleton.mp h).symm)⟩
    rw [D4.hc2] at this; simpa using this
  have hKA : ({b} : Finset V) ⊆ M.atoms := by simpa using D4.hb
  let Ta : TwoExit M := ⟨{b}, hKA, y₂, y₁, by rw [D4.hc1]; exact pair_comm _ _, hy12.symm, D4.hfar1.symm, D4.ho2, D4.ho1⟩
  have hTaY : Ta.Y = {b} := rfl
  have ha_all : ∀ x, M.atom x = b → x = Ta.x ∨ x = Ta.y := by
    intro x hx; rcases hall1 x hx with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hnadj : Ta.c ≠ b' ∧ Ta.d ≠ b' := ⟨(hyd y₂ (by simp)).2, (hyd y₁ (by simp)).2⟩
  have p₃ : M.atom y₃ ∉ ({b} : Finset V) ∧ M.atom (M.mate y₃) ∉ ({b} : Finset V) :=
    ⟨by rw [hat3]; simpa using D4.hbb'.symm, by simpa using (hyd y₃ (by simp)).1⟩
  have p₄ : M.atom y₄ ∉ ({b} : Finset V) ∧ M.atom (M.mate y₄) ∉ ({b} : Finset V) :=
    ⟨by rw [hat4]; simpa using D4.hbb'.symm, by simpa using (hyd y₄ (by simp)).1⟩
  obtain ⟨hcK, hdir⟩ := chain_after_erase hS.noLoop D4.hc2 p₃ p₄
  have hbN : b' ∈ (Degen.eraseAtoms M {b}).atoms := mem_sdiff.mpr ⟨D4.hb', by simpa using D4.hbb'.symm⟩
  have hneN : (⟨y₄, p₄⟩ : Degen.RetainedDart M {b}) ≠ ⟨y₃, p₃⟩ := fun h => hy34 (congrArg Subtype.val h).symm
  have hKb : ({b'} : Finset V) ⊆ (Degen.eraseAtoms M {b}).atoms := by simpa using hbN
  let Tb : TwoExit (Degen.eraseAtoms M {b}) :=
    ⟨{b'}, hKb, ⟨y₄, p₄⟩, ⟨y₃, p₃⟩, by rw [hcK]; exact pair_comm _ _, hneN, D4.hfar2.symm, D4.ho4, D4.ho3⟩
  have hTbY : Tb.Y = {b'} := rfl
  have hbn : ∀ x : D, M.atom x = b' → M.atom x ∉ ({b} : Finset V) ∧ M.atom (M.mate x) ∉ ({b} : Finset V) := by
    intro x hx
    rcases hall2 x hx with rfl | rfl
    · exact p₃
    · exact p₄
  have hb_all : ∀ x : D, M.atom x = b' → x = Tb.x.val ∨ x = Tb.y.val := by
    intro x hx
    rcases hall2 x hx with h | h
    · exact Or.inr h
    · exact Or.inl h
  -- the half-closure
  have hle2 := hS.noTriple
  have hpostAt : Tb.post.atoms = (closureTwo M b b' y₁ y₂ y₃ y₄).atoms := by
    have hm : ∀ y, M.atom (M.mate y) ∈ M.atoms → M.atom (M.mate y) ≠ b → M.atom (M.mate y) ≠ b' →
        M.atom (M.mate y) ∈ (M.atoms \ {b}) \ {b'} := fun y h1 h2 h3 =>
      mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨h1, by simpa using h2⟩, by simpa using h3⟩
    rw [atoms_closureTwo M b b' y₁ y₂ y₃ y₄ (hm _ (M.atom_mem _) (hyd y₁ (by simp)).1 (hyd y₁ (by simp)).2)
      (hm _ (M.atom_mem _) (hyd y₂ (by simp)).1 (hyd y₂ (by simp)).2)
      (hm _ (M.atom_mem _) (hyd y₃ (by simp)).1 (hyd y₃ (by simp)).2)
      (hm _ (M.atom_mem _) (hyd y₄ (by simp)).1 (hyd y₄ (by simp)).2)]
    rw [Tb.post_atoms, hTbY]; rfl
  have hcdmem : M.atom (M.mate y₁) ∈ (closureTwo M b b' y₁ y₂ y₃ y₄).atoms ∧
      M.atom (M.mate y₂) ∈ (closureTwo M b b' y₁ y₂ y₃ y₄).atoms := by
    change _ ∈ insert _ (insert _ _) ∧ _ ∈ insert _ (insert _ _)
    exact ⟨mem_insert_self _ _, mem_insert_of_mem (mem_insert_self _ _)⟩
  have hH : IsVineIIHalfClosure Tb.post := by
    refine halfClosure_of_zq (c := M.atom (M.mate y₁)) (d := M.atom (M.mate y₂)) (c' := M.atom (M.mate y₃))
      (d' := M.atom (M.mate y₄)) hφ hpostAt ⟨hcdmem.1, hcdmem.2, D4.hfar1⟩ ?_ ?_
    · intro p q
      change (Mole.addBond Tb.post (M.atom (M.mate y₁)) (M.atom (M.mate y₂))).bondsBetween p q = _
      rw [addBond_bondsBetween]
    · intro p q
      by_cases hpq : p ∈ (closureTwo M b b' y₁ y₂ y₃ y₄).atoms ∧ q ∈ (closureTwo M b b' y₁ y₂ y₃ y₄).atoms
      · have hA : (closureTwo M b b' y₁ y₂ y₃ y₄).atoms = (M.atoms \ {b}) \ {b'} := by
          rw [← hpostAt, Tb.post_atoms, hTbY]; rfl
        rw [hA] at hpq
        have h1 := mem_sdiff.mp hpq.1; have h2 := mem_sdiff.mp h1.1
        have h3 := mem_sdiff.mp hpq.2; have h4 := mem_sdiff.mp h3.1
        rw [bb_closureTwo M b b' y₁ y₂ y₃ y₄ (by simpa using h2.2) (by simpa using h1.2) (by simpa using h4.2)
          (by simpa using h3.2)]
        have := hle2 p q
        split_ifs <;> omega
      · have : (closureTwo M b b' y₁ y₂ y₃ y₄).bondsBetween p q = 0 := by
          by_cases hp : p ∈ (closureTwo M b b' y₁ y₂ y₃ y₄).atoms
          · rw [Degen.bondsBetween_comm]; exact bb_zero_of_not_mem _ (fun hq => hpq ⟨hp, hq⟩) p
          · exact bb_zero_of_not_mem _ hp q
        rw [this]; omega
  exact isVine_of_halfClosure hS.noLoop hS.conn hS.noTriple D4.hb D4.hb' D4.hbb' hdirA hdirB D4.hdeg4 Ta hTaY ha_all Tb
    hTbY hb_all hnadj hH |> fun h => by simpa using h

end
end WaveTurbulence.FinalCountG8
