/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineObj2
public import WaveTurbulence.Foundations.FinalCount.G3Final2
/-! **FINALCOUNT-G3: bridge** from the vine hypothesis `IsVine X C.atoms j₁ j₂` on a component of the final molecule to
the shape data `FinalJoints` (joints of degree `2` and non-`ε`, all other atoms `ε` of degree `4`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {hf : HSt V D₀} {a₀ j₁ j₂ : V}

section groupAll
variable {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V}

theorem degIn_of_all (h : ∀ x, M.InGroup S x) (v : V) : M.degIn S v = M.deg v := by
  unfold Molecule.degIn Molecule.deg
  congr 1; ext x
  simp only [Finset.mem_filter]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', h x⟩⟩

theorem outIn_of_all (h : ∀ x, M.InGroup S x) (v : V) : M.outIn S v = M.outdeg v := by
  unfold Molecule.outIn Molecule.outdeg
  congr 1; ext x
  simp only [Finset.mem_filter]
  exact ⟨fun h' => ⟨h'.1, h'.2.2⟩, fun h' => ⟨h'.1, h x, h'.2⟩⟩

theorem inIn_of_all (h : ∀ x, M.InGroup S x) (v : V) : M.inIn S v = M.indeg v := by
  unfold Molecule.inIn Molecule.indeg
  congr 1; ext x
  simp only [Finset.mem_filter]
  exact ⟨fun h' => ⟨h'.1, h'.2.2⟩, fun h' => ⟨h'.1, h x, h'.2⟩⟩

end groupAll

theorem compMol_grp (hf : HSt V D₀) (a₀ : V) (x : PDart hf.s.M (compP hf.s.M a₀)) :
    (compMol hf.s.M a₀).InGroup (compMol hf.s.M a₀).atoms x :=
  ⟨(compMol hf.s.M a₀).atom_mem x, (compMol hf.s.M a₀).atom_mem _⟩

/-- A vine component of the final molecule has the shape `FinalJoints`. -/
theorem finalJoints_of_vine {R : ℕ} (hst : FinalStruct R hf.s) {X : VineType}
    (hv : (compMol hf.s.M a₀).IsVine X (compMol hf.s.M a₀).atoms j₁ j₂) (ha₀ : a₀ ∈ hf.s.M.atoms) :
    FinalJoints hf a₀ j₁ j₂ := by
  obtain ⟨-, h1, h2, hne, o1, i1, o2, i2, hd, -⟩ := hv.1
  have m1 := (mem_compMol _ _).1 h1
  have m2 := (mem_compMol _ _).1 h2
  have hg := compMol_grp hf a₀
  have d1 : hf.s.M.deg j₁ = 2 := by
    rw [← compMol_deg hf.s.M a₀ m1.2, deg_eq, ← outIn_of_all hg, ← inIn_of_all hg, o1, i1]
  have d2 : hf.s.M.deg j₂ = 2 := by
    rw [← compMol_deg hf.s.M a₀ m2.2, deg_eq, ← outIn_of_all hg, ← inIn_of_all hg, o2, i2]
  refine ⟨m1.1, m2.1, hne, m1.2, m2.2, d1, d2, ?_, ?_, ?_⟩
  · intro h; have := hst.eps_deg j₁ m1.1 h; omega
  · intro h; have := hst.eps_deg j₂ m2.1 h; omega
  · intro b hb hbc
    by_cases e1 : b = j₁
    · exact Or.inl e1
    by_cases e2 : b = j₂
    · exact Or.inr (Or.inl e2)
    right; right
    have hbm : b ∈ (compMol hf.s.M a₀).atoms := (mem_compMol _ _).2 ⟨hb, hbc⟩
    have h4 := hd b hbm e1 e2
    have hdeg : hf.s.M.deg b = 4 := by
      rw [← compMol_deg hf.s.M a₀ hbc, ← degIn_of_all hg]; exact h4
    refine ⟨?_, hdeg⟩
    by_contra hne'
    have := hst.ab_deg b hb hne'
    omega

end WaveTurbulence.FinalCountG3
