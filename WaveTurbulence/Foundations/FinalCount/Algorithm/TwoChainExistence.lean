/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.TwoChainPatterns
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BoundarySupport
public import WaveTurbulence.Foundations.FinalCount.Algorithm.StarSingleBonds
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
import Mathlib.Tactic

/-! # Exhaustive actual degree-two chain geometry in rule seven -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 2R-3F: the neighboring degree-two atoms close a triangle,
have a common outer neighbor, or have two different outer neighbors. -/
theorem exists_two_chain_realization (M : Molecule V D) (hno : AppbNoLoops M)
    {a : V} (ha : a ∈ M.atoms) (hda : M.deg a = 2) (st : Star M a 2)
    (hne : st.neighbor 0 ≠ st.neighbor 1)
    (hdb : M.deg (st.neighbor 0) = 2) (hdc : M.deg (st.neighbor 1) = 2) :
    (∃ r : AppbRealization M AppbPatternKind.r23triangle.pattern,r.vertex 1 = a) ∨
    (∃ r : AppbRealization M appbR23Common,r.vertex 1 = a) ∨
    (∃ r : AppbRealization M AppbPatternKind.r23.pattern,r.vertex 1 = a) := by
  classical
  let b := st.neighbor 0
  let c := st.neighbor 1
  have hb : b ∈ M.atoms := st.neighbor_mem 0
  have hc : c ∈ M.atoms := st.neighbor_mem 1
  have hba : b ≠ a := st.neighbor_ne 0
  have hca : c ≠ a := st.neighbor_ne 1
  have hbc : b ≠ c := hne
  have hinj : Function.Injective st.neighbor := by
    intro i j hh
    fin_cases i <;> fin_cases j
    all_goals first | rfl | exact (hne hh).elim | exact (hne hh.symm).elim
  have hab1 : M.bondsBetween a b = 1 := st.bondsBetween_neighbor_eq_one hinj 0
  have hac1 : M.bondsBetween a c = 1 := st.bondsBetween_neighbor_eq_one hinj 1
  have hba1 : M.bondsBetween b a = 1 := (bondsBetween_symm M b a).trans hab1
  have hca1 : M.bondsBetween c a = 1 := (bondsBetween_symm M c a).trans hac1
  obtain ⟨x,hx,d,hd,hdb',hda',hex⟩ := exists_boundary_neighbor M hno hdb hba1
  obtain ⟨y,hy,e,he,hec,hea,hey⟩ := exists_boundary_neighbor M hno hdc hca1
  have heout (i : Fin 2) : M.out (st.edge i).val = true :=
    (mem_filter.mp (mem_filter.mp (st.edge i).property).1).2
  by_cases hdc' : d = c
  · subst d
    have hnd : ([a,b,c] : List V).Nodup := by
      simp only [List.nodup_cons,List.mem_cons,
        List.mem_singleton,List.not_mem_nil,List.nodup_nil,not_false_eq_true,and_true,not_or]
      exact ⟨⟨hba.symm,hca.symm⟩,hbc⟩
    let r := triangleTwoChain M hnd (by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc) hda hdb hdc
      ![(st.edge 0).val,(st.edge 1).val,x]
      (by intro i; fin_cases i
          · exact heout 0
          · exact heout 1
          · exact (mem_filter.mp hx).2)
      (by intro i; fin_cases i
          · exact st.endpoints 0
          · exact st.endpoints 1
          · exact hex)
    exact Or.inl ⟨r,rfl⟩
  · have heb : e ≠ b := by
      intro heq
      have hcbp : 0 < M.bondsBetween c b := by
        apply card_pos.mpr
        exact ⟨y,mem_filter.mpr ⟨hy,by simpa only [heq] using hey⟩⟩
      have hbcp : 0 < M.bondsBetween b c := by rw [bondsBetween_symm]; exact hcbp
      exact hdc' (boundary_neighbor_unique M hno hdb hba1 hx hex hda' hca hbcp).symm
    by_cases hde : d = e
    · subst e
      have hnd : ([a,b,c,d] : List V).Nodup := by
        simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,
          List.nodup_nil,not_false_eq_true,and_true,not_or]
        exact ⟨⟨hba.symm,hca.symm,hda'.symm⟩,⟨⟨hbc,hdb'.symm⟩,(Ne.symm hdc')⟩⟩
      let r := commonTwoChain M hnd (by
        intro v hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl
        · exact ha
        · exact hb
        · exact hc
        · exact hd) hda hdb hdc
        ![(st.edge 0).val,(st.edge 1).val,x,y]
        (by intro i; fin_cases i
            · exact heout 0
            · exact heout 1
            · exact (mem_filter.mp hx).2
            · exact (mem_filter.mp hy).2)
        (by intro i; fin_cases i
            · exact st.endpoints 0
            · exact st.endpoints 1
            · exact hex
            · exact hey)
      exact Or.inr (Or.inl ⟨r,rfl⟩)
    · have hnd : ([a,b,c,d,e] : List V).Nodup := by
        simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,
          List.nodup_nil,not_false_eq_true,and_true,not_or]
        exact ⟨⟨hba.symm,hca.symm,hda'.symm,hea.symm⟩,
          ⟨⟨hbc,hdb'.symm,heb.symm⟩,⟨⟨(Ne.symm hdc'),hec.symm⟩,hde⟩⟩⟩
      let r := openTwoChain M hnd (by
        intro v hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · exact ha
        · exact hb
        · exact hc
        · exact hd
        · exact he) hda hdb hdc
        ![(st.edge 0).val,(st.edge 1).val,x,y]
        (by intro i; fin_cases i
            · exact heout 0
            · exact heout 1
            · exact (mem_filter.mp hx).2
            · exact (mem_filter.mp hy).2)
        (by intro i; fin_cases i
            · exact st.endpoints 0
            · exact st.endpoints 1
            · exact hex
            · exact hey)
      exact Or.inr (Or.inr ⟨r,rfl⟩)

end WaveTurbulence.Mole.AppbAlgorithm
