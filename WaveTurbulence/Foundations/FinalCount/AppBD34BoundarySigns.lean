/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD34Frames
public import WaveTurbulence.Foundations.FinalCount.AppBFrameSignCap
public import WaveTurbulence.Foundations.FinalCount.AppBCutInternalSign
public import WaveTurbulence.Foundations.FinalCount.AppBTripleQuadSigns
import Mathlib.Tactic

/-! # The boundary triple of a 3D4 group has admissible source signs -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbD34Signs {M : Molecule V D} (k : AppbPatternKind) (hk : k ∈ appbD34Kinds)
    (r : AppbRealization M k.pattern) (j : Fin 5) : ℤˣ :=
  appbIncidenceSign M (r.vertex (if j < 3 then 1 else 2))
    (r.edge (appbFiveEmbedding (appb_d34_kind_length k hk) j)).val

theorem appb_d34_internal_sign {M : Molecule V D} (k : AppbPatternKind) (hk : k ∈ appbD34Kinds)
    (r : AppbRealization M k.pattern) (j : Fin 5) (hj : j < 2) :
    appbIncidenceSign M (r.vertex 2) (r.edge (appbFiveEmbedding (appb_d34_kind_length k hk) j)).val =
      -appbD34Signs k hk r j := by
  have ht : ∀ k ∈ appbD34Kinds,1 ∈ k.pattern.vertices ∧ 2 ∈ k.pattern.vertices := by decide
  have hne : r.vertex 2 ≠ r.vertex 1 := fun he => (by decide : (2 : ℕ) ≠ 1)
    (r.vertex_injective (ht k hk).2 (ht k hk).1 he)
  have he : M.ends (r.edge (appbFiveEmbedding (appb_d34_kind_length k hk) j)).val = s(r.vertex 2,r.vertex 1) := by
    rw [r.endpoints]
    have hends : ∀ (k : AppbPatternKind) (hk : k ∈ appbD34Kinds),∀ j : Fin 5,j < 2 →
        k.pattern.edges[appbFiveEmbedding (appb_d34_kind_length k hk) j] = (1,2) := by
      intro k hk j hj
      simp only [appbD34Kinds,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      all_goals fin_cases j
      all_goals try norm_num [Fin.lt_def] at hj
      all_goals rfl
    rw [hends k hk j hj]
    exact Sym2.eq_swap
  have hh := appb_incidence_sign_endpoints M _ _ _ he hne
  have hj3 : j < 3 := by omega
  simpa only [appbD34Signs,if_pos hj3] using hh

theorem appb_d34_boundary_cut_sign {M : Molecule V D} (k : AppbPatternKind) (hk : k ∈ appbD34Kinds)
    (r : AppbRealization M k.pattern) (j : Fin 3) :
    appbCutSign M r.removedAtoms (r.edge ((appbD34CutTriple k hk r).index j)).val =
      appbD34Signs k hk r (![2,3,4] j) := by
  let i := appbFiveEmbedding (appb_d34_kind_length k hk) (![2,3,4] j)
  have hh := appb_d34_cut_endpoint_table k hk r (![2,3,4] j)
  have hj : ¬(![2,3,4] j : Fin 5) < 2 := by fin_cases j <;> decide
  have hnot : r.vertex k.pattern.edges[i].2 ∉ r.removedAtoms := fun hm => hj (hh.2.mp hm)
  have he := appb_cutSign_eq_internal M r.removedAtoms (r.edge i).val
    (r.vertex k.pattern.edges[i].1) (r.vertex k.pattern.edges[i].2) (r.endpoints i) hh.1 hnot
  change appbCutSign M r.removedAtoms (r.edge i).val = _
  rw [he]
  have howner : k.pattern.edges[i].1 = if (![2,3,4] j : Fin 5) < 3 then 1 else 2 := by
    simp only [appbD34Kinds,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    all_goals fin_cases j <;> norm_num [i,appbFiveEmbedding,AppbPatternKind.pattern,finCongr,Fin.lt_def]
  rw [howner]
  rfl

theorem appb_d34_boundary_signs_not_all {M : Molecule V D} (k : AppbPatternKind) (hk : k ∈ appbD34Kinds)
    (r : AppbRealization M k.pattern) (hM : M.IsMolecule) (a : ℤˣ) :
    ¬∀ j : Fin 3,appbCutSign M r.removedAtoms (r.edge ((appbD34CutTriple k hk r).index j)).val = a := by
  let σ := appbD34Signs k hk r
  let e := appbFiveEmbedding (appb_d34_kind_length k hk)
  have ht : ∀ k ∈ appbD34Kinds,1 ∈ k.pattern.vertices ∧ 2 ∈ k.pattern.vertices := by decide
  have hfirst : ¬(σ 0 = a ∧ σ 1 = a ∧ σ 2 = a) := by
    rintro ⟨h0,h1,h2⟩
    apply appb_not_all_frame_signs r hM (r.vertex 1) (r.vertex_mem 1 (ht k hk).1)
      (appbD34Frame k hk r).index (appbD34Frame k hk r).incidence a
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  have hsecond (i : Fin 5) (hi : i < 2) : ¬(-σ i = a ∧ σ 3 = a ∧ σ 4 = a) := by
    rintro ⟨h0,h3,h4⟩
    let idx : Fin 3 ↪ Fin k.pattern.edges.length :=
      (⟨![i,3,4],by
        have hiv : i.val < 2 := hi
        fin_cases i
        all_goals try norm_num at hiv
        all_goals decide⟩ : Fin 3 ↪ Fin 5).trans e
    apply appb_not_all_frame_signs r hM (r.vertex 2) (r.vertex_mem 2 (ht k hk).2) idx (by
      intro j
      change appbIncidence M (r.vertex 2) (r.edge (e (![i,3,4] j))).val = 1
      rw [(appb_d34_incidence_table k hk r _).2]
      fin_cases j
      · change (if i = 2 then 0 else (1 : ℕ)) = 1
        have hh : i ≠ 2 := by omega
        rw [if_neg hh]
      · change (if (3 : Fin 5) = 2 then 0 else (1 : ℕ)) = 1
        decide
      · change (if (4 : Fin 5) = 2 then 0 else (1 : ℕ)) = 1
        decide) a
    intro j
    fin_cases j
    · change appbIncidenceSign M (r.vertex 2) (r.edge (e i)).val = a
      rw [appb_d34_internal_sign k hk r i hi]
      exact h0
    · exact h3
    · exact h4
  intro hall
  apply appb_triple_quad_boundary_signs σ a hfirst (hsecond 0 (by decide)) (hsecond 1 (by decide))
  have h0 := hall 0
  have h1 := hall 1
  have h2 := hall 2
  rw [appb_d34_boundary_cut_sign] at h0 h1 h2
  exact ⟨h0,h1,h2⟩

end WaveTurbulence.Mole
