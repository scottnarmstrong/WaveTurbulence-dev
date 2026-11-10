/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Ex2
public import WaveTurbulence.Foundations.FinalCount.G3TriBridge
public import WaveTurbulence.Foundations.FinalCount.GhostMain4
/-! **FINALCOUNT-G3: bridges for the charged ghost triangle bound (part 1).**  Graph-level facts used to feed G2-GHOST's
`triangle_excess_ghost`: an all-degree-`2` triangle of `α` atoms contradicts `CompBeta` (`hnot3`), `alphaLabels = triAlphaNew`
(through `isA0_iff`, `isA1_iff`), and `labelProd = ghostCharge`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} {d : ℕ}

/-- If all three triangle atoms have degree `≤ 2`, the triangle is a closed atom set of `M`. -/
theorem blobM_closed {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (T : TriData M)
    (hd : ∀ j, M.deg (T.t j) ≤ 2) : IsClosedSet M (Finset.univ.image T.t) := by
  intro x hx
  rw [Finset.mem_image] at hx ⊢
  obtain ⟨j, -, hj⟩ := hx
  have hx' : x = T.a j ∨ x = T.b j := T.dart_ab_of_deg j (hd j) hj.symm
  rcases hx' with rfl | rfl
  · refine ⟨j - 1, Finset.mem_univ _, ?_⟩
    have hm : M.mate (T.a j) = T.b (j - 1) := by
      have := T.mate_a (j - 1); rwa [sub_add_cancel] at this
    rw [hm]; exact (T.atom_b _).symm
  · refine ⟨j + 1, Finset.mem_univ _, ?_⟩
    rw [T.mate_b]; exact (T.atom_a _).symm

/-- **`hnot3`**: the three triangle atoms are not all `α`-atoms of degree `≤ 2` (that triangle would be a component without a
`β`-atom and without an imperfect atom). -/
theorem not_all_alpha_of_compBeta {s : St.{u} V D₀} (hCB : CompBeta s) (hCl : Clean s) (T : TriData s.M)
    (hd : ∀ j, s.M.deg (T.t j) ≤ 2) (hα : ∀ j, ∃ R k, s.cls (T.t j) = .alpha R k) : False := by
  obtain ⟨b, hb, hsc, hcase⟩ := hCB (T.t 0) (T.t_mem 0) (hCl _ (T.t_mem 0))
  have hbm := (blobM_closed T hd).sc (Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩) hsc
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hbm
  obtain ⟨R, k, hc⟩ := hα j
  have h2 := tri_deg_ge_two T j
  have h3 := hd j
  rcases hcase with h | h
  · rw [hc] at h; cases h
  · apply h; unfold contrib; rw [hc]; simp only [Cls.base]; omega

/-- The label `Q_g` of an `α`-ghost (any value for a non-`α` atom). -/
noncomputable def ghostQ (h : HSt V D₀) (T : TriData h.s.M) (j : Fin 3) : ℝ :=
  match h.s.cls (T.t j) with
  | .alpha R _ => R
  | _ => 1

/-- The label `κ_g` of an `α`-ghost. -/
noncomputable def ghostK (h : HSt V D₀) (T : TriData h.s.M) (j : Fin 3) : ℕ :=
  match h.s.cls (T.t j) with
  | .alpha _ k => k
  | _ => 0

theorem ghostQ_eq {h : HSt V D₀} {T : TriData h.s.M} {j : Fin 3} {R : ℝ} {k : ℕ} (hc : h.s.cls (T.t j) = .alpha R k) :
    ghostQ h T j = R := by simp [ghostQ, hc]

theorem labelProd_eq_ghostCharge (L γ η : ℝ) (h : HSt V D₀) (T : TriData h.s.M) :
    labelProd L γ η (alphaGhostList h T) =
      ghostCharge L γ η (fun j => ∃ R k, h.s.cls (T.t j) = .alpha R k) (ghostQ h T) (ghostK h T) := by
  unfold labelProd alphaGhostList ghostCharge
  rw [Finset.prod_filter, Fin.prod_univ_three]
  simp only [List.finRange_succ, List.finRange_zero, List.filterMap_cons]
  rcases h0 : h.s.cls (T.t 0) with _ | ⟨R0, k0⟩ | _ | _ <;>
  rcases h1 : h.s.cls (T.t 1) with _ | ⟨R1, k1⟩ | _ | _ <;>
  rcases h2 : h.s.cls (T.t 2) with _ | ⟨R2, k2⟩ | _ | _ <;>
  simp [ghostQ, ghostK, h0, h1, h2, mul_assoc]

/-- **`alphaLabels = triAlphaNew`**: G2's list of new `α`-atoms of a triangle step (with the labels of the ghost positions
replaced by `0`, which is irrelevant since a ghost never creates an `α`-atom) is G3's. -/
theorem alphaLabels_eq_triAlphaNew (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
    (hgd : ∀ j, h.s.cls (T.t j) ≠ .eps → h.s.M.deg (T.t j) ≤ 2) :
    T.alphaLabels (Q 0) (Q 1) (if h.s.cls (T.t 0) = .eps then kp 0 else 0)
      (if h.s.cls (T.t 1) = .eps then kp 1 else 0) = triAlphaNew h T Q kp := by
  unfold TriData.alphaLabels triAlphaNew
  have hA0 := isA0_iff T
  have hA1 := isA1_iff T
  have c0 : (Fin.castSucc (0 : Fin 2) : Fin 3) = 0 := rfl
  have c1 : (Fin.castSucc (1 : Fin 2) : Fin 3) = 1 := rfl
  have hl : List.finRange 2 = [0, 1] := rfl
  have n0 : ¬ T.IsA0 ↔ ¬ (T.kept.SameComponent (T.f 0) (T.f 2) ∨ T.kept.SameComponent (T.f 0) (T.f 1)) := not_congr hA0
  rw [hl]
  simp only [List.filterMap_cons, List.filterMap_nil, c0, c1, hA0, hA1]
  have n1 : ¬ T.IsA1 ↔ ¬ T.kept.SameComponent (T.f 1) (T.f 2) := not_congr hA1
  by_cases e0 : h.s.cls (T.t 0) = .eps <;> by_cases e1 : h.s.cls (T.t 1) = .eps
  · simp [e0, e1, triCls_f0, triCls_f1]
    split_ifs <;> simp
  · have g1 := n1.1 (T.not_isA1_of_ghost1 (hgd 1 e1))
    simp [e0, e1, triCls_f0]
    split_ifs <;> simp
  · have g0 := n0.1 (T.not_isA0_of_ghost (hgd 0 e0))
    simp [e0, e1, triCls_f1]
    split_ifs <;> simp
  · have g1 := n1.1 (T.not_isA1_of_ghost1 (hgd 1 e1))
    have g0 := n0.1 (T.not_isA0_of_ghost (hgd 0 e0))
    simp [e0, e1]
    tauto

end WaveTurbulence.FinalCountG3
