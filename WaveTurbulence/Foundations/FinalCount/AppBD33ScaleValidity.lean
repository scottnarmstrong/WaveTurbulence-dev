/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBValidLinkScales
public import WaveTurbulence.Foundations.FinalCount.AppBLinkPresentation
public import WaveTurbulence.Foundations.FinalCount.AppBD33LinkFactors
public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceGap
public import WaveTurbulence.Foundations.FinalCount.AppBResidualLabels
import Mathlib.Tactic

/-! # The normal double-pair scale premise follows from physical link validity -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset Set
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_d33_link_presentation (M : Molecule V D) (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hlink : AppbLink M (appbD33LinkAtoms r)) :
    ∃ u v : Fin 2 → V,Degen.SourceLadder (m := 1) M u v ∧
      Molecule.ladderAtoms u v = appbD33LinkAtoms r ∧
      u 0 = r.vertex 1 ∧ v 0 = r.vertex 2 ∧ u 1 = r.vertex 3 ∧ v 1 = r.vertex 4 := by
  obtain ⟨u,v,hL,hS,h0⟩ := hlink.presentation_at (a := r.vertex 1) (by simp [appbD33LinkAtoms])
  have h12 : u 0 ≠ r.vertex 2 := by
    rw [h0]
    exact (r.vertex_eq_iff 1 2 (by decide) (by decide)).not.mpr (by decide)
  have hdouble : M.bondsBetween (u 0) (r.vertex 2) = 2 := by
    rw [h0]
    exact appb_d33_internal_multiplicity M r
  have h2 : v 0 = r.vertex 2 := (Degen.sourceLadder_double_partner_eq M
    (fun _ hx => deg_le_four M hM hx) hL 0 h12 hdouble).symm
  have hu : M.bondsBetween (r.vertex 1) (u 1) = 1 := by
    have hh := (hL.2.2.2.2 (0 : Fin 1)).1
    change M.bondsBetween (u 0) (u 1) = 1 at hh
    rwa [h0] at hh
  have hv : M.bondsBetween (r.vertex 2) (v 1) = 1 := by
    have hh := (hL.2.2.2.2 (0 : Fin 1)).2.1
    change M.bondsBetween (v 0) (v 1) = 1 at hh
    rwa [h2] at hh
  exact ⟨u,v,hL,hS,h0,h2,appb_d33_single_neighbor_1 M r _ hu,
    appb_d33_single_neighbor_2 M r _ hv⟩

theorem appb_d33_lostScale_range {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) {d : ℕ} {L c : ℝ} {w : Mom d}
    {Adm : (D → (Fin d → ℤ)) → Prop} {scales : Finset V → ℝ}
    (h : AppbValidLinkScales M L w Adm c scales) :
    appbD33LostScale r scales = 0 ∨ appbD33LostScale r scales ∈ Icc L⁻¹ 1 := by
  classical
  unfold appbD33LostScale
  split_ifs with hlink
  · exact h.1 _ ((mem_appbLinks _ _).mp hlink)
  · exact Or.inl rfl

theorem appb_d33_lostScale_gap {M : Molecule V D} (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.d33.pattern) {d : ℕ} {L c : ℝ} {w : Mom d}
    {Adm : (D → (Fin d → ℤ)) → Prop} {scales : Finset V → ℝ}
    (h : AppbValidLinkScales M L w Adm c scales)
    (κ : D → (Fin d → ℤ)) (hκ : Adm κ) (hm : ∀ x,κ (M.mate x) = κ x)
    (hp : 0 < appbD33LostScale r scales) :
    c⁻¹*appbD33LostScale r scales ≤
      ‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val-
        Molecule.kvec L w κ (r.edge ⟨3,by decide⟩).val‖ := by
  classical
  have hlink : appbD33LinkAtoms r ∈ appbLinks M := by
    by_contra hn
    simp only [appbD33LostScale,hn,ite_false] at hp
    linarith only [hp]
  have he : appbD33LostScale r scales = scales (appbD33LinkAtoms r) := by
    simp only [appbD33LostScale,hlink,ite_true]
  rw [he] at hp ⊢
  obtain ⟨u,v,hL,hS,h1,h2,h3,h4⟩ := appb_d33_link_presentation M hM r ((mem_appbLinks _ _).mp hlink)
  let x := (r.edge ⟨2,by decide⟩).val
  let y := (r.edge ⟨3,by decide⟩).val
  let x' := appbIncidenceDart M (r.vertex 1) x
  let y' := appbIncidenceDart M (r.vertex 2) y
  have hx : M.ends x' = s(u 0,u 1) ∧ M.atom x' = u 0 := by
    rw [h1,h3]
    have hends : M.ends x = s(r.vertex 1,r.vertex 3) := r.endpoints ⟨2,by decide⟩
    have hne : r.vertex 1 ≠ r.vertex 3 := (r.vertex_eq_iff 1 3 (by decide) (by decide)).not.mpr (by decide)
    rcases Sym2.eq_iff.mp hends with hh | hh
    · simp only [x',appbIncidenceDart,hh.1,ite_true]
      exact ⟨hends,trivial⟩
    · simp only [x',appbIncidenceDart,hh.1,hne.symm,ite_false,Molecule.ends,M.mate_mate,hh.2]
      exact ⟨trivial,trivial⟩
  have hy : M.ends y' = s(v 0,v 1) ∧ M.atom y' = v 0 := by
    rw [h2,h4]
    have hends : M.ends y = s(r.vertex 2,r.vertex 4) := r.endpoints ⟨3,by decide⟩
    have hne : r.vertex 2 ≠ r.vertex 4 := (r.vertex_eq_iff 2 4 (by decide) (by decide)).not.mpr (by decide)
    rcases Sym2.eq_iff.mp hends with hh | hh
    · simp only [y',appbIncidenceDart,hh.1,ite_true]
      exact ⟨hends,trivial⟩
    · simp only [y',appbIncidenceDart,hh.1,hne.symm,ite_false,Molecule.ends,M.mate_mate,hh.2]
      exact ⟨trivial,trivial⟩
  have hlabels (a : V) (z : D) : Molecule.kvec L w κ (appbIncidenceDart M a z) = Molecule.kvec L w κ z := by
    unfold appbIncidenceDart
    split_ifs <;> simp only [Molecule.kvec,hm]
  have hg : M.IsLadderGap L w κ u v (by decide) (Molecule.kvec L w κ x-Molecule.kvec L w κ y) := by
    refine ⟨x',y',hx.1,hy.1,hx.2,hy.2,?_⟩
    simp only [Molecule.gapAt,x',y',hlabels]
  simpa only [hS] using h.2 u v hL κ hκ _ hg (hS ▸ hp)

end WaveTurbulence.Mole
