/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase2A
public import WaveTurbulence.Foundations.FinalCount.AsmTriBridge
/-! **Ghost assembly, Phase 2 (B): the new critical atoms of a triangle step** (design: `CHAIN-DESIGN.md`).

* `TRpt`: pointwise (T-TR) of two vectors; its failure is the cone of aperture `θ₀ = L^{-6η}` (`inCone_of_not_TRpt`);
* `nbrAt`: the neighbour at the `i`-th dart of an atom; every neighbour of a degree-2 atom is one of `nbrAt · 0`,
  `nbrAt · 1` (`nbrAt_cover`);
* `critA_f_cases`: a critical atom of the post state that is not a survivor is `f 0` or `f 1`;
* `critA_f0`/`critA_f1`: a critical `f j` comes from an `ε` atom `t j` with `IsA j`, `kp j = 0` and a critical label. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- Pointwise (T-TR) of two vectors (Gram form, `θ₀² = L^{-12η}`). -/
def TRpt (L η : ℝ) (r c : Mom d) : Prop :=
  L ^ (-12 * η) * (‖r‖ ^ 2 * ‖c‖ ^ 2) ≤ ‖r‖ ^ 2 * ‖c‖ ^ 2 - inner ℝ r c ^ 2

theorem inCone_of_not_TRpt {L η : ℝ} (hL : 0 < L) {r c : Mom d} (h : ¬ TRpt L η r c) :
    InCone (L ^ (-6 * η)) r c := by
  unfold TRpt at h; unfold InCone
  rw [Tri.rpow_neg6_sq hL]
  push Not at h
  linarith

theorem TRpt.symm {L η : ℝ} {r c : Mom d} (h : TRpt L η r c) : TRpt L η c r := by
  unfold TRpt at h ⊢
  rw [real_inner_comm]
  linarith [mul_comm (‖r‖ ^ 2) (‖c‖ ^ 2)]

theorem TRpt.neg_left {L η : ℝ} {r c : Mom d} (h : TRpt L η r c) : TRpt L η (-r) c := by
  unfold TRpt at h ⊢; rwa [norm_neg, inner_neg_left, neg_sq]

theorem TRpt.neg_right {L η : ℝ} {r c : Mom d} (h : TRpt L η r c) : TRpt L η r (-c) := by
  unfold TRpt at h ⊢; rwa [norm_neg, inner_neg_right, neg_sq]

theorem inCone_neg_ctr (θ : ℝ) (r c : Mom d) : InCone θ r (-c) ↔ InCone θ r c := by
  unfold InCone; rw [norm_neg, inner_neg_right, neg_sq]

theorem inCone_pm_ctr {θ : ℝ} {r c c' : Mom d} (hc : c' = c ∨ c' = -c) (h : InCone θ r c) : InCone θ r c' := by
  rcases hc with rfl | rfl
  · exact h
  · exact (inCone_neg_ctr θ r c).2 h

/-- The neighbour at the `i`-th dart of `v` (in the order of `toList`). -/
noncomputable def nbrAt (h' : HSt V D₀) (v : V) (i : Fin 2) : Option V :=
  ((h'.s.M.dartsAt v).toList[i.val]?).map (fun x => h'.s.M.atom (h'.s.M.mate x))

theorem nbrAt_cover {h' : HSt V D₀} {v y : V} (hdeg : h'.s.M.deg v = 2) (hadj : h'.s.M.Adj v y) :
    ∃ i, nbrAt h' v i = some y := by
  obtain ⟨x, hx, hy⟩ := hadj
  have hxm : x ∈ (h'.s.M.dartsAt v).toList := by
    rw [Finset.mem_toList]; simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]; exact hx
  obtain ⟨n, hn, hxn⟩ := List.getElem_of_mem hxm
  have hlen : (h'.s.M.dartsAt v).toList.length = 2 := by rw [Finset.length_toList]; exact hdeg
  refine ⟨⟨n, by omega⟩, ?_⟩
  unfold nbrAt
  rw [List.getElem?_eq_getElem hn, hxn]
  simp [hy]

variable (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ) (hcl : PClosed T.kept (triKeep h.s T))

/-- A critical atom of the post state that is not a survivor is `f 0` or `f 1`. -/
theorem critA_f_cases {L γ η : ℝ} {x : V} (hx : IsCritA L γ η (h.triPost T Q kp hcl) x)
    (hX : x ∉ triSurv h T Q kp hcl) : x = T.f 0 ∨ x = T.f 1 := by
  have hmem := hx.1
  have : ∃ j, x = T.f j := by
    by_contra hn
    push Not at hn
    exact hX ⟨hmem, hn⟩
  obtain ⟨j, rfl⟩ := this
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd hx (not_critA_f2 h T Q kp hcl)

/-- A critical `f 0`: `t 0` was `ε`, `IsA0`, `kp 0 = 0`, critical `Q 0`. -/
theorem critA_f0 {L γ η : ℝ} (hx : IsCritA L γ η (h.triPost T Q kp hcl) (T.f 0)) :
    h.s.cls (T.t 0) = .eps ∧ T.IsA0 ∧ kp 0 = 0 ∧ Crit L γ η (Q 0) := by
  obtain ⟨-, -, R, hR, hcr⟩ := hx
  have hc : (h.triPost T Q kp hcl).s.cls (T.f 0) = triCls h.s T Q kp (T.f 0) := rfl
  rw [hc] at hR
  have h02 : T.f 0 ≠ T.f 2 := T.f_ne (by decide)
  unfold triCls at hR
  simp only [h02, ite_false, ite_true] at hR
  split_ifs at hR with he hsc
  · obtain ⟨hQ, hk⟩ := Cls.alpha.inj hR
    exact ⟨he, (FinalCountAsm.isA0_iff T).2 hsc, hk, by rw [hQ]; exact hcr⟩

/-- A critical `f 1`: `t 1` was `ε`, `IsA1`, `kp 1 = 0`, critical `Q 1`. -/
theorem critA_f1 {L γ η : ℝ} (hx : IsCritA L γ η (h.triPost T Q kp hcl) (T.f 1)) :
    h.s.cls (T.t 1) = .eps ∧ T.IsA1 ∧ kp 1 = 0 ∧ Crit L γ η (Q 1) := by
  obtain ⟨-, -, R, hR, hcr⟩ := hx
  have hc : (h.triPost T Q kp hcl).s.cls (T.f 1) = triCls h.s T Q kp (T.f 1) := rfl
  rw [hc] at hR
  have h12 : T.f 1 ≠ T.f 2 := T.f_ne (by decide)
  have h10 : T.f 1 ≠ T.f 0 := T.f_ne (by decide)
  unfold triCls at hR
  simp only [h12, h10, ite_false, ite_true] at hR
  split_ifs at hR with he hsc
  · obtain ⟨hQ, hk⟩ := Cls.alpha.inj hR
    exact ⟨he, (FinalCountAsm.isA1_iff T).2 hsc, hk, by rw [hQ]; exact hcr⟩

end WaveTurbulence.GammaLow.FinalCount.Ghost
