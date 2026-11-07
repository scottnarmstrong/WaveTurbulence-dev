/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CropAddresses

/-! # Prefix-closed pruning and the actual exterior cut paths -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree

theorem RouteKept.last {keep : Path → Bool} {p : Path} (h : RouteKept keep p) : keep p = true := by
  induction p generalizing keep with
  | nil => exact h
  | cons i p ih => exact ih h.2

theorem routeKept_iff (keep : Path → Bool)
    (hc : ∀ p q : Path, q.IsPrefix p → keep p = true → keep q = true) (p : Path) :
    RouteKept keep p ↔ keep p = true := by
  constructor
  · exact RouteKept.last
  · intro hp
    induction p generalizing keep with
    | nil => exact hp
    | cons i p ih =>
      refine ⟨hc (i::p) [] List.nil_prefix hp,?_⟩
      apply ih (fun q => keep (i::q)) ?_ hp
      intro p q hq hkeep
      exact hc (i::p) (i::q) (List.cons_prefix_cons.mpr ⟨rfl,hq⟩) hkeep

noncomputable def avoidCutPaths (root : Path) (cuts : Finset Path) (p : Path) : Bool := by
  classical
  exact decide (∀ c ∈ cuts, ¬ c.IsPrefix (root++p))

theorem avoidCutPaths_prefix (root : Path) (cuts : Finset Path) (p q : Path)
    (hq : q.IsPrefix p) (hp : avoidCutPaths root cuts p = true) : avoidCutPaths root cuts q = true := by
  classical
  simp only [avoidCutPaths,decide_eq_true_eq] at hp ⊢
  intro c hc hcut
  apply hp c hc
  apply hcut.trans
  obtain ⟨suffix,hsuffix⟩ := hq
  exact ⟨suffix,by rw [List.append_assoc,hsuffix]⟩

/-- An exact branching-address characterization for cutting fixed exterior
subtrees. No arbitrary region or tree-shape equivalence is a premise. -/
theorem cropTree_avoidCuts_branching_iff (T : TTree) (root : Path) (cuts : Finset Path) (p : Path) :
    p ∈ (cropTree T (avoidCutPaths root cuts)).branching ↔
      p ∈ T.branching ∧ ∀ c ∈ cuts, ¬ c.IsPrefix (root++p) := by
  classical
  rw [cropTree_branching_iff,routeKept_iff _ (avoidCutPaths_prefix root cuts)]
  simp only [avoidCutPaths,decide_eq_true_eq]

end WaveTurbulence.VineEstS2
