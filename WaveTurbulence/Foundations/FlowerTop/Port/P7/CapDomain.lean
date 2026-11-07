/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapPhase
/-! FLOWER-P7: the time domain of the cap with both roots pinned at `t` and caps `t`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

/-- The designated nodes of the pinned couple: both roots at time `t`. -/
def pinRoots {T : Fin (2 * 3) → TTree} (t : ℝ) : GBranch (capTree T) → Option ℝ :=
  fun b => if b.1.2 = [] then some t else none

theorem pinRoots_root {T : Fin (2 * 3) → TTree} (t : ℝ) (j : Fin 2) :
    pinRoots (T := T) t (rootBranch T j) = some t := by
  simp [pinRoots, rootBranch]

theorem pinRoots_lift {T : Fin (2 * 3) → TTree} (t : ℝ) (a : GBranch T) :
    pinRoots (T := T) t (liftBranch a) = none := by
  simp [pinRoots, liftBranch, liftAddr]

theorem isChildOf_lift {T : Fin (2 * 3) → TTree} (a' a : GBranch T) :
    (liftBranch a').IsChildOf (liftBranch a) ↔ a'.IsChildOf a := by
  constructor
  · rintro ⟨h1, i, h2⟩
    simp only [liftBranch, liftAddr, List.cons_append, List.cons.injEq] at h1 h2
    obtain ⟨h2a, h2b⟩ := h2
    refine ⟨?_, i, h2b⟩
    rw [← idx_jOf_iOf a'.1.1, ← idx_jOf_iOf a.1.1, h1, h2a]
  · rintro ⟨h1, i, h2⟩
    refine ⟨?_, i, ?_⟩
    · simp [liftBranch, liftAddr, h1]
    · simp [liftBranch, liftAddr, h1, h2]

theorem exists_child_lift {T : Fin (2 * 3) → TTree} (b' : GBranch (capTree T)) (b : GBranch (capTree T))
    (h : b'.IsChildOf b) : ∃ a' : GBranch T, liftBranch a' = b' := by
  obtain ⟨_, i, hi⟩ := h
  apply exists_liftBranch
  rw [hi]; simp

theorem domain_cap (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ)
    (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (σ : GBranch LG.garden.tree → ℝ) :
    extendCap LG.garden.tree t σ ∈
        kDomainFix (capLayered LG hsig p hp) (fun _ => t) (pinRoots (T := LG.garden.tree) t) ↔
      σ ∈ kDomainFix LG (fun _ => t) (fun _ => none) := by
  constructor
  · intro hQ a
    have h := hQ (liftBranch a)
    rw [pinRoots_lift] at h
    refine ⟨fun _ => ?_, fun a' ha' _ => ?_⟩
    · have h1 := (h.1 rfl)
      rw [liftBranch_toNode, capLayered_layer_lift, extendCap_lift] at h1
      exact h1
    · have h2 := h.2 (liftBranch a') ((isChildOf_lift a' a).2 ha') (Or.inl (pinRoots_lift t a'))
      rwa [extendCap_lift, extendCap_lift] at h2
  · intro hG b
    obtain ⟨y, rfl⟩ := (capBranchEquiv LG.garden.tree).surjective b
    rcases y with j | a
    · rw [capBranchEquiv_inl]
      refine ⟨fun h => ?_, fun b' hb' _ => ?_⟩
      · rw [pinRoots_root] at h
        exact absurd h (by simp)
      · obtain ⟨a', rfl⟩ := exists_child_lift b' _ hb'
        rw [extendCap_root, extendCap_lift]
        exact ((hG a').1 rfl).2.2.2
    · rw [capBranchEquiv_inr]
      refine ⟨fun _ => ?_, fun b' hb' _ => ?_⟩
      · have h1 := (hG a).1 rfl
        rw [liftBranch_toNode, capLayered_layer_lift, extendCap_lift]
        exact h1
      · obtain ⟨a', rfl⟩ := exists_child_lift b' _ hb'
        rw [extendCap_lift, extendCap_lift]
        exact (hG a).2 a' ((isChildOf_lift a' a).1 hb') (Or.inl rfl)

end WaveTurbulence.FlowerP7
