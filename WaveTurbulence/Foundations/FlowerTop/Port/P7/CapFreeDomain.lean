/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapFreePhase
/-! FLOWER-P7: the time domain of the cap with free root times `s`: it is the root domain times the domain of the six
trees with the caps `s_{j(c)}`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

/-- The domain of the two root times (layer `p`, below the cap `t`). -/
def rootDom (p : ℕ) (t : ℝ) : Set (Fin 2 → ℝ) :=
  {s | ∀ j, (p : ℝ) < s j ∧ s j < p + 1 ∧ 0 < s j ∧ s j < t}

theorem domain_capS (LG : LayeredGarden (2 * 3)) (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ)
    (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (s : Fin 2 → ℝ) (σ : GBranch LG.garden.tree → ℝ) :
    extendCapS LG.garden.tree s σ ∈
        kDomainFix (capLayered LG hsig p hp) (fun _ => t) (fun _ => none) ↔
      s ∈ rootDom p t ∧ σ ∈ kDomainFix LG (fun b => s (jOf b.1.1)) (fun _ => none) := by
  constructor
  · intro hQ
    refine ⟨fun j => ?_, fun a => ⟨fun _ => ?_, fun a' ha' _ => ?_⟩⟩
    · have h := (hQ (rootBranch LG.garden.tree j)).1 rfl
      rw [capLayered_layer_root, extendCapS_root] at h
      exact h
    · have h := (hQ (liftBranch a)).1 rfl
      rw [liftBranch_toNode, capLayered_layer_lift, extendCapS_lift] at h
      refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
      have hne : (liftBranch a).1.2 ≠ [] := by simp [liftBranch, liftAddr]
      obtain ⟨n, hn⟩ : ∃ n, (liftBranch a).1.2.length = n + 1 := by
        refine ⟨(liftBranch a).1.2.length - 1, ?_⟩
        have := List.length_pos_iff.2 hne
        omega
      obtain ⟨r, hr1, hr2, hr3⟩ := domain_lt_root _ _ _ hQ n (liftBranch a) hn
      have hrr : r = rootBranch LG.garden.tree (jOf a.1.1) :=
        Subtype.ext (Prod.ext (by simpa [liftBranch, liftAddr, rootBranch] using hr1) hr2)
      rw [hrr, extendCapS_root, extendCapS_lift] at hr3
      exact hr3
    · have h2 := (hQ (liftBranch a)).2 (liftBranch a') ((isChildOf_lift a' a).2 ha') (Or.inl rfl)
      rwa [extendCapS_lift, extendCapS_lift] at h2
  · rintro ⟨hs, hσ⟩ b
    obtain ⟨y, rfl⟩ := (capBranchEquiv LG.garden.tree).surjective b
    rcases y with j | a
    · rw [capBranchEquiv_inl]
      refine ⟨fun _ => ?_, fun b' hb' _ => ?_⟩
      · rw [capLayered_layer_root, extendCapS_root]
        exact hs j
      · obtain ⟨a', rfl⟩ := exists_child_lift b' _ hb'
        rw [extendCapS_root, extendCapS_lift]
        have hj : jOf a'.1.1 = j := by
          have := hb'.1
          simpa [liftBranch, liftAddr, rootBranch] using this
        have h' : σ a' < s (jOf a'.1.1) := ((hσ a').1 rfl).2.2.2
        rw [hj] at h'
        exact h'
    · rw [capBranchEquiv_inr]
      refine ⟨fun _ => ?_, fun b' hb' _ => ?_⟩
      · have h1 := (hσ a).1 rfl
        rw [liftBranch_toNode, capLayered_layer_lift, extendCapS_lift]
        exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.trans (hs (jOf a.1.1)).2.2.2⟩
      · obtain ⟨a', rfl⟩ := exists_child_lift b' _ hb'
        rw [extendCapS_lift, extendCapS_lift]
        exact (hσ a).2 a' ((isChildOf_lift a' a).1 hb') (Or.inl rfl)

end WaveTurbulence.FlowerP7
