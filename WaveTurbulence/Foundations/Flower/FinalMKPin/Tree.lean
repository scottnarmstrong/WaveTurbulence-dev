/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPin.Domain
import Mathlib.Tactic

/-! # C4a PIN-FOURIER: the contracted relation `chF` is a forest

The generic engine (`class_bound`) needs a depth that decreases along `chF` and at most one `chF`-parent per clock.
The depth `depF a` is the depth of the top branch of the fibre of `a`. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKPin
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.Flower.FinalMKDefs
open MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w : ℕ} {G : Garden w}
variable {fix : GBranch G.tree → Option ℝ} {face : GBranch G.tree → Option (GBranch G.tree)}

/-- The depth of the top branch of a fibre. -/
noncomputable def depF (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (a : Iv fix face) : ℕ :=
  if ∃ x, face x = some a.1 ∧ a.1.IsChildOf x then a.1.1.2.length - 1 else a.1.1.2.length

theorem isChildOf_len {a p : GBranch G.tree} (h : a.IsChildOf p) : a.1.2.length = p.1.2.length + 1 := by
  obtain ⟨_, i, hi⟩ := h
  rw [hi]; simp

/-- Two unpinned branches on one clock: equal, or a substituted pair. -/
theorem FaceOK.repV_eq_cases (hF : FaceOK fix face) {v v' : GBranch G.tree} (_hv : fix v = none)
    (_hv' : fix v' = none) (h : repV face v = repV face v') :
    v = v' ∨ face v = some v' ∨ face v' = some v := by
  rcases hg : face v with _ | x <;> rcases hk : face v' with _ | y
  · rw [repV_of_none hg, repV_of_none hk] at h; exact Or.inl h
  · rw [repV_of_none hg, repV_of_some hk] at h; exact Or.inr (Or.inr (by rw [h]))
  · rw [repV_of_some hg, repV_of_none hk] at h; exact Or.inr (Or.inl (by rw [h]))
  · rw [repV_of_some hg, repV_of_some hk] at h
    subst h
    have h1 : v.1.1 = x.1.1 := by
      rcases (hF.recip v x hg).2.2.2 with hc | hc
      · exact hc.1
      · exact hc.1.symm
    have h2 : v'.1.1 = x.1.1 := by
      rcases (hF.recip v' x hk).2.2.2 with hc | hc
      · exact hc.1
      · exact hc.1.symm
    exact Or.inl (hF.uniq v v' (by simp [hg]) (by simp [hk]) (h1.trans h2.symm))

theorem chF_huniq (hF : FaceOK fix face) (a b b' : Iv fix face) (h : chF fix face a b) (h' : chF fix face a b') :
    b = b' := by
  obtain ⟨hne, v, u, hch, hv, hu, hva, hub⟩ := h
  obtain ⟨hne', v', u', hch', hv', hu', hva', hub'⟩ := h'
  rcases hF.repV_eq_cases hv hv' (hva.trans hva'.symm) with e | e | e
  · subst e
    have := isChildOf_unique hch hch'
    subst this
    exact Subtype.ext (hub.symm.trans hub')
  · -- `face v = some v'`: `v' = a`
    exfalso
    have hv'a : v' = a.1 := by rw [← hva, repV_of_some e]
    rcases (hF.recip v v' e).2.2.2 with hc | hc
    · have := isChildOf_unique hch hc
      subst this
      exact hne (Subtype.ext (by rw [← hub, ← hv'a, repV_of_none (hF.recip v u e).2.2.1]))
    · have := isChildOf_unique hch' hc
      subst this
      exact hne' (Subtype.ext (by rw [← hub', hva]))
  · exfalso
    have hva' : v = a.1 := by rw [← hva', repV_of_some e]
    rcases (hF.recip v' v e).2.2.2 with hc | hc
    · have := isChildOf_unique hch' hc
      subst this
      exact hne' (Subtype.ext (by rw [← hub', ← hva', repV_of_none (hF.recip v' u' e).2.2.1]))
    · have := isChildOf_unique hch hc
      subst this
      exact hne (Subtype.ext (by rw [← hub, hva']))

theorem chF_hdep (hF : FaceOK fix face) (a b : Iv fix face) (h : chF fix face a b) : depF fix face b < depF fix face a := by
  obtain ⟨hne, v, u, hch, hv, hu, hva, hub⟩ := h
  have hlen := isChildOf_len hch
  -- the depth of `a` is that of `v`
  have ha : depF fix face a = v.1.2.length := by
    unfold depF
    rcases hg : face v with _ | y
    · rw [repV_of_none hg] at hva
      subst hva
      rw [if_neg]
      rintro ⟨x, hx, hcx⟩
      have := isChildOf_unique hch hcx
      subst this
      exact hne (Subtype.ext (by rw [← hub, repV_of_some hx]))
    · rw [repV_of_some hg] at hva
      rcases (hF.recip v y hg).2.2.2 with hc | hc
      · exfalso
        have e : u = y := isChildOf_unique hch hc
        exact hne (Subtype.ext (by rw [← hub, e, repV_of_none (hF.recip v y hg).2.2.1, hva]))
      · rw [← hva, if_pos ⟨v, hg, hc⟩, isChildOf_len hc]; omega
  have hb : depF fix face b ≤ u.1.2.length := by
    unfold depF
    rcases hk : face u with _ | y
    · rw [repV_of_none hk] at hub
      subst hub
      split_ifs <;> omega
    · rw [repV_of_some hk] at hub
      rw [← hub]
      rcases (hF.recip u y hk).2.2.2 with hc | hc
      · have := isChildOf_len hc
        split_ifs <;> omega
      · rw [if_pos ⟨u, hk, hc⟩, isChildOf_len hc]; omega
  omega

end WaveTurbulence.Flower.FinalMKPin
