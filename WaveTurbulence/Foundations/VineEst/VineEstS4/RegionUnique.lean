/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLRegionData

/-! # `CLRegionData` is a subsingleton (V5 Step 4 groundwork)

The slot labels of a CL region are forced by the incidence characterizations and the signs, so the kernel
`clRecenteredLocalKernel` does not depend on the choice of `CLRegionData` for a fixed `(G, U, a, b)`.  This justifies
building the twisted regions of TARGET `vineest` (sum over LF twists `G'`) by transport and choice.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.RegRed TTree

variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem regionData_subsingleton (D E : CLRegionData G S a b) : D = E := by
  have hex : D.excluded = E.excluded := by
    by_contra hne
    exact (D.upper D.excluded).mp ((E.upper _).mpr hne) rfl
  have hkp : D.kept = E.kept := by
    have h1 := (D.lower D.kept).mpr rfl
    exact (E.lower D.kept).mp h1
  have hpos : D.positive = E.positive := by
    by_contra hne
    -- D.positive lies in the complement of E.kept = {E.positive, E.negative}
    have h1 : D.positive ≠ D.kept := by
      intro h
      exact (by simpa using (D.lower_excluded D.positive).mpr (Or.inl rfl) h : False)
    have h2 : D.positive = E.negative := by
      have := (E.lower_excluded D.positive).mp (hkp ▸ h1)
      rcases this with h | h
      · exact absurd h hne
      · exact h
    have h3 := D.positive_sign
    rw [h2] at h3
    have := E.negative_sign
    rw [h3] at this
    exact absurd this (by decide)
  have hneg : D.negative = E.negative := by
    have h1 : D.negative ≠ D.kept := by
      intro h
      exact (by simpa using (D.lower_excluded D.negative).mpr (Or.inr rfl) h : False)
    rcases (E.lower_excluded D.negative).mp (hkp ▸ h1) with h | h
    · exfalso
      exact D.distinct (hpos.trans h.symm)
    · exact h
  rcases D with ⟨⟨e1, k1, a1, a2, a3, a4⟩, p1, p2, p3, p4, p5, p6, p7⟩
  rcases E with ⟨⟨e2, k2, b1, b2, b3, b4⟩, q1, q2, q3, q4, q5, q6, q7⟩
  simp only at hex hkp hpos hneg
  subst hex hkp hpos hneg
  rfl

end WaveTurbulence.VineEstS4
