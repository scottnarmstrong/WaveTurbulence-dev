/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.NoCutVertex

/-!
# N2 Lemma 1.14(a): a sub-object is all-in or all-out of a 2-cut rung

* `IsSubObjU.deg_induce_of_inner`: a non-joint atom of a sub-object has degree `4` inside `E(U)`;
* `IsSubObjU.closed_of_inner`: and keeps all its bonds inside `S(U)`;
* `phiAllInOut_holds : PhiAllInOutStatement` (N2 Lemma 1.14(a)).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

theorem IsSubObjU.atoms_subset {G : UMultigraph V} {U : SubObj V} (hU : IsSubObjU G U) : U.atoms ⊆ G.verts :=
  hU.1.subset

theorem IsSubObjU.k₁_mem {G : UMultigraph V} {U : SubObj V} (hU : IsSubObjU G U) : U.k₁ ∈ U.atoms := by
  have := hU.2.2.1; rwa [SubObj.core_verts] at this

theorem IsSubObjU.k₂_mem {G : UMultigraph V} {U : SubObj V} (hU : IsSubObjU G U) : U.k₂ ∈ U.atoms := by
  have := hU.2.2.2.1; rwa [SubObj.core_verts] at this

/-- In `E(U)`, a non-joint atom of a sub-object has degree `4`. -/
theorem IsSubObjU.deg_induce_of_inner {G : UMultigraph V} {U : SubObj V} (hU : IsSubObjU G U) {v : V}
    (hv : v ∈ U.atoms) (h1 : v ≠ U.k₁) (h2 : v ≠ U.k₂) : deg (induce G U.atoms) v = 4 := by
  have hcore := hU.2.2
  have h4 := hcore.2.2.2.2.2.1 v (by rw [SubObj.core_verts]; exact hv) h1 h2
  cases hh : U.hyper
  · have : U.core G = induce G U.atoms := by simp [SubObj.core, hh, SubObj.edges]
    rwa [this] at h4
  · have : U.core G = eraseBond (induce G U.atoms) s(U.k₁, U.k₂) := by simp [SubObj.core, hh, SubObj.edges]
    rw [this] at h4
    have hmH : (induce G U.atoms).mult s(U.k₁, U.k₂) ≠ 0 := by
      rw [induce_mult_of_mem G hU.k₁_mem hU.k₂_mem]; exact hU.2.1 hh
    have hd := deg_eraseBond (induce G U.atoms) hcore.2.2.1 hU.k₁_mem hU.k₂_mem hmH v
    rw [if_neg (by rintro (h | h); exacts [h1 h, h2 h]), add_zero, h4] at hd
    exact hd.symm

/-- In a block, a non-joint atom of a sub-object keeps all its bonds inside the sub-object. -/
theorem IsSubObjU.closed_of_inner {G : UMultigraph V} {j₁ j₂ : V} {U : SubObj V} (hB : IsBlockU G j₁ j₂)
    (hU : IsSubObjU G U) {v : V} (hv : v ∈ U.atoms) (h1 : v ≠ U.k₁) (h2 : v ≠ U.k₂) :
    v ≠ j₁ ∧ v ≠ j₂ ∧ ∀ w ∈ G.verts, G.mult s(v, w) ≠ 0 → w ∈ U.atoms :=
  interior_closed hB hU.atoms_subset hv (hU.deg_induce_of_inner hv h1 h2)

/-- **N2 Lemma 1.14(a)** (all-in or all-out). -/
theorem phiAllInOut_holds : PhiAllInOutStatement.{u} := by
  intro V _ G j₁ j₂ a b xm xp ym yp Km Kp U hB hl hR hU h1a h1b h2a h2b
  obtain ⟨hR', -, -, -, -⟩ := hR
  have hRc := hR'.toCore
  have hnb_a : ∀ w, w = b ∨ w = xm ∨ w = xp → G.mult s(a, w) ≠ 0 := by
    rintro w (rfl | rfl | rfl)
    · rw [hR'.mult_ab]; omega
    · rw [hR'.a_xm]; omega
    · rw [hR'.a_xp]; omega
  have hnb_b : ∀ w, w = a ∨ w = ym ∨ w = yp → G.mult s(b, w) ≠ 0 := by
    rintro w (rfl | rfl | rfl)
    · rw [Sym2.eq_swap, hR'.mult_ab]; omega
    · rw [hR'.b_ym]; omega
    · rw [hR'.b_yp]; omega
  have hxmV := (hRc.mem_verts (Or.inl hRc.xm_mem)).1
  have hxpV := (hRc.mem_verts (Or.inr hRc.xp_mem)).1
  have hymV := (hRc.mem_verts (Or.inl hRc.ym_mem)).1
  have hypV := (hRc.mem_verts (Or.inr hRc.yp_mem)).1
  by_cases haS : a ∈ U.atoms
  · obtain ⟨-, -, hcla⟩ := hU.closed_of_inner hB haS (Ne.symm h1a) (Ne.symm h2a)
    have hbS := hcla b hR'.b_mem (hnb_a b (Or.inl rfl))
    obtain ⟨-, -, hclb⟩ := hU.closed_of_inner hB hbS (Ne.symm h1b) (Ne.symm h2b)
    left
    refine ⟨?_, ?_, hcla xm hxmV (hnb_a xm (Or.inr (Or.inl rfl))), hcla xp hxpV (hnb_a xp (Or.inr (Or.inr rfl))),
      hclb ym hymV (hnb_b ym (Or.inr (Or.inl rfl))), hclb yp hypV (hnb_b yp (Or.inr (Or.inr rfl)))⟩
    · simp only [SubObj.inner, Finset.mem_erase]; exact ⟨Ne.symm h2a, Ne.symm h1a, haS⟩
    · simp only [SubObj.inner, Finset.mem_erase]; exact ⟨Ne.symm h2b, Ne.symm h1b, hbS⟩
  · right
    refine ⟨haS, fun hbS => haS ?_⟩
    obtain ⟨-, -, hclb⟩ := hU.closed_of_inner hB hbS (Ne.symm h1b) (Ne.symm h2b)
    exact hclb a hR'.a_mem (hnb_b a (Or.inl rfl))

end WaveTurbulence.TVine.Core
