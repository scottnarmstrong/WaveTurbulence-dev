/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.JointsInRungs

/-!
# N2 Lemma 1.12: no sub-object contains a joint of its container

`containerJoints_holds : ContainerJointsStatement`. Proof (N2 Lemma 1.12): a joint `J` of the block has degree 2, so
in a sub-object `U` it can only be a joint of a block-type `U`; every atom of `U` other than its second joint `j'`
keeps all its bonds inside `U`. If `j'` is the other joint of the block, `U` is closed, hence everything (the block is
connected), contradicting properness. Otherwise `j'` is an interior cut atom (it separates `U ∖ {j'}`, which misses
the other joint of the block). (The connectivity of the interior, `disjointlem` (i), is not needed.)
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

/-- An atom whose degree inside `S` is its full degree has all its neighbours in `S`. -/
theorem closed_of_deg_eq (G : UMultigraph V) {S : Finset V} (hS : S ⊆ G.verts) {u : V} (huS : u ∈ S)
    (hdeg : deg (induce G S) u = deg G u) : ∀ w ∈ G.verts, G.mult s(u, w) ≠ 0 → w ∈ S := by
  have hadd := deg_induce_add G hS huS
  have hzero : ∑ w ∈ G.verts \ S, G.mult s(u, w) = 0 := by omega
  intro w hw hm
  by_contra hwS
  exact hm ((Finset.sum_eq_zero_iff.mp hzero) w (Finset.mem_sdiff.mpr ⟨hw, hwS⟩))

theorem deg_induce_le (G : UMultigraph V) {S : Finset V} (hS : S ⊆ G.verts) {u : V} (huS : u ∈ S) :
    deg (induce G S) u ≤ deg G u := by
  have := deg_induce_add G hS huS; omega

private theorem cj_core {G : UMultigraph V} {j₁ j₂ : V} {U : SubObj V} (hB : IsBlockU G j₁ j₂)
    (hcutv : ∀ w ∈ interior G j₁ j₂, ConnOn G (G.verts.erase w)) (hU : IsSubObjU G U) (hk : U.k₁ = j₁) :
    j₁ ∉ U.atoms := by
  intro hjS
  have hU' := hU
  obtain ⟨hsub, hadj, hcore⟩ := hU
  set S := U.atoms with hSdef
  have hSV : S ⊆ G.verts := hsub.subset
  cases hh : U.hyper
  · have hcoreEq : U.core G = induce G S := by simp [SubObj.core, hh, SubObj.edges, hSdef]
    rw [hcoreEq] at hcore
    obtain ⟨hk₁S, hk₂S, hkk, hd₁, hd₂, hd, hconn⟩ := hcore
    -- every atom of `S` other than `k₂` keeps its bonds inside `S`
    have hcl : ∀ u ∈ S, u ≠ U.k₂ → ∀ w ∈ G.verts, G.mult s(u, w) ≠ 0 → w ∈ S := by
      intro u huS huk
      by_cases hu1 : u = U.k₁
      · subst hu1
        apply closed_of_deg_eq G hSV huS
        rw [hd₁, hk, hB.2.2.2.1]
      · exact (interior_closed hB hSV huS (hd u huS hu1 huk)).2.2
    by_cases hj' : U.k₂ = j₂
    · -- `U` is closed in `G`, hence everything
      have hall : S = G.verts := eq_of_closed' hB.2.2.2.2.2.2 hSV ⟨j₁, hjS⟩ (by
        intro u huS w hw hm
        by_cases huk : u = U.k₂
        · subst huk
          apply closed_of_deg_eq G hSV huS _ w hw hm
          rw [hd₂, hj', hB.2.2.2.2.1]
        · exact hcl u huS huk w hw hm)
      exact hsub.ne hall
    · -- `k₂` is an interior cut atom
      have hk₂j₁ : U.k₂ ≠ j₁ := fun h => hkk (hk.trans h.symm)
      have hk₂V : U.k₂ ∈ G.verts := hSV hk₂S
      have hk₂I : U.k₂ ∈ interior G j₁ j₂ := by simp [interior, hk₂V, hk₂j₁, hj']
      have hj₂S : j₂ ∉ S := by
        intro h
        have h1 : j₂ ≠ U.k₁ := by rw [hk]; exact hB.2.2.1.symm
        have h2 : j₂ ≠ U.k₂ := Ne.symm hj'
        exact (interior_closed hB hSV h (hd j₂ h h1 h2)).2.1 rfl
      have hT := eq_of_closed' (hcutv U.k₂ hk₂I) (S := S.erase U.k₂)
        (fun x hx => Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hx, hSV (Finset.mem_of_mem_erase hx)⟩)
        ⟨j₁, Finset.mem_erase.mpr ⟨Ne.symm hk₂j₁, hjS⟩⟩ (by
          intro u hu w hw hm
          exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hw,
            hcl u (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu) w (Finset.mem_of_mem_erase hw) hm⟩)
      have : j₂ ∈ S.erase U.k₂ := by
        rw [hT]; exact Finset.mem_erase.mpr ⟨fun h => hj' h.symm, hB.2.1⟩
      exact hj₂S (Finset.mem_of_mem_erase this)
  · -- hyper type: `j₁` would have degree `3`
    have hcoreEq : U.core G = eraseBond (induce G S) s(U.k₁, U.k₂) := by
      simp [SubObj.core, hh, SubObj.edges, hSdef]
    rw [hcoreEq] at hcore
    have hk₁S : U.k₁ ∈ S := hcore.1
    have hk₂S : U.k₂ ∈ S := hcore.2.1
    have hmH : (induce G S).mult s(U.k₁, U.k₂) ≠ 0 := by
      rw [induce_mult_of_mem G hk₁S hk₂S]; exact hadj hh
    have hdE := deg_eraseBond (induce G S) hcore.2.2.1 hk₁S hk₂S hmH U.k₁
    rw [if_pos (Or.inl rfl), hcore.2.2.2.1] at hdE
    have hle := deg_induce_le G hSV hk₁S
    rw [← hdE, hk, hB.2.2.2.1] at hle
    omega

/-- A joint of the block that lies in a sub-object is a joint of it. -/
private theorem cj_mem_joint {G : UMultigraph V} {j₁ j₂ : V} {U : SubObj V} (hB : IsBlockU G j₁ j₂)
    (hU : IsSubObjU G U) (hjS : j₁ ∈ U.atoms) : U.k₁ = j₁ ∨ U.k₂ = j₁ := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hsub, hadj, hcore⟩ := hU
  have hSV : U.atoms ⊆ G.verts := hsub.subset
  have hjC : j₁ ∈ (U.core G).verts := by rw [SubObj.core_verts]; exact hjS
  have h4 := hcore.2.2.2.2.2.1 j₁ hjC (Ne.symm hne.1) (Ne.symm hne.2)
  have hle := deg_induce_le G hSV hjS
  have hk₁S : U.k₁ ∈ U.atoms := by have := hcore.1; rwa [SubObj.core_verts] at this
  have hk₂S : U.k₂ ∈ U.atoms := by have := hcore.2.1; rwa [SubObj.core_verts] at this
  have hcl : deg (U.core G) j₁ ≤ deg (induce G U.atoms) j₁ := by
    cases hh : U.hyper
    · simp [SubObj.core, hh, SubObj.edges]
    · have hmH : (induce G U.atoms).mult s(U.k₁, U.k₂) ≠ 0 := by
        rw [induce_mult_of_mem G hk₁S hk₂S]; exact hadj hh
      have hkk : U.k₁ ≠ U.k₂ := hcore.2.2.1
      have hdE := deg_eraseBond (induce G U.atoms) hkk hk₁S hk₂S hmH j₁
      simp only [SubObj.core, hh, if_true, SubObj.edges]
      omega
  have := hB.2.2.2.1
  omega

/-- **N2 Lemma 1.12** (container joints). -/
theorem containerJoints_holds : ContainerJointsStatement.{u} := by
  intro V _ G j₁ j₂ U hB hl hI hcutv hU
  have hcut' : ∀ w ∈ interior G j₂ j₁, ConnOn G (G.verts.erase w) := by
    intro w hw; apply hcutv; simp only [interior, Finset.mem_erase] at hw ⊢; tauto
  constructor
  · intro hjS
    rcases cj_mem_joint hB hU hjS with h | h
    · exact cj_core hB hcutv hU h hjS
    · exact cj_core hB hcutv hU.swap h hjS
  · intro hjS
    rcases cj_mem_joint hB.swap hU hjS with h | h
    · exact cj_core hB.swap hcut' hU h hjS
    · exact cj_core hB.swap hcut' hU.swap h hjS

end WaveTurbulence.TVine.Core
