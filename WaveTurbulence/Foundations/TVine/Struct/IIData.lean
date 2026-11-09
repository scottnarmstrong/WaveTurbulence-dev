/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.SubObjU
public import WaveTurbulence.Foundations.TVine.Struct.Kinds
public import WaveTurbulence.Foundations.TVine.Core.Parity
public import WaveTurbulence.Foundations.TVine.Core.Induced
import Mathlib.Tactic

/-!
# Sub-objects of a vine (II), U level (packet L3; N3 §2.2, proof of Cor 1.16′ (1), (2) for (II))

A vine (II) is the ladder `j₁ – R₁ = ⋯ = R_m – j₂` of `m ≥ 1` rungs. Its structure enters only through **level
data** (`IIData`): a level function with `j_b` at level `0`, `j_t` at level `top`, and for every interior atom `x` a
partner `part x` at the same level with `mult(x, part x) ≥ 2`, a neighbour `dn x` one level down and a neighbour
`up x` one level up.

* `deg_core_add_le`: core degree plus bonds to atoms outside `S(U)` is at most the degree in `G`;
* `not_both_joints`: in a block, no proper sub-object contains both joints;
* `IIData.rev`: the reversed level data;
* **`IIData.jb_not_mem`**, **`IIData.member_shape`**: a proper sub-object of a vine (II) contains no joint, is of
  block type, and is a rung `{x, part x}` (N3 L570–L576).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core

universe u

variable {V : Type u} [DecidableEq V]

theorem deg_core_le_induce (G : UMultigraph V) (U : SubObj V) (x : V) :
    deg (U.core G) x ≤ deg (induce G U.atoms) x := by
  unfold deg
  rw [core_verts]
  exact add_le_add (Finset.sum_le_sum fun w _ => core_mult_le G U _) (core_mult_le G U _)

/-- **Core degree plus some bonds leaving `S(U)` is at most the degree.** -/
theorem deg_core_add_le {G : UMultigraph V} {U : SubObj V} (hA : U.atoms ⊆ G.verts) {x : V} (hx : x ∈ U.atoms)
    {T : Finset V} (hT : T ⊆ G.verts \ U.atoms) :
    deg (U.core G) x + ∑ w ∈ T, G.mult s(x, w) ≤ deg G x := by
  have h1 := deg_core_le_induce G U x
  have h2 := deg_induce G hx hA
  have h3 : ∑ w ∈ T, G.mult s(x, w) ≤ ∑ w ∈ G.verts \ U.atoms, G.mult s(x, w) :=
    Finset.sum_le_sum_of_subset hT
  omega

/-- The core degree of an atom of a sub-object: `2` at its joints, `4` elsewhere. -/
theorem core_deg_cases {G : UMultigraph V} {U : SubObj V} (hU : IsSubObjU G U) {x : V} (hx : x ∈ U.atoms) :
    ((x = U.k₁ ∨ x = U.k₂) ∧ deg (U.core G) x = 2) ∨ (x ≠ U.k₁ ∧ x ≠ U.k₂ ∧ deg (U.core G) x = 4) := by
  obtain ⟨-, -, -, hd₁, hd₂, hd, -⟩ := hU.2.2
  by_cases h1 : x = U.k₁
  · subst h1; exact Or.inl ⟨Or.inl rfl, hd₁⟩
  by_cases h2 : x = U.k₂
  · subst h2; exact Or.inl ⟨Or.inr rfl, hd₂⟩
  exact Or.inr ⟨h1, h2, hd x (by rw [core_verts]; exact hx) h1 h2⟩

theorem joint_of_deg_le_three {G : UMultigraph V} {U : SubObj V} (hU : IsSubObjU G U) {x : V} (hx : x ∈ U.atoms)
    (h : deg (U.core G) x ≤ 3) : x = U.k₁ ∨ x = U.k₂ := by
  rcases core_deg_cases hU hx with ⟨h', -⟩ | ⟨-, -, h'⟩
  · exact h'
  · omega

theorem false_of_deg_le_one {G : UMultigraph V} {U : SubObj V} (hU : IsSubObjU G U) {x : V} (hx : x ∈ U.atoms)
    (h : deg (U.core G) x ≤ 1) : False := by
  rcases core_deg_cases hU hx with ⟨-, h'⟩ | ⟨-, -, h'⟩ <;> omega

theorem k₁_mem {G : UMultigraph V} {U : SubObj V} (hU : IsSubObjU G U) : U.k₁ ∈ U.atoms := by
  have := hU.2.2.1; rwa [core_verts] at this

theorem k₂_mem {G : UMultigraph V} {U : SubObj V} (hU : IsSubObjU G U) : U.k₂ ∈ U.atoms := by
  have := hU.2.2.2.1; rwa [core_verts] at this

/-- In the hyper case, the core degree at a joint of `U` is one less than the induced degree. -/
theorem deg_core_hyper {G : UMultigraph V} {U : SubObj V} (hU : IsSubObjU G U) (hh : U.hyper = true) {x : V}
    (hx : x = U.k₁ ∨ x = U.k₂) : deg (U.core G) x + 1 = deg (induce G U.atoms) x := by
  have hne : U.k₁ ≠ U.k₂ := hU.2.2.2.2.1
  have hm : (induce G U.atoms).mult s(U.k₁, U.k₂) ≠ 0 := by
    rw [Core.induce_mult_of_mem G (k₁_mem hU) (k₂_mem hU)]; exact hU.2.1 hh
  have := deg_eraseBond (induce G U.atoms) hne (k₁_mem hU) (k₂_mem hU) hm x
  rw [if_pos hx] at this
  have hc : U.core G = eraseBond (induce G U.atoms) s(U.k₁, U.k₂) := by
    show (if U.hyper then eraseBond (SubObj.edges G U) s(U.k₁, U.k₂) else SubObj.edges G U) = _
    rw [if_pos hh]; rfl
  rw [hc]; exact this

/-- **In a block, no proper sub-object contains both joints.** -/
theorem not_both_joints {G : UMultigraph V} {j₁ j₂ : V} (hB : IsBlockU G j₁ j₂) {U : SubObj V}
    (hU : IsSubObjU G U) (h₁ : j₁ ∈ U.atoms) (h₂ : j₂ ∈ U.atoms) : False := by
  obtain ⟨hj₁, hj₂, hj, hd₁, hd₂, hd, hconn⟩ := hB
  have hA : U.atoms ⊆ G.verts := hU.1.subset
  have hle : ∀ x ∈ U.atoms, deg (U.core G) x ≤ deg G x := fun x hx => by
    have := deg_core_add_le (T := ∅) hA hx (Finset.empty_subset _); simpa using this
  have hk₁ : j₁ = U.k₁ ∨ j₁ = U.k₂ := joint_of_deg_le_three hU h₁ (by have := hle j₁ h₁; omega)
  have hk₂ : j₂ = U.k₁ ∨ j₂ = U.k₂ := joint_of_deg_le_three hU h₂ (by have := hle j₂ h₂; omega)
  have hkj : ∀ x, (x = U.k₁ ∨ x = U.k₂) → x = j₁ ∨ x = j₂ := by
    rintro x (rfl | rfl) <;> rcases hk₁ with h | h <;> rcases hk₂ with h' | h' <;> first
      | exact Or.inl h.symm | exact Or.inr h'.symm | exact absurd (h.trans h'.symm) hj
  have hdegj : ∀ x, (x = U.k₁ ∨ x = U.k₂) → deg G x = 2 := fun x hx => by
    rcases hkj x hx with rfl | rfl
    · exact hd₁
    · exact hd₂
  cases hh : U.hyper with
  | true =>
    have h1 := deg_core_hyper hU hh hk₁
    have h2 := deg_induce G h₁ hA
    rcases core_deg_cases hU h₁ with ⟨-, h3⟩ | ⟨hn₁, hn₂, -⟩
    · omega
    · rcases hk₁ with h | h
      · exact hn₁ h
      · exact hn₂ h
  | false =>
    have hc : U.core G = induce G U.atoms := by
      show (if U.hyper then eraseBond (SubObj.edges G U) s(U.k₁, U.k₂) else SubObj.edges G U) = _
      rw [hh]; rfl
    have hout : ∀ x ∈ U.atoms, ∑ w ∈ G.verts \ U.atoms, G.mult s(x, w) = 0 := by
      intro x hx
      have h2 := deg_induce G hx hA
      rw [← hc] at h2
      rcases core_deg_cases hU hx with ⟨hx', h3⟩ | ⟨hn₁, hn₂, h3⟩
      · have := hdegj x hx'; omega
      · have : deg G x = 4 := hd x (hA hx) (fun h => by rcases hkj x (by subst h; exact hk₁) with h' | h' <;> simp_all)
          (fun h => by rcases hkj x (by subst h; exact hk₂) with h' | h' <;> simp_all)
        omega
    have hcl : ∀ x ∈ U.atoms, ∀ w ∈ G.verts, G.mult s(x, w) ≠ 0 → w ∈ U.atoms := by
      intro x hx w hw hm
      by_contra hwA
      have := hout x hx
      rw [Finset.sum_eq_zero_iff] at this
      exact hm (this w (Finset.mem_sdiff.mpr ⟨hw, hwA⟩))
    have := eq_of_closed' hconn hA ⟨j₁, h₁⟩ hcl
    exact hU.1.ne this

/-- **Level data of a vine (II)** (the ladder `j_b – R₁ = ⋯ = R_m – j_t`). -/
structure IIData (G : UMultigraph V) (jb jt : V) where
  lev : V → ℕ
  top : ℕ
  part : V → V
  dn : V → V
  up : V → V
  jb_mem : jb ∈ G.verts
  jt_mem : jt ∈ G.verts
  lev_jb : lev jb = 0
  lev_jt : lev jt = top
  top_pos : 0 < top
  jb_up : ∃ z ∈ G.verts, 0 < lev z ∧ 1 ≤ G.mult s(jb, z)
  jt_dn : ∃ z ∈ G.verts, lev z < top ∧ 1 ≤ G.mult s(jt, z)
  inner : ∀ x ∈ G.verts, x ≠ jb → x ≠ jt →
    (1 ≤ lev x ∧ lev x < top) ∧
    (part x ∈ G.verts ∧ part x ≠ x ∧ lev (part x) = lev x ∧ 2 ≤ G.mult s(x, part x)) ∧
    (dn x ∈ G.verts ∧ lev (dn x) + 1 = lev x ∧ 1 ≤ G.mult s(x, dn x)) ∧
    (up x ∈ G.verts ∧ lev (up x) = lev x + 1 ∧ 1 ≤ G.mult s(x, up x))

namespace IIData

variable {G : UMultigraph V} {jb jt : V}

theorem lev_le (D : IIData G jb jt) (hne : jb ≠ jt) {y : V} (hy : y ∈ G.verts) : D.lev y ≤ D.top := by
  by_cases h1 : y = jb
  · subst h1; rw [D.lev_jb]; exact Nat.zero_le _
  by_cases h2 : y = jt
  · subst h2; rw [D.lev_jt]
  exact (D.inner y hy h1 h2).1.2.le

/-- The reversed level data. -/
def rev (D : IIData G jb jt) (hne : jb ≠ jt) : IIData G jt jb where
  lev x := D.top - D.lev x
  top := D.top
  part := D.part
  dn := D.up
  up := D.dn
  jb_mem := D.jt_mem
  jt_mem := D.jb_mem
  lev_jb := by simp [D.lev_jt]
  lev_jt := by simp [D.lev_jb]
  top_pos := D.top_pos
  jb_up := by
    obtain ⟨z, hz, h1, h2⟩ := D.jt_dn
    exact ⟨z, hz, by omega, h2⟩
  jt_dn := by
    obtain ⟨z, hz, h1, h2⟩ := D.jb_up
    exact ⟨z, hz, by have := D.top_pos; omega, h2⟩
  inner x hx h1 h2 := by
    obtain ⟨⟨l1, l2⟩, ⟨p1, p2, p3, p4⟩, ⟨d1, d2, d3⟩, ⟨u1, u2, u3⟩⟩ := D.inner x hx h2 h1
    have hu := D.lev_le hne u1
    refine ⟨⟨by omega, by omega⟩, ⟨p1, p2, by rw [p3], p4⟩, ⟨u1, by omega, u3⟩, ⟨d1, by omega, d3⟩⟩

/-- **A proper sub-object of a vine (II) does not contain the bottom joint.** -/
theorem jb_not_mem (D : IIData G jb jt) (hB : IsBlockU G jb jt) {U : SubObj V} (hU : IsSubObjU G U) : jb ∉ U.atoms := by
  intro hjb
  have hne : jb ≠ jt := hB.2.2.1
  by_cases hjt : jt ∈ U.atoms
  · exact not_both_joints hB hU hjb hjt
  have hA : U.atoms ⊆ G.verts := hU.1.subset
  have hdjb : deg (U.core G) jb ≤ 2 := by
    have := deg_core_add_le (T := ∅) hA hjb (Finset.empty_subset _); simp at this
    have := hB.2.2.2.1; omega
  have hjbk := joint_of_deg_le_three hU hjb (by omega)
  obtain ⟨y, hyA, hy⟩ := Finset.exists_mem_eq_sup U.atoms ⟨jb, hjb⟩ D.lev
  have hsup : ∀ w ∈ U.atoms, D.lev w ≤ D.lev y := fun w hw => hy ▸ Finset.le_sup hw
  by_cases hyb : y = jb
  · -- every atom is at level `0`, hence `jb`; but the two joints of `U` differ
    have hall : ∀ w ∈ U.atoms, w = jb := by
      intro w hw
      by_contra hwb
      have hwt : w ≠ jt := fun h => hjt (h ▸ hw)
      have := (D.inner w (hA hw) hwb hwt).1.1
      have := hsup w hw
      rw [hyb, D.lev_jb] at this; omega
    exact hU.2.2.2.2.1 ((hall _ (k₁_mem hU)).trans (hall _ (k₂_mem hU)).symm)
  have hyt : y ≠ jt := fun h => hjt (h ▸ hyA)
  obtain ⟨⟨l1, -⟩, ⟨p1, p2, p3, p4⟩, -, ⟨u1, u2, u3⟩⟩ := D.inner y (hA hyA) hyb hyt
  have hupA : D.up y ∉ U.atoms := fun h => by have := hsup _ h; omega
  by_cases hpA : D.part y ∈ U.atoms
  · have hpb : D.part y ≠ jb := fun h => by rw [h, D.lev_jb] at p3; omega
    have hpt : D.part y ≠ jt := fun h => hjt (h ▸ hpA)
    obtain ⟨-, -, -, ⟨u1', u2', u3'⟩⟩ := D.inner (D.part y) p1 hpb hpt
    have hupA' : D.up (D.part y) ∉ U.atoms := fun h => by have := hsup _ h; omega
    have hdy := deg_core_add_le hA hyA (T := {D.up y}) (by simp [u1, hupA])
    have hdp := deg_core_add_le hA hpA (T := {D.up (D.part y)}) (by simp [u1', hupA'])
    have hgy := hB.2.2.2.2.2.1 y (hA hyA) hyb hyt
    have hgp := hB.2.2.2.2.2.1 _ p1 hpb hpt
    simp only [Finset.sum_singleton] at hdy hdp
    have hky := joint_of_deg_le_three hU hyA (by omega)
    have hkp := joint_of_deg_le_three hU hpA (by omega)
    have hyb' : y ≠ jb := hyb
    rcases hjbk with h | h <;> rcases hky with h' | h' <;> rcases hkp with h'' | h'' <;>
      first
        | exact hyb' (h'.trans h.symm)
        | exact hpb (h''.trans h.symm)
        | exact p2 (h''.trans h'.symm)
  · have hne' : D.part y ≠ D.up y := fun h => by rw [h] at p3; omega
    have hdy := deg_core_add_le hA hyA (T := {D.part y, D.up y})
      (by intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact Finset.mem_sdiff.mpr ⟨p1, hpA⟩
          · exact Finset.mem_sdiff.mpr ⟨u1, hupA⟩)
    rw [Finset.sum_pair hne'] at hdy
    have hgy := hB.2.2.2.2.2.1 y (hA hyA) hyb hyt
    exact false_of_deg_le_one hU hyA (by omega)

/-- **A proper sub-object of a vine (II) avoids both joints.** -/
theorem joints_not_mem (D : IIData G jb jt) (hB : IsBlockU G jb jt) {U : SubObj V} (hU : IsSubObjU G U) :
    jb ∉ U.atoms ∧ jt ∉ U.atoms :=
  ⟨D.jb_not_mem hB hU, (D.rev hB.2.2.1).jb_not_mem hB.swap hU⟩

/-- **A proper sub-object of a vine (II) is a rung**: of block type, on `{x, part x}`. -/
theorem member_shape (D : IIData G jb jt) (hB : IsBlockU G jb jt) {U : SubObj V} (hU : IsSubObjU G U) :
    U.hyper = false ∧ ∃ x, U.atoms = {x, D.part x} := by
  obtain ⟨hjb, hjt⟩ := D.joints_not_mem hB hU
  have hA : U.atoms ⊆ G.verts := hU.1.subset
  have hne : U.atoms.Nonempty := ⟨_, k₁_mem hU⟩
  have hint : ∀ w ∈ U.atoms, w ≠ jb ∧ w ≠ jt := fun w hw =>
    ⟨fun h => hjb (h ▸ hw), fun h => hjt (h ▸ hw)⟩
  have hdeg : ∀ w ∈ U.atoms, deg G w = 4 := fun w hw =>
    hB.2.2.2.2.2.1 w (hA hw) (hint w hw).1 (hint w hw).2
  -- the bottom level
  obtain ⟨x, hxA, hinf⟩ := Finset.exists_min_image U.atoms D.lev hne
  -- the top level
  obtain ⟨y, hyA, hsup⟩ := Finset.exists_max_image U.atoms D.lev hne
  -- an atom with both an absent neighbour and an absent partner is impossible; with an absent neighbour, a joint
  have key : ∀ w ∈ U.atoms, ∀ z, z ∈ G.verts → D.lev z ≠ D.lev w → 1 ≤ G.mult s(w, z) → z ∉ U.atoms →
      D.part w ∈ U.atoms ∧ (w = U.k₁ ∨ w = U.k₂) := by
    intro w hw z hz hzl hzm hzA
    obtain ⟨-, ⟨p1, p2, p3, p4⟩, -, -⟩ := D.inner w (hA hw) (hint w hw).1 (hint w hw).2
    by_cases hpA : D.part w ∈ U.atoms
    · refine ⟨hpA, joint_of_deg_le_three hU hw ?_⟩
      have := deg_core_add_le hA hw (T := {z}) (by simp [hz, hzA])
      simp only [Finset.sum_singleton] at this
      have := hdeg w hw; omega
    · exfalso
      have hne' : D.part w ≠ z := fun h => hzl (h ▸ p3)
      have := deg_core_add_le hA hw (T := {D.part w, z})
        (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl
            · exact Finset.mem_sdiff.mpr ⟨p1, hpA⟩
            · exact Finset.mem_sdiff.mpr ⟨hz, hzA⟩)
      rw [Finset.sum_pair hne'] at this
      have := hdeg w hw
      exact false_of_deg_le_one hU hw (by omega)
  have hdn : ∀ w ∈ U.atoms, D.lev w = D.lev x →
      D.part w ∈ U.atoms ∧ (w = U.k₁ ∨ w = U.k₂) := by
    intro w hw hl
    obtain ⟨-, -, ⟨d1, d2, d3⟩, -⟩ := D.inner w (hA hw) (hint w hw).1 (hint w hw).2
    exact key w hw _ d1 (by omega) d3 (fun h => by have := hinf _ h; omega)
  have hup : ∀ w ∈ U.atoms, D.lev w = D.lev y →
      D.part w ∈ U.atoms ∧ (w = U.k₁ ∨ w = U.k₂) := by
    intro w hw hl
    obtain ⟨-, -, -, ⟨u1, u2, u3⟩⟩ := D.inner w (hA hw) (hint w hw).1 (hint w hw).2
    exact key w hw _ u1 (by omega) u3 (fun h => by have := hsup _ h; omega)
  obtain ⟨hpx, hkx⟩ := hdn x hxA rfl
  obtain ⟨-, p2x, p3x, -⟩ := (D.inner x (hA hxA) (hint x hxA).1 (hint x hxA).2).2.1
  have hkpx := (hdn _ hpx p3x).2
  -- the joints of `U` are `x` and `part x`
  have hkk : ∀ w, (w = U.k₁ ∨ w = U.k₂) → w = x ∨ w = D.part x := by
    have hk := hU.2.2.2.2.1
    rintro w (rfl | rfl) <;> rcases hkx with h | h <;> rcases hkpx with h' | h' <;> first
      | exact Or.inl h.symm | exact Or.inr h'.symm | exact absurd (h'.trans h.symm) p2x
      | exact absurd (h.trans h'.symm) hk | exact absurd (h'.trans h.symm) hk
  -- the top level is the bottom level
  have hyx : D.lev y = D.lev x := by
    rcases hkk y (hup y hyA rfl).2 with h | h
    · rw [h]
    · rw [h, p3x]
  -- every atom is a joint of `U`
  have hall : ∀ w ∈ U.atoms, w = x ∨ w = D.part x := fun w hw =>
    hkk w (hdn w hw (le_antisymm (hyx ▸ hsup w hw) (hinf w hw))).2
  have hAeq : U.atoms = {x, D.part x} := by
    ext w; simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact hall w
    · rintro (rfl | rfl)
      · exact hxA
      · exact hpx
  refine ⟨?_, x, hAeq⟩
  -- hyper type is impossible: the core degree at `x` would be `≤ 1`
  cases hh : U.hyper with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨-, -, ⟨d1, d2, d3⟩, ⟨u1, u2, u3⟩⟩ := D.inner x (hA hxA) (hint x hxA).1 (hint x hxA).2
    have hdA : D.dn x ∉ U.atoms := fun h => by have := hinf _ h; omega
    have huA : D.up x ∉ U.atoms := fun h => by have := hsup _ h; omega
    have hne' : D.dn x ≠ D.up x := fun h => by rw [h] at d2; omega
    have h1 := deg_core_hyper hU hh hkx
    have h2 := deg_induce G hxA hA
    have h3 : G.mult s(x, D.dn x) + G.mult s(x, D.up x) ≤ ∑ w ∈ G.verts \ U.atoms, G.mult s(x, w) := by
      rw [← Finset.sum_pair (f := fun w => G.mult s(x, w)) hne']
      exact Finset.sum_le_sum_of_subset (by
        intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact Finset.mem_sdiff.mpr ⟨d1, hdA⟩
        · exact Finset.mem_sdiff.mpr ⟨u1, huA⟩)
    have := hdeg x hxA
    exact false_of_deg_le_one hU hxA (by omega)

end IIData

end WaveTurbulence.TVine.Struct
