/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Param

/-!
# DH21 Proposition 4.3 (`branchpair`): the pairing of branching nodes (packet C2)

For a regular couple there is a unique way to pair the branching nodes such that
`ζ_{𝔫'} Ω_{𝔫'} = -ζ_𝔫 Ω_𝔫` for every pair and every decoration (DH21 Prop 4.3, L729–L737).

* existence: the link partner `linkPartner` (TARGET Prop `deflink`) has this property for every
  vector decoration (`linkPartner_antisymm`);
* uniqueness: any fixed-point-free involution with this property for all lattice decorations
  `k_𝔫 = κ_𝔫 / L` (`κ` integer, root value `0`) is the link partner (`branchpair`), for `d ≥ 1`.
  The proof picks, through `decEquiv`, the decoration with `x_𝔫 = y_𝔫 = e₁` at one chosen node and
  `0` elsewhere; then `Ω` vanishes exactly off that link.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {G : Garden 2} {Q : RegCpl}

/-- The link containing a branching node. -/
noncomputable def linkOf (hQ : Q.Decodes G) (b : GBranch G.tree) :
    (Fin 2 × Path) × (Fin 2 × Path) :=
  (exists_unique_link hQ b).exists.choose

theorem linkOf_spec (hQ : Q.Decodes G) (b : GBranch G.tree) :
    linkOf hQ b ∈ Q.links ∧ (b.1 = (linkOf hQ b).1 ∨ b.1 = (linkOf hQ b).2) :=
  (exists_unique_link hQ b).exists.choose_spec

theorem linkOf_eq (hQ : Q.Decodes G) (b : GBranch G.tree) {l : (Fin 2 × Path) × (Fin 2 × Path)}
    (hl : l ∈ Q.links) (hb : b.1 = l.1 ∨ b.1 = l.2) : linkOf hQ b = l :=
  (exists_unique_link hQ b).unique (linkOf_spec hQ b) ⟨hl, hb⟩

/-- **The link partner** of a branching node (TARGET Prop `deflink`). -/
noncomputable def linkPartner (hQ : Q.Decodes G) (b : GBranch G.tree) : GBranch G.tree :=
  if b.1 = (linkOf hQ b).1 then ⟨(linkOf hQ b).2, (link_branching hQ (linkOf_spec hQ b).1).2.1⟩
  else ⟨(linkOf hQ b).1, (link_branching hQ (linkOf_spec hQ b).1).1⟩

theorem linkPartner_of_fst (hQ : Q.Decodes G) {l : (Fin 2 × Path) × (Fin 2 × Path)}
    (hl : l ∈ Q.links) (b : GBranch G.tree) (hb : b.1 = l.1) : (linkPartner hQ b).1 = l.2 := by
  have e := linkOf_eq hQ b hl (Or.inl hb)
  unfold linkPartner
  split_ifs with h
  · simp [e, hb]
  · exact absurd (by rw [e]; exact hb) h

theorem linkPartner_of_snd (hQ : Q.Decodes G) {l : (Fin 2 × Path) × (Fin 2 × Path)}
    (hl : l ∈ Q.links) (b : GBranch G.tree) (hb : b.1 = l.2) : (linkPartner hQ b).1 = l.1 := by
  have e := linkOf_eq hQ b hl (Or.inr hb)
  have hne := (link_branching hQ hl).2.2
  unfold linkPartner
  split_ifs with h
  · rw [e, hb] at h; exact absurd h.symm hne
  · simp [e, hb, Ne.symm hne]

theorem linkPartner_linkPartner (hQ : Q.Decodes G) (b : GBranch G.tree) :
    linkPartner hQ (linkPartner hQ b) = b := by
  obtain ⟨hl, hb⟩ := linkOf_spec hQ b
  apply Subtype.ext
  rcases hb with hb | hb
  · have h1 := linkPartner_of_fst hQ hl b hb
    rw [linkPartner_of_snd hQ hl _ h1, hb]
  · have h1 := linkPartner_of_snd hQ hl b hb
    rw [linkPartner_of_fst hQ hl _ h1, hb]

/-- **The choice set `𝒩^ch`** (DH21 Def 4.11; TARGET Prop `deflink`, last paragraph) contains exactly one
node of every link: the chosen node `l.1` and not `l.2`. -/
theorem chosenSet_link (hQ : Q.Decodes G) {l : (Fin 2 × Path) × (Fin 2 × Path)} (hl : l ∈ Q.links) :
    l.1 ∈ chosenSet Q.links ∧ l.2 ∉ chosenSet Q.links := by
  refine ⟨List.mem_toFinset.mpr (List.mem_map_of_mem hl), fun h => ?_⟩
  obtain ⟨l', hl', he⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
  have := eq_of_flat_nodup (couple_links_flat_nodup Q) hl hl' (Or.inr rfl) (Or.inl he.symm)
  subst this
  exact (link_branching hQ hl).2.2 he

/-- Every branching node or its link partner is chosen, not both. -/
theorem chosen_xor (hQ : Q.Decodes G) (b : GBranch G.tree) :
    (b.1 ∈ chosenSet Q.links ∧ (linkPartner hQ b).1 ∉ chosenSet Q.links) ∨
      (b.1 ∉ chosenSet Q.links ∧ (linkPartner hQ b).1 ∈ chosenSet Q.links) := by
  obtain ⟨hl, hb⟩ := linkOf_spec hQ b
  have hc := chosenSet_link hQ hl
  rcases hb with hb | hb
  · left; rw [linkPartner_of_fst hQ hl b hb, hb]; exact hc
  · right; rw [linkPartner_of_snd hQ hl b hb, hb]; exact ⟨hc.2, hc.1⟩

/-! ### Uniqueness -/

theorem latticePoint_add {d : ℕ} (L : ℝ) (m n : Fin d → ℤ) :
    latticePoint L (m + n) = latticePoint L m + latticePoint L n := by
  ext j; simp [latticePoint, add_div]

theorem latticePoint_sub {d : ℕ} (L : ℝ) (m n : Fin d → ℤ) :
    latticePoint L (m - n) = latticePoint L m - latticePoint L n := by
  ext j; simp [latticePoint, sub_div]

theorem latticePoint_zero {d : ℕ} (L : ℝ) : latticePoint L (0 : Fin d → ℤ) = 0 := by
  ext j; simp [latticePoint]

end WaveTurbulence.Links
