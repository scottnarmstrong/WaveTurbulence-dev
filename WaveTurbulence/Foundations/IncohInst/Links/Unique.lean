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

theorem linkPartner_ne (hQ : Q.Decodes G) (b : GBranch G.tree) : linkPartner hQ b ≠ b := by
  obtain ⟨hl, hb⟩ := linkOf_spec hQ b
  have hne := (link_branching hQ hl).2.2
  intro h
  rcases hb with hb | hb
  · have := linkPartner_of_fst hQ hl b hb
    rw [h] at this; exact hne (hb.symm.trans this)
  · have := linkPartner_of_snd hQ hl b hb
    rw [h] at this; exact hne (this.symm.trans hb)

theorem linkPartner_linkPartner (hQ : Q.Decodes G) (b : GBranch G.tree) :
    linkPartner hQ (linkPartner hQ b) = b := by
  obtain ⟨hl, hb⟩ := linkOf_spec hQ b
  apply Subtype.ext
  rcases hb with hb | hb
  · have h1 := linkPartner_of_fst hQ hl b hb
    rw [linkPartner_of_snd hQ hl _ h1, hb]
  · have h1 := linkPartner_of_snd hQ hl b hb
    rw [linkPartner_of_fst hQ hl _ h1, hb]

/-- **Existence** (DH21 Prop 4.3): the link partner satisfies `ζ_{𝔫'} Ω_{𝔫'} = -ζ_𝔫 Ω_𝔫` for every
vector decoration. -/
theorem linkPartner_antisymm {d : ℕ} (hQ : Q.Decodes G) (hG : IsCouple G)
    {κ : GNode G.tree → Mom d} (hκ : IsDecoration G κ) (b : GBranch G.tree) :
    ((G.sign (linkPartner hQ b).toNode : ℤ) : ℝ) * omegaNode G κ (linkPartner hQ b) =
      -(((G.sign b.toNode : ℤ) : ℝ) * omegaNode G κ b) := by
  obtain ⟨hl, hb⟩ := linkOf_spec hQ b
  rcases hb with hb | hb
  · exact zeta_omega_link hQ hG hκ hl b _ hb (linkPartner_of_fst hQ hl b hb)
  · have := zeta_omega_link hQ hG hκ hl (linkPartner hQ b) b (linkPartner_of_snd hQ hl b hb) hb
    linarith

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

theorem isDecoration_latticePoint {d : ℕ} {w : ℕ} {G : Garden w} (L : ℝ)
    {κ : GNode G.tree → (Fin d → ℤ)} (h : IsDecoration G κ) :
    IsDecoration G (fun a => latticePoint L (κ a)) :=
  ⟨fun b => by simp only [h.1 b, latticePoint_add, latticePoint_sub],
    fun ℓ => by simp only [h.2 ℓ]⟩

theorem latticePoint_single_ne {d : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : L ≠ 0) :
    latticePoint L (Pi.single (⟨0, hd⟩ : Fin d) 1 : Fin d → ℤ) ≠ 0 := by
  intro h
  have := congrArg (fun v : Mom d => v (⟨0, hd⟩ : Fin d)) h
  simp [latticePoint, hL] at this

/-- **DH21 Proposition 4.3** (`branchpair`, L729–L737; TARGET Prop `deflink`): for a couple carrier
`G` decoded by `Q` and `d ≥ 1`, the link partner is the unique fixed-point-free involution `P` of
the branching nodes with `ζ_{P𝔫} Ω_{P𝔫} = -ζ_𝔫 Ω_𝔫` for every lattice decoration `k = κ/L`.
(Existence holds for every vector decoration: `linkPartner_antisymm`.) -/
theorem branchpair {d : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : L ≠ 0) (hQ : Q.Decodes G) (hG : IsCouple G) :
    ∃! P : GBranch G.tree → GBranch G.tree, (∀ b, P (P b) = b) ∧ (∀ b, P b ≠ b) ∧
      ∀ κ : GNode G.tree → (Fin d → ℤ), IsDecoration G κ → ∀ b,
        ((G.sign (P b).toNode : ℤ) : ℝ) * omegaNode G (fun a => latticePoint L (κ a)) (P b) =
          -(((G.sign b.toNode : ℤ) : ℝ) * omegaNode G (fun a => latticePoint L (κ a)) b) := by
  refine ⟨linkPartner hQ, ⟨linkPartner_linkPartner hQ, linkPartner_ne hQ,
    fun κ hκ b => linkPartner_antisymm hQ hG (isDecoration_latticePoint L hκ) b⟩, ?_⟩
  rintro P ⟨-, hne, hanti⟩
  funext b
  obtain ⟨hl, hb⟩ := linkOf_spec hQ b
  set l := linkOf hQ b
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hl
  set e : Fin d → ℤ := Pi.single (⟨0, hd⟩ : Fin d) 1
  set θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ) :=
    fun j' => if j' = j then (e, e) else (0, 0)
  set κ := (decOfParams hQ (0 : Fin d → ℤ) θ).1
  have hκ : IsDecoration G κ := (decOfParams hQ (0 : Fin d → ℤ) θ).2.1
  set k : GNode G.tree → Mom d := fun a => latticePoint L (κ a)
  have hk : IsDecoration G k := isDecoration_latticePoint L hκ
  have hpar := decParams_decOfParams hQ hG (0 : Fin d → ℤ) θ
  -- the parameters at the chosen node of every link
  have hxy : ∀ j' : Fin Q.links.length, ∀ c : GBranch G.tree, c.1 = (Q.links.get j').1 →
      xNode κ c = (θ j').1 ∧ yNode κ c = (θ j').2 := fun j' c hc => by
    have := congrFun hpar j'
    simp only [decParams, chosenNode, Prod.mk.injEq] at this
    rw [← hc, xv_extend, yv_extend] at this
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hxk : ∀ c : GBranch G.tree, xNode k c = latticePoint L (xNode κ c) := fun c => by
    simp only [xNode, k, latticePoint_sub]
  have hyk : ∀ c : GBranch G.tree, yNode k c = latticePoint L (yNode κ c) := fun c => by
    simp only [yNode, k, latticePoint_sub]
  have hsign : ∀ c : GBranch G.tree, ((G.sign c.toNode : ℤ) : ℝ) ≠ 0 := fun c => by
    rcases Int.units_eq_one_or (G.sign c.toNode) with h | h <;> rw [h] <;> norm_num
  -- `Ω` vanishes off the link `l`
  have hvan : ∀ v : GBranch G.tree, omegaNode G k v ≠ 0 → linkOf hQ v = l := fun v hv => by
    obtain ⟨hl', hv'⟩ := linkOf_spec hQ v
    obtain ⟨j', hj'⟩ := List.mem_iff_get.mp hl'
    by_contra hne'
    have hjj : j' ≠ j := fun h => hne' (by rw [← hj', ← hj, h])
    set c : GBranch G.tree := ⟨(linkOf hQ v).1, (link_branching hQ hl').1⟩
    have hc0 : omegaNode G k c = 0 := by
      obtain ⟨h1, h2⟩ := hxy j' c (by rw [hj'])
      simp only [θ, hjj, ↓reduceIte] at h1 h2
      rw [omegaNode_eq hk, hxk, hyk, h1, h2, latticePoint_zero]
      simp
    rcases hv' with hv' | hv'
    · exact hv (by rwa [show v = c from Subtype.ext hv'])
    · have := zeta_omega_link hQ hG hk hl' c v rfl hv'
      rw [hc0, mul_zero, neg_zero] at this
      exact hv ((mul_eq_zero.mp this).resolve_left (hsign v))
  -- `Ω_b ≠ 0`
  set c : GBranch G.tree := ⟨l.1, (link_branching hQ hl).1⟩
  have hcne : omegaNode G k c ≠ 0 := by
    obtain ⟨h1, h2⟩ := hxy j c (by rw [hj])
    simp only [θ, ↓reduceIte] at h1 h2
    rw [omegaNode_eq hk, hxk, hyk, h1, h2, real_inner_self_eq_norm_sq]
    have := latticePoint_single_ne hd hL
    have : ‖latticePoint L e‖ ≠ 0 := norm_ne_zero_iff.mpr this
    positivity
  have hbne : omegaNode G k b ≠ 0 := by
    rcases hb with hb | hb
    · rwa [show b = c from Subtype.ext hb]
    · have := zeta_omega_link hQ hG hk hl c b rfl hb
      intro h0
      rw [h0, mul_zero] at this
      exact hcne ((mul_eq_zero.mp (neg_eq_zero.mp this.symm)).resolve_left (hsign c))
  have hPne : omegaNode G k (P b) ≠ 0 := by
    have := hanti κ hκ b
    intro h0
    rw [h0, mul_zero] at this
    exact hbne ((mul_eq_zero.mp (neg_eq_zero.mp this.symm)).resolve_left (hsign b))
  have hPl := hvan (P b) hPne
  obtain ⟨-, hPb⟩ := linkOf_spec hQ (P b)
  rw [hPl] at hPb
  have hlne := (link_branching hQ hl).2.2
  apply Subtype.ext
  rcases hb with hb | hb
  · rw [linkPartner_of_fst hQ hl b hb]
    rcases hPb with h | h
    · exact absurd (Subtype.ext (h.trans hb.symm)) (hne b)
    · exact h
  · rw [linkPartner_of_snd hQ hl b hb]
    rcases hPb with h | h
    · exact h
    · exact absurd (Subtype.ext (h.trans hb.symm)) (hne b)

end WaveTurbulence.Links
