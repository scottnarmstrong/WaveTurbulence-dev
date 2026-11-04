/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Bridge

/-!
# Links on couple carriers: `ζΩ` antisymmetry, `(x,y)` relation, `ε`, partition (packet C2)

TARGET Prop `deflink` (L874–L882) on a couple carrier `G` decoded by a code `Q`:

* `exists_unique_link`: every branching node lies in exactly one link, and the two nodes of a link
  are distinct branching nodes (the links divide `𝒩` into two-element subsets);
* `omegaNode_eq`: `Ω_𝔫 = 2⟨x_𝔫, y_𝔫⟩` (TARGET L983);
* `zeta_omega_link`: `ζ_{𝔫'} Ω_{𝔫'} = -ζ_𝔫 Ω_𝔫` for every decoration (DH21 Prop 4.3);
* `xy_link`: `{x_{𝔫'}, y_{𝔫'}} = {ζ₁ x_𝔫, ζ₂ y_𝔫}` (FINDINGS F16);
* `epsCoef_link`: `ε_{𝔫'} = ε_𝔫` for integer decorations (`ε` of TARGET (defcoef0)).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg Finset

/-! ### The partition, on carriers -/

theorem flatPairs_cons {α : Type*} (p : α × α) (L : List (α × α)) :
    flatPairs (p :: L) = p.1 :: p.2 :: flatPairs L := rfl

theorem mem_flatPairs {α : Type*} {x : α} {L : List (α × α)} {l : α × α} (hl : l ∈ L)
    (hx : x = l.1 ∨ x = l.2) : x ∈ flatPairs L := by
  simp only [flatPairs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨l, hl, hx⟩

/-- In a list of pairs with no repeated endpoint, an endpoint determines its pair. -/
theorem eq_of_flat_nodup {α : Type*} {L : List (α × α)} (h : (flatPairs L).Nodup) {x : α}
    {l l' : α × α} (hl : l ∈ L) (hl' : l' ∈ L) (hx : x = l.1 ∨ x = l.2)
    (hx' : x = l'.1 ∨ x = l'.2) : l = l' := by
  induction L with
  | nil => simp at hl
  | cons p L ih =>
    rw [flatPairs_cons, List.nodup_cons, List.nodup_cons, List.mem_cons] at h
    obtain ⟨h1, h2, h3⟩ := h
    rcases List.mem_cons.mp hl with e | hl₀ <;> rcases List.mem_cons.mp hl' with e' | hl₀'
    · rw [e, e']
    · exfalso
      subst e
      have hm := mem_flatPairs hl₀' hx'
      rcases hx with rfl | rfl
      · exact h1 (Or.inr hm)
      · exact h2 hm
    · exfalso
      subst e'
      have hm := mem_flatPairs hl₀ hx
      rcases hx' with rfl | rfl
      · exact h1 (Or.inr hm)
      · exact h2 hm
    · exact ih h3 hl₀ hl₀'

/-- The two nodes of a link are distinct. -/
theorem fst_ne_snd_of_flat_nodup {α : Type*} {L : List (α × α)} (h : (flatPairs L).Nodup)
    {l : α × α} (hl : l ∈ L) : l.1 ≠ l.2 := by
  induction L with
  | nil => simp at hl
  | cons p L ih =>
    rw [flatPairs_cons, List.nodup_cons, List.nodup_cons, List.mem_cons] at h
    rcases List.mem_cons.mp hl with rfl | hl
    · exact fun e => h.1 (Or.inl e)
    · exact ih h.2.2 hl

theorem mem_pairEndpoints_links_iff {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    (x : Fin 2 × Path) : x ∈ pairEndpoints Q.links ↔ x.2 ∈ (G.tree x.1).branching := by
  rw [RegCpl.links, ← couple_branchAddresses, tree_eq_coupleForest hQ]
  obtain ⟨j, p⟩ := x
  fin_cases j <;> simp [branchAddresses, addrExt, coupleForest]

/-- **The links divide the branching nodes into two-element subsets** (TARGET Prop `deflink`). -/
theorem exists_unique_link {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (b : GBranch G.tree) :
    ∃! l, l ∈ Q.links ∧ (b.1 = l.1 ∨ b.1 = l.2) := by
  have hx : b.1 ∈ pairEndpoints Q.links := (mem_pairEndpoints_links_iff hQ b.1).2 b.2
  obtain ⟨l, hl, hxl⟩ := (mem_pairEndpoints_iff _ _).1 hx
  exact ⟨l, ⟨hl, hxl⟩, fun l' ⟨hl', hxl'⟩ =>
    (eq_of_flat_nodup (couple_links_flat_nodup Q) hl hl' hxl hxl').symm⟩

/-- Both nodes of a link are branching nodes of the carrier, and they are distinct. -/
theorem link_branching {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    {l : (Fin 2 × Path) × (Fin 2 × Path)} (hl : l ∈ Q.links) :
    l.1.2 ∈ (G.tree l.1.1).branching ∧ l.2.2 ∈ (G.tree l.2.1).branching ∧ l.1 ≠ l.2 :=
  ⟨(mem_pairEndpoints_links_iff hQ _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inl rfl⟩),
    (mem_pairEndpoints_links_iff hQ _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inr rfl⟩),
    fst_ne_snd_of_flat_nodup (couple_links_flat_nodup Q) hl⟩

/-! ### `x`, `y`, `Ω` and `ε` on carriers -/

variable {V : Type*} [AddCommGroup V] {w : ℕ} {G : Garden w}

/-- `x_𝔫 = κ_{𝔫₁} - κ_𝔫`. -/
def xNode (κ : GNode G.tree → V) (b : GBranch G.tree) : V := κ (b.child 0) - κ b.toNode

/-- `y_𝔫 = κ_𝔫 - κ_{𝔫₃}`. -/
def yNode (κ : GNode G.tree → V) (b : GBranch G.tree) : V := κ b.toNode - κ (b.child 2)

theorem xv_extend (κ : GNode G.tree → V) (b : GBranch G.tree) :
    xv (extend κ) b.1 = xNode κ b := by
  simp only [xv, xNode]
  rw [← extend_node κ (b.child 0), ← extend_node κ b.toNode]
  rfl

theorem yv_extend (κ : GNode G.tree → V) (b : GBranch G.tree) :
    yv (extend κ) b.1 = yNode κ b := by
  simp only [yv, yNode]
  rw [← extend_node κ (b.child 2), ← extend_node κ b.toNode]
  rfl

/-- **The `(x,y)` relation of a link on a carrier** (TARGET Prop `deflink`, FINDINGS F16):
`{x_{𝔫'}, y_{𝔫'}} = {s₁ x_𝔫, s₂ y_𝔫}` and `ζ_{𝔫'} = -s₁ s₂ ζ_𝔫`. -/
theorem xy_link {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    {κ : GNode G.tree → V} (hκ : IsDecoration G κ) {l : (Fin 2 × Path) × (Fin 2 × Path)}
    (hl : l ∈ Q.links) (b b' : GBranch G.tree) (hb : b.1 = l.1) (hb' : b'.1 = l.2) :
    ∃ s₁ s₂ : ℤˣ,
      ((xNode κ b' = (s₁ : ℤ) • xNode κ b ∧ yNode κ b' = (s₂ : ℤ) • yNode κ b) ∨
        (xNode κ b' = (s₁ : ℤ) • yNode κ b ∧ yNode κ b' = (s₂ : ℤ) • xNode κ b)) ∧
      G.sign b'.toNode = -(s₁ * s₂) * G.sign b.toNode := by
  obtain ⟨s₁, s₂, hxy, hs⟩ := linkRel_of_decoration hQ hG hκ l hl
  rw [← hb, ← hb', xv_extend, xv_extend, yv_extend, yv_extend] at hxy
  rw [← hb, ← hb'] at hs
  exact ⟨s₁, s₂, hxy, hs⟩

/-- `Ω(k₁,k₂,k₃,k) = 2⟨k₁ - k, k - k₃⟩` when `k = k₁ - k₂ + k₃` (TARGET L983). -/
theorem resFactor_eq {d : ℕ} (k₁ k₂ k₃ k : Mom d) (h : k = k₁ - k₂ + k₃) :
    resFactor k₁ k₂ k₃ k = 2 * inner ℝ (k₁ - k) (k - k₃) := by
  have hk₂ : k₂ = k₁ - k + k₃ := by rw [h]; abel
  rw [hk₂]
  simp only [resFactor, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_comm]
  ring

/-- `Ω_𝔫 = 2⟨x_𝔫, y_𝔫⟩` for a decoration (TARGET L983). -/
theorem omegaNode_eq {d : ℕ} {κ : GNode G.tree → Mom d} (hκ : IsDecoration G κ)
    (b : GBranch G.tree) : omegaNode G κ b = 2 * inner ℝ (xNode κ b) (yNode κ b) :=
  resFactor_eq _ _ _ _ (hκ.1 b)

theorem inner_smul_units {d : ℕ} (s : ℤˣ) (x y : Mom d) :
    inner ℝ ((s : ℤ) • x) y = (s : ℝ) * inner ℝ x y := by
  rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left]

/-- **`ζ_{𝔫'} Ω_{𝔫'} = -ζ_𝔫 Ω_𝔫` for linked nodes and every decoration** (DH21 Prop 4.3, TARGET
Prop `deflink`). -/
theorem zeta_omega_link {d : ℕ} {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    {κ : GNode G.tree → Mom d} (hκ : IsDecoration G κ) {l : (Fin 2 × Path) × (Fin 2 × Path)}
    (hl : l ∈ Q.links) (b b' : GBranch G.tree) (hb : b.1 = l.1) (hb' : b'.1 = l.2) :
    ((G.sign b'.toNode : ℤ) : ℝ) * omegaNode G κ b' =
      -(((G.sign b.toNode : ℤ) : ℝ) * omegaNode G κ b) := by
  obtain ⟨s₁, s₂, hxy, hs⟩ := xy_link hQ hG hκ hl b b' hb hb'
  rw [omegaNode_eq hκ, omegaNode_eq hκ, hs]
  have h12 : ((s₁ : ℤ) : ℝ) * ((s₂ : ℤ) : ℝ) * (((s₁ : ℤ) : ℝ) * ((s₂ : ℤ) : ℝ)) = 1 := by
    rcases Int.units_eq_one_or s₁ with rfl | rfl <;> rcases Int.units_eq_one_or s₂ with rfl | rfl <;>
      norm_num
  have key : inner ℝ (xNode κ b') (yNode κ b') =
      ((s₁ : ℤ) : ℝ) * ((s₂ : ℤ) : ℝ) * inner ℝ (xNode κ b) (yNode κ b) := by
    rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy, inner_smul_units, real_inner_comm,
      inner_smul_units]
    · rw [real_inner_comm]; ring
    · ring
  rw [key]
  simp only [Units.val_mul, Units.val_neg, Int.cast_mul, Int.cast_neg]
  linear_combination (-(((G.sign b.toNode : ℤ) : ℝ) * (2 * inner ℝ (xNode κ b) (yNode κ b)))) * h12

/-- `ε` in terms of `x` and `y`: `+1` if both are nonzero, `-1` if both vanish, `0` otherwise. -/
def epsXY {d : ℕ} (x y : Fin d → ℤ) : ℝ :=
  if y ≠ 0 ∧ x ≠ 0 then 1 else if y = 0 ∧ x = 0 then -1 else 0

theorem epsCoef_eq_epsXY {d : ℕ} (n₁ n₂ n₃ n : Fin d → ℤ) (h : n = n₁ - n₂ + n₃) :
    epsCoef n₁ n₂ n₃ = epsXY (n₁ - n) (n - n₃) := by
  have h1 : n - n₃ = n₁ - n₂ := by rw [h]; abel
  have h2 : n₁ - n = n₂ - n₃ := by rw [h]; abel
  have e1 : (n₂ = n₁) ↔ (n - n₃ = 0) := by rw [h1, sub_eq_zero, eq_comm]
  have e1' : (n₁ = n₂) ↔ (n - n₃ = 0) := by rw [h1, sub_eq_zero]
  have e2 : (n₂ = n₃) ↔ (n₁ - n = 0) := by rw [h2, sub_eq_zero]
  unfold epsCoef epsXY
  simp only [ne_eq, e1, e1', e2]

theorem epsXY_smul {d : ℕ} (s₁ s₂ : ℤˣ) (x y : Fin d → ℤ) :
    epsXY ((s₁ : ℤ) • x) ((s₂ : ℤ) • y) = epsXY x y := by
  have h1 : ∀ (s : ℤˣ) (v : Fin d → ℤ), (s : ℤ) • v = 0 ↔ v = 0 := fun s v => by
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp
  simp only [epsXY, ne_eq, h1]

theorem epsXY_swap {d : ℕ} (x y : Fin d → ℤ) : epsXY y x = epsXY x y := by
  unfold epsXY; by_cases a : x = 0 <;> by_cases b : y = 0 <;> simp [a, b]

/-- **`ε_{𝔫'} = ε_𝔫` for linked nodes** and every integer decoration (TARGET (defcoef0); used in
TARGET (incohproof2): `ε` depends only on `(x_𝔫, y_𝔫)`). -/
theorem epsCoef_link {d : ℕ} {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    {κ : GNode G.tree → (Fin d → ℤ)} (hκ : IsDecoration G κ) {l : (Fin 2 × Path) × (Fin 2 × Path)}
    (hl : l ∈ Q.links) (b b' : GBranch G.tree) (hb : b.1 = l.1) (hb' : b'.1 = l.2) :
    epsCoef (κ (b'.child 0)) (κ (b'.child 1)) (κ (b'.child 2)) =
      epsCoef (κ (b.child 0)) (κ (b.child 1)) (κ (b.child 2)) := by
  obtain ⟨s₁, s₂, hxy, -⟩ := xy_link hQ hG hκ hl b b' hb hb'
  rw [epsCoef_eq_epsXY _ _ _ _ (hκ.1 b'), epsCoef_eq_epsXY _ _ _ _ (hκ.1 b)]
  change epsXY (xNode κ b') (yNode κ b') = epsXY (xNode κ b) (yNode κ b)
  rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy, epsXY_smul]
  exact epsXY_swap _ _

end WaveTurbulence.Links
