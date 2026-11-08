/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Bond
public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitSummand
public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitGeom2

/-! # V5-SPACE-EXT: the bond weight splits at a chain joint

For blocks `S` (joints `a, b`) and `T` (joints `b, c`) with `S ∩ T = {b}` and `S ∪ T` a block, every dart with
both ends in `S ∪ T` has both ends in `S` or both in `T`, never both (the degree counts of `defblock`).
Hence `bondW (S ∪ T) = bondW S * bondW T`. The labels a region dart reads lie in the realization of the
region, so the S factor sees only `rA`/`glue`'s S side and the T factor only `rB`/`glue`'s T side. -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.VineSpaceB
open WaveTurbulence TTree Twist RegRed VineEstS4

variable {w d : ℕ}

section Mol
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem degIn_eq_out_add_in (S : Finset V) (v : V) : M.degIn S v = M.outIn S v + M.inIn S v := by
  have he := ((M.dartsAt v).filter fun x => M.InGroup S x).card_filter_add_card_filter_not (fun x => M.out x = true)
  rw [Finset.filter_filter, Finset.filter_filter] at he
  simp only [Bool.not_eq_true] at he
  exact he.symm

/-- Darts at `v` in group `S`. -/
def dartsIn (S : Finset V) (v : V) : Finset D := (M.dartsAt v).filter fun x => M.InGroup S x

theorem mem_dartsIn {S : Finset V} {v : V} {x : D} :
    x ∈ dartsIn M S v ↔ M.atom x = v ∧ M.InGroup S x := by
  simp [dartsIn, Molecule.dartsAt]

theorem card_dartsIn (S : Finset V) (v : V) : (dartsIn M S v).card = M.degIn S v := rfl

theorem dartsIn_mono {S S' : Finset V} (h : S ⊆ S') (v : V) : dartsIn M S v ⊆ dartsIn M S' v := by
  intro x hx
  rw [mem_dartsIn] at hx ⊢
  exact ⟨hx.1, h hx.2.1, h hx.2.2⟩

/-- If the group degree does not grow, no new dart at `v` appears. -/
theorem dartsIn_eq_of_degIn {S S' : Finset V} (h : S ⊆ S') {v : V} (hd : M.degIn S' v ≤ M.degIn S v) :
    dartsIn M S v = dartsIn M S' v :=
  Finset.eq_of_subset_of_card_le (dartsIn_mono M h v) hd

variable {M}
variable {S T : Finset V} {a b c : V} (hS : M.IsBlock S a b) (hT : M.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : M.IsBlock (S ∪ T) a c)
include hS hT hi hU

theorem degIn_S_eq {v : V} (hv : v ∈ S) (hvb : v ≠ b) : M.degIn (S ∪ T) v ≤ M.degIn S v := by
  have hvT : v ∉ T := fun h => hvb (Finset.mem_singleton.mp (hi ▸ Finset.mem_inter.mpr ⟨hv, h⟩))
  by_cases hva : v = a
  · subst hva
    rw [degIn_eq_out_add_in, degIn_eq_out_add_in, hS.2.2.2.2.1, hS.2.2.2.2.2.1, hU.2.2.2.2.1, hU.2.2.2.2.2.1]
  · have hvc : v ≠ c := fun h => hvT (h ▸ hT.2.2.1)
    rw [hS.2.2.2.2.2.2.2.2.1 v hv hva hvb, hU.2.2.2.2.2.2.2.2.1 v (Finset.mem_union_left _ hv) hva hvc]

theorem degIn_T_eq {v : V} (hv : v ∈ T) (hvb : v ≠ b) : M.degIn (S ∪ T) v ≤ M.degIn T v := by
  have hvS : v ∉ S := fun h => hvb (Finset.mem_singleton.mp (hi ▸ Finset.mem_inter.mpr ⟨h, hv⟩))
  by_cases hvc : v = c
  · subst hvc
    rw [degIn_eq_out_add_in, degIn_eq_out_add_in, hT.2.2.2.2.2.2.1, hT.2.2.2.2.2.2.2.1,
      hU.2.2.2.2.2.2.1, hU.2.2.2.2.2.2.2.1]
  · have hva : v ≠ a := fun h => hvS (h ▸ hS.2.1)
    rw [hT.2.2.2.2.2.2.2.2.1 v hv hvb hvc, hU.2.2.2.2.2.2.2.2.1 v (Finset.mem_union_right _ hv) hva hvc]

/-- **A dart of `S ∪ T` is a dart of `S` or of `T`.** -/
theorem inGroup_union {x : D} (hx : M.InGroup (S ∪ T) x) : M.InGroup S x ∨ M.InGroup T x := by
  have key : ∀ {S₁ T₁ : Finset V}, S₁ ∪ T₁ = S ∪ T → S₁ ∩ T₁ = {b} →
      (∀ {v}, v ∈ S₁ → v ≠ b → M.degIn (S ∪ T) v ≤ M.degIn S₁ v) →
      ∀ {y : D}, M.InGroup (S ∪ T) y → M.atom y ∈ S₁ → M.atom y ≠ b → M.InGroup S₁ y := by
    intro S₁ T₁ hun hint hdeg y hy hv hvb
    have he := dartsIn_eq_of_degIn M (hun ▸ Finset.subset_union_left) (hdeg hv hvb)
    have hmem : y ∈ dartsIn M (S ∪ T) (M.atom y) := (mem_dartsIn M).mpr ⟨rfl, hy⟩
    rw [← he] at hmem
    exact ((mem_dartsIn M).mp hmem).2
  have hv := hx.1
  rcases Finset.mem_union.mp hv with hvS | hvT
  · by_cases hvb : M.atom x = b
    · rcases Finset.mem_union.mp hx.2 with h | h
      · exact Or.inl ⟨hvS, h⟩
      · exact Or.inr ⟨hvb ▸ hT.2.1, h⟩
    · exact Or.inl (key rfl hi (fun h1 h2 => degIn_S_eq hS hT hi hU h1 h2) hx hvS hvb)
  · by_cases hvb : M.atom x = b
    · rcases Finset.mem_union.mp hx.2 with h | h
      · exact Or.inl ⟨hvb ▸ hS.2.2.1, h⟩
      · exact Or.inr ⟨hvT, h⟩
    · exact Or.inr (key (Finset.union_comm T S ▸ rfl) (Finset.inter_comm T S ▸ hi)
        (fun h1 h2 => degIn_T_eq hS hT hi hU h1 h2) hx hvT hvb)

/-- **No dart is a dart of both blocks** (no self-loop at the joint). -/
theorem not_inGroup_both {x : D} (hS' : M.InGroup S x) (hT' : M.InGroup T x) : False := by
  have hxb : M.atom x = b := Finset.mem_singleton.mp (hi ▸ Finset.mem_inter.mpr ⟨hS'.1, hT'.1⟩)
  have hbU : b ∈ S ∪ T := Finset.mem_union_left _ hS.2.2.1
  have hba : b ≠ a := hS.2.2.2.1.symm
  have hbc : b ≠ c := hT.2.2.2.1
  have h4 : M.degIn (S ∪ T) b = 4 := hU.2.2.2.2.2.2.2.2.1 b hbU hba hbc
  have h2S : M.degIn S b = 2 := by rw [degIn_eq_out_add_in, hS.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.1]
  have h2T : M.degIn T b = 2 := by rw [degIn_eq_out_add_in, hT.2.2.2.2.1, hT.2.2.2.2.2.1]
  have hsub : dartsIn M (S ∪ T) b ⊆ dartsIn M S b ∪ dartsIn M T b := by
    intro y hy
    obtain ⟨hya, hyU⟩ := (mem_dartsIn M).mp hy
    rcases inGroup_union hS hT hi hU hyU with h | h
    · exact Finset.mem_union_left _ ((mem_dartsIn M).mpr ⟨hya, h⟩)
    · exact Finset.mem_union_right _ ((mem_dartsIn M).mpr ⟨hya, h⟩)
  have hxi : x ∈ dartsIn M S b ∩ dartsIn M T b :=
    Finset.mem_inter.mpr ⟨(mem_dartsIn M).mpr ⟨hxb, hS'⟩, (mem_dartsIn M).mpr ⟨hxb, hT'⟩⟩
  have hc := Finset.card_le_card hsub
  have hcu := Finset.card_union_add_card_inter (dartsIn M S b) (dartsIn M T b)
  have hpos : 0 < (dartsIn M S b ∩ dartsIn M T b).card := Finset.card_pos.mpr ⟨x, hxi⟩
  have e1 : (dartsIn M S b).card = 2 := h2S
  have e2 : (dartsIn M T b).card = 2 := h2T
  have e0 : (dartsIn M (S ∪ T) b).card = 4 := h4
  have hc' : (dartsIn M (S ∪ T) b).card ≤ (dartsIn M S b ∪ dartsIn M T b).card := hc
  omega

end Mol

section Garden
variable {G : Garden w}

theorem regionDarts_union {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
    (hU : G.molecule.IsBlock (S ∪ T) a c) :
    regionDarts G (S ∪ T) = regionDarts G S ∪ regionDarts G T := by
  ext y
  simp only [Finset.mem_union, mem_regionDarts]
  constructor
  · exact inGroup_union hS hT hi hU
  · rintro (h | h)
    · exact ⟨Finset.mem_union_left _ h.1, Finset.mem_union_left _ h.2⟩
    · exact ⟨Finset.mem_union_right _ h.1, Finset.mem_union_right _ h.2⟩

theorem regionDarts_disjoint {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
    (hU : G.molecule.IsBlock (S ∪ T) a c) :
    Disjoint (regionDarts G S) (regionDarts G T) := by
  rw [Finset.disjoint_left]
  intro y hyS hyT
  exact not_inGroup_both hS hT hi hU (mem_regionDarts.mp hyS) (mem_regionDarts.mp hyT)

/-- **The bond weight of a concatenation is the product of the two block weights.** -/
theorem bondW_union (ψ : ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d) (lay : GBranch G.tree → ℕ)
    {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
    (hU : G.molecule.IsBlock (S ∪ T) a c) (x : GNode G.tree → Fin d → ℤ) :
    bondW ψ L base G lay (S ∪ T) x = bondW ψ L base G lay S x * bondW ψ L base G lay T x := by
  unfold bondW
  rw [regionDarts_union hS hT hi hU, Finset.prod_union (regionDarts_disjoint hS hT hi hU)]

/-- The node read by a region dart lies in the realization of the region. -/
theorem dartNode_mem_real {U : Finset (GBranch G.tree)} {y : GardenDart G} (hy : y ∈ regionDarts G U) :
    Mole.dartNode G y ∈ clRealizationNodes G U := by
  have hy' := mem_regionDarts.mp hy
  cases y with
  | inl c =>
    obtain ⟨c, s⟩ := c
    have hc : c.1 ∈ U := by
      cases s
      · exact hy'.1
      · exact hy'.2
    exact (branch_mem_clRealizationNodes c.1).mpr hc
  | inr l =>
    exact (leaf_mem_clRealizationNodes l.1).mpr ⟨l.2.1, l.2.2.1, l.2.2.2, hy'⟩

theorem dartNode_mem_splitA {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (RS : CLRegionData G S a b)
    {y : GardenDart G} (hy : y ∈ regionDarts G S) : Mole.dartNode G y ∈ splitA RS :=
  Finset.mem_union_left _ (dartNode_mem_real hy)

theorem dartNode_mem_support {T : Finset (GBranch G.tree)} {b c : GBranch G.tree} (RT : CLRegionData G T b c)
    {y : GardenDart G} (hy : y ∈ regionDarts G T) : Mole.dartNode G y ∈ clLocalSupport RT :=
  Finset.mem_union_left _ (dartNode_mem_real hy)

variable (ψ : ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d) (lay : GBranch G.tree → ℕ)

theorem bondW_rA {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (RS : CLRegionData G S a b)
    (x : GNode G.tree → Fin d → ℤ) : bondW ψ L base G lay S (rA RS x) = bondW ψ L base G lay S x :=
  bondW_congr ψ L base G S (fun _ _ => rfl) (fun _y hy => by
    simp only [rA, dartNode_mem_splitA RS hy, ite_true])

theorem bondW_rB {T : Finset (GBranch G.tree)} {b c : GBranch G.tree} (RT : CLRegionData G T b c)
    (x : GNode G.tree → Fin d → ℤ) : bondW ψ L base G lay T (rB RT x) = bondW ψ L base G lay T x :=
  bondW_congr ψ L base G T (fun _ _ => rfl) (fun _y hy => by
    simp only [rB, dartNode_mem_support RT hy, ite_true])

theorem bondW_glue_S {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (RS : CLRegionData G S a b)
    (xS xT : GNode G.tree → Fin d → ℤ) :
    bondW ψ L base G lay S (glue RS xS xT) = bondW ψ L base G lay S xS :=
  bondW_congr ψ L base G S (fun _ _ => rfl) (fun _y hy => glue_A RS xS xT (dartNode_mem_splitA RS hy))

theorem bondW_glue_T {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
    (hU : G.molecule.IsBlock (S ∪ T) a c) (RS : CLRegionData G S a b) (RT : CLRegionData G T b c)
    {L' : ℝ} (hL : L' ≠ 0) {base' : Mom d} {xS xT : GNode G.tree → Fin d → ℤ} {β2 β3 : Mom d}
    (hc : BdAt RT L' base' (bdT RT L' base' xS β2 β3) xT) :
    bondW ψ L base G lay T (glue RS xS xT) = bondW ψ L base G lay T xT :=
  bondW_congr ψ L base G T (fun _ _ => rfl) (fun _y hy =>
    glue_B hS hT hi hU RS RT hL hc (dartNode_mem_support RT hy))

end Garden

end WaveTurbulence.VineSpaceB
