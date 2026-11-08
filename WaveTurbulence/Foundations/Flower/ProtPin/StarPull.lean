/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.MultLeaf
public import WaveTurbulence.Foundations.Flower.FiltCoh.TreeStarLayer
public import WaveTurbulence.Foundations.XChain.ProductCut.ProdCut

/-! # D3 PROT-PIN: D3's multiplier pulled back to the pieces of a cut

D2c's `multFactors_D3'` writes the multiplier of a cut piece as a product over its branches of D3's branch factors
`fD3'` read at the placed branches. For the gates the piece multiplier must be D3's multiplier of the piece itself:
`starWeight S' ω' · filtWeight F' 0 M' · filtWeight Fu' 0 Mu'`. Given an embedding of the piece (`PieceEmb`: node and
branch maps commuting with `toNode` and `child`) the pulled-back data (`pullS`, `pullF`) do this exactly
(`pull_mult`): a node of the piece carries its star iff its image does and both are branching or both leaves (the lone
leaf of a prefix is a branching node of the object: its star belongs to the cut factor), and roots of the piece carry
no star unless branching. The star costs localize the same way (`costB`, `prod_cost_branch`, `pull_cost`), and a
branch factor is bounded by its cost (`norm_fD3'_le`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open scoped Classical

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.FlShell

variable {w w' d : ℕ}

/-- An embedding of a piece: node and branch maps commuting with `toNode` and `child`. -/
structure PieceEmb {G : Garden w} {G' : Garden w'} (ι : GNode G'.tree → GNode G.tree)
    (β : GBranch G'.tree → GBranch G.tree) : Prop where
  node : ∀ x, (β x).toNode = ι x.toNode
  child : ∀ x i, (β x).child i = ι (x.child i)

/-- The pulled-back star set. -/
def pullS {G : Garden w} {G' : Garden w'} (ι : GNode G'.tree → GNode G.tree) (S : Finset (GNode G.tree)) :
    Finset (GNode G'.tree) :=
  Finset.univ.filter fun z => ι z ∈ S ∧
    (z.1.2 ∈ (G'.tree z.1.1).branching ↔ (ι z).1.2 ∈ (G.tree (ι z).1.1).branching) ∧
    (z.1.2 = [] → z.1.2 ∈ (G'.tree z.1.1).branching)

/-- The pulled-back filter set. -/
def pullF {G : Garden w} {G' : Garden w'} (β : GBranch G'.tree → GBranch G.tree) (F : Finset (GBranch G.tree)) :
    Finset (GBranch G'.tree) :=
  Finset.univ.filter fun x => β x ∈ F

theorem pullF_empty {G : Garden w} {G' : Garden w'} (β : GBranch G'.tree → GBranch G.tree) :
    pullF β (∅ : Finset (GBranch G.tree)) = ∅ := by
  simp [pullF]

theorem mem_pullF {G : Garden w} {G' : Garden w'} (β : GBranch G'.tree → GBranch G.tree)
    (F : Finset (GBranch G.tree)) (x : GBranch G'.tree) : x ∈ pullF β F ↔ β x ∈ F := by
  simp [pullF]

section Emb

variable {G : Garden w} {G' : Garden w'} {ι : GNode G'.tree → GNode G.tree} {β : GBranch G'.tree → GBranch G.tree}

theorem PieceEmb.br (E : PieceEmb ι β) (z : GNode G'.tree) (hz : z.1.2 ∈ (G'.tree z.1.1).branching) :
    (ι z).1.2 ∈ (G.tree (ι z).1.1).branching := by
  have h1 : (ι z).1 = (β ⟨z.1, hz⟩).1 := (congrArg Subtype.val (E.node ⟨z.1, hz⟩)).symm
  rw [h1]
  exact (β ⟨z.1, hz⟩).2

theorem child_path_ne_nil {T : Fin w' → TTree} (x : GBranch T) (i : Fin 3) : (x.child i).1.2 ≠ [] := by
  simp [GBranch.child]

theorem PieceEmb.mem_node (E : PieceEmb ι β) (S : Finset (GNode G.tree)) (x : GBranch G'.tree) :
    x.toNode ∈ pullS ι S ↔ (β x).toNode ∈ S := by
  simp only [pullS, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [E.node x]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, ⟨fun _ => E.br _ x.2, fun _ => x.2⟩, fun _ => x.2⟩

theorem PieceEmb.mem_kid (E : PieceEmb ι β) (S : Finset (GNode G.tree)) (x : GBranch G'.tree) (i : Fin 3) :
    (x.child i ∈ pullS ι S ∧ (x.child i).1.2 ∉ (G'.tree (x.child i).1.1).branching) ↔
      ((β x).child i ∈ S ∧ ((β x).child i).1.2 ∉ (G.tree ((β x).child i).1.1).branching) := by
  rw [E.child x i]
  simp only [pullS, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, h2, -⟩, h3⟩
    exact ⟨h1, fun h => h3 (h2.mpr h)⟩
  · rintro ⟨h1, h2⟩
    have h3 : (x.child i).1.2 ∉ (G'.tree (x.child i).1.1).branching := fun h => h2 (E.br _ h)
    exact ⟨⟨h1, ⟨fun h => absurd h h3, fun h => absurd h h2⟩, fun h0 => absurd h0 (child_path_ne_nil x i)⟩, h3⟩

/-- **A pulled-back branch factor is the branch factor of the image.** -/
theorem fD3'_pull (E : PieceEmb ι β) (S : Finset (GNode G.tree)) (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (F : Finset (GBranch G.tree)) (M : GBranch G.tree → ℝ) (Fu : Finset (GBranch G.tree))
    (Mu : GBranch G.tree → ℝ) (x : GBranch G'.tree) (ξ : Fin 4 → Mom d) :
    fD3' (pullS ι S) (fun z => ω (ι z)) (pullF β F) (fun _ => false) (fun y => M (β y)) (pullF β Fu)
        (fun y => Mu (β y)) x ξ =
      fD3' S ω F (fun _ => false) M Fu Mu (β x) ξ := by
  unfold fD3' fD3 leafKids
  congr 1
  · congr 1
    · by_cases h : (β x).toNode ∈ S
      · rw [if_pos ((E.mem_node S x).mpr h), if_pos h, E.node x]
      · rw [if_neg (fun h' => h ((E.mem_node S x).mp h')), if_neg h]
    · congr 1
      · by_cases h : β x ∈ F
        · rw [if_pos ((mem_pullF β F x).mpr h), if_pos h]
        · rw [if_neg (fun h' => h ((mem_pullF β F x).mp h')), if_neg h]
      · by_cases h : β x ∈ Fu
        · rw [if_pos ((mem_pullF β Fu x).mpr h), if_pos h]
        · rw [if_neg (fun h' => h ((mem_pullF β Fu x).mp h')), if_neg h]
  · refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : (β x).child i ∈ S ∧ ((β x).child i).1.2 ∉ (G.tree ((β x).child i).1.1).branching
    · rw [if_pos ((E.mem_kid S x i).mpr h), if_pos h, E.child x i]
    · rw [if_neg (fun h' => h ((E.mem_kid S x i).mp h')), if_neg h]

/-- **The pulled-back multiplier**: the product of the placed branch factors is D3's multiplier of the piece. -/
theorem pull_mult (E : PieceEmb ι β) (S : Finset (GNode G.tree)) (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (F : Finset (GBranch G.tree)) (M : GBranch G.tree → ℝ) (Fu : Finset (GBranch G.tree))
    (Mu : GBranch G.tree → ℝ) (K : GNode G'.tree → Mom d) :
    ∏ x, fD3' S ω F (fun _ => false) M Fu Mu (β x) (bstar K x) =
      Flower.IncTop.starWeight (pullS ι S) (fun z => ω (ι z)) K *
        filtWeight (pullF β F) (fun _ => false) (fun y => M (β y)) K *
        filtWeight (pullF β Fu) (fun _ => false) (fun y => Mu (β y)) K := by
  rw [starFilt_local' (pullS ι S) (fun a ha _ => ((Finset.mem_filter.mp ha).2.2.2 ‹_›))]
  exact Finset.prod_congr rfl fun x _ => (fD3'_pull E S ω F M Fu Mu x _).symm

end Emb

/-! ### Star costs -/

/-- One branch's share of the star cost `∏_{a ∈ S} max (c a) 0` (its own star and its leaf children's). -/
def costB {G : Garden w} (S : Finset (GNode G.tree)) (c : GNode G.tree → ℝ) (b : GBranch G.tree) : ℝ :=
  (if b.toNode ∈ S then max (c b.toNode) 0 else 1) *
    ∏ i : Fin 3, if b.child i ∈ S ∧ (b.child i).1.2 ∉ (G.tree (b.child i).1.1).branching then
      max (c (b.child i)) 0 else 1

theorem costB_nonneg {G : Garden w} (S : Finset (GNode G.tree)) (c : GNode G.tree → ℝ) (b : GBranch G.tree) :
    0 ≤ costB S c b := by
  unfold costB
  refine mul_nonneg (by split_ifs <;> simp) (Finset.prod_nonneg fun i _ => by split_ifs <;> simp)

/-- The constant star weight `max (c a) 0`. -/
def cstar {G : Garden w} (c : GNode G.tree → ℝ) : GNode G.tree → Flower.IncTop.Star 0 → ℂ :=
  fun a _ => ((max (c a) 0 : ℝ) : ℂ)

theorem fS_cstar {G : Garden w} (S : Finset (GNode G.tree)) (c : GNode G.tree → ℝ) (b : GBranch G.tree)
    (ξ : Fin 4 → Mom 0) : fS S (cstar c) b ξ = ((costB S c b : ℝ) : ℂ) := by
  unfold fS leafKids costB cstar
  simp only [Complex.ofReal_mul, Complex.ofReal_prod]
  congr 1
  · split_ifs <;> simp
  · refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs <;> simp

theorem fD3'_cstar {G : Garden w} (S : Finset (GNode G.tree)) (c : GNode G.tree → ℝ) (b : GBranch G.tree) :
    fD3' S (cstar c) ∅ (fun _ => false) (fun _ => 0) ∅ (fun _ => 0) b (fun _ => (0 : Mom 0)) =
      ((costB S c b : ℝ) : ℂ) := by
  rw [← fS_cstar S c b (fun _ => 0)]
  unfold fD3' fD3 fS
  simp

/-- **The star cost is branch-local** (roots in `S` branching). -/
theorem prod_cost_branch {G : Garden w} (S : Finset (GNode G.tree))
    (hroot : ∀ a ∈ S, a.1.2 = [] → a.1.2 ∈ (G.tree a.1.1).branching) (c : GNode G.tree → ℝ) :
    ∏ a ∈ S, max (c a) 0 = ∏ b : GBranch G.tree, costB S c b := by
  have h := starWeight_branch S hroot (cstar c) (fun _ => (0 : Mom 0))
  simp only [fS_cstar, Flower.IncTop.starWeight, cstar] at h
  have h' : ((∏ a ∈ S, max (c a) 0 : ℝ) : ℂ) = ((∏ b : GBranch G.tree, costB S c b : ℝ) : ℂ) := by
    push_cast
    exact h
  exact_mod_cast h'

theorem costB_pull {G : Garden w} {G' : Garden w'} {ι : GNode G'.tree → GNode G.tree}
    {β : GBranch G'.tree → GBranch G.tree} (E : PieceEmb ι β) (S : Finset (GNode G.tree)) (c : GNode G.tree → ℝ)
    (x : GBranch G'.tree) : costB (pullS ι S) (fun z => c (ι z)) x = costB S c (β x) := by
  have h := fD3'_pull (d := 0) E S (cstar c) ∅ (fun _ => 0) ∅ (fun _ => 0) x (fun _ => 0)
  rw [pullF_empty] at h
  have hc : (fun z => cstar c (ι z)) = cstar (fun z => c (ι z)) := rfl
  rw [hc, fD3'_cstar, fD3'_cstar] at h
  exact_mod_cast h

/-- **The star cost of a piece** is the product of the image costs. -/
theorem pull_cost {G : Garden w} {G' : Garden w'} {ι : GNode G'.tree → GNode G.tree}
    {β : GBranch G'.tree → GBranch G.tree} (E : PieceEmb ι β) (S : Finset (GNode G.tree)) (c : GNode G.tree → ℝ) :
    ∏ x, costB S c (β x) = ∏ a ∈ pullS ι S, max (c (ι a)) 0 := by
  rw [prod_cost_branch (pullS ι S) (fun a ha _ => ((Finset.mem_filter.mp ha).2.2.2 ‹_›))]
  exact Finset.prod_congr rfl fun x _ => (costB_pull E S c x).symm

/-- **A branch factor is bounded by its star cost** (presented stars, upper filters `≤ 1`). -/
theorem norm_fD3'_le {G : Garden w} (S : Finset (GNode G.tree)) (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (c : GNode G.tree → ℝ) {J : ℕ} (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented J (ω a) (c a))
    (F : Finset (GBranch G.tree)) (M : GBranch G.tree → ℝ) (Fu : Finset (GBranch G.tree))
    (Mu : GBranch G.tree → ℝ) (b : GBranch G.tree) (ξ : Fin 4 → Mom d) :
    ‖fD3' S ω F (fun _ => false) M Fu Mu b ξ‖ ≤ costB S c b := by
  have hchi : ∀ (p : Prop) [Decidable p] (x : ℝ), ‖(if p then ((chi0 x : ℝ) : ℂ) else 1)‖ ≤ 1 := by
    intro p _ x
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (XChain.ProductCut.chi0_nonneg x)]
      exact XChain.ProductCut.chi0_le_one x
    · simp
  have hs : ‖(if b.toNode ∈ S then ω b.toNode (WithLp.toLp 2 ξ) else 1)‖ ≤
      (if b.toNode ∈ S then max (c b.toNode) 0 else 1) := by
    split_ifs with h
    · exact FiltCoh.norm_star_le (hpres _ h) _
    · simp
  have hk : ‖∏ i : Fin 3, (if b.child i ∈ S ∧ (b.child i).1.2 ∉ (G.tree (b.child i).1.1).branching then
      ω (b.child i) (WithLp.toLp 2 fun _ => ξ i.succ) else 1)‖ ≤
      ∏ i : Fin 3, (if b.child i ∈ S ∧ (b.child i).1.2 ∉ (G.tree (b.child i).1.1).branching then
        max (c (b.child i)) 0 else 1) := by
    rw [norm_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
    split_ifs with h
    · exact FiltCoh.norm_star_le (hpres _ h.1) _
    · simp
  have hs0 : 0 ≤ (if b.toNode ∈ S then max (c b.toNode) 0 else 1) := by split_ifs <;> simp
  unfold fD3' fD3 leafKids costB
  simp only [norm_mul, Bool.false_eq_true, ↓reduceIte]
  exact (mul_le_mul (mul_le_mul hs (mul_le_mul (hchi _ _) (hchi _ _) (norm_nonneg _) zero_le_one)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hs0) hk (norm_nonneg _) (mul_nonneg hs0 (by norm_num))).trans
    (le_of_eq (by ring))

end WaveTurbulence.Flower.ProtPin
