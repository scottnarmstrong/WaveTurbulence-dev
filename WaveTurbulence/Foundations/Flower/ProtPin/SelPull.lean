/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermStarCut
public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiBound

/-! # D3 PROT-PIN (R181): D3's multiplier with a first-layer flag `ann`, pulled back to the pieces

The `ann`-generalization of `StarPull`/`TermStarCut` (whose statements fix `ann = fun _ => false`): the first filter
layer `filtWeight F ann M` carries `chiD` on the branches with `ann b = true` (a selected annular filter) and `chi0`
elsewhere. Pulled back along a piece embedding, the flag is `ann ∘ β` (`fD3'_pullA`, `pull_multA`); a branch factor is
bounded by its star cost times `chiDSup` (`norm_fD3'_leA`; `chiDSup ≥ 1` bounds both `|chiD|` and `chi0`). The
`ann = false` versions in StarPull/TermStarCut are the specializations in content. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open scoped Classical

namespace WaveTurbulence.Flower.ProtPin.Sel

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.FlShell

variable {w w' d : ℕ}

/-- D3's gate-form multiplier with a first-layer flag: `starWeight S ω · filtWeight F ann M · filtWeight Fu 0 Mu`. -/
def gateMA {G : Garden w} (S : Finset (GNode G.tree)) (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M : GBranch G.tree → ℝ)
    (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) (K : GNode G.tree → Mom d) : ℂ :=
  Flower.IncTop.starWeight S ω K * filtWeight F ann M K * filtWeight Fu (fun _ => false) Mu K

/-- D3's multiplier of a piece with a first-layer flag, pulled back along `(ι, β)`. -/
def pullMultA {G : Garden w} {G' : Garden w'} (ι : GNode G'.tree → GNode G.tree)
    (β : GBranch G'.tree → GBranch G.tree) (S : Finset (GNode G.tree)) (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M : GBranch G.tree → ℝ)
    (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) (K : GNode G'.tree → Mom d) : ℂ :=
  gateMA (pullS ι S) (fun z => ω (ι z)) (pullF β F) (fun y => ann (β y)) (fun y => M (β y)) (pullF β Fu)
    (fun y => Mu (β y)) K

section Emb

variable {G : Garden w} {G' : Garden w'} {ι : GNode G'.tree → GNode G.tree} {β : GBranch G'.tree → GBranch G.tree}

/-- **A pulled-back branch factor is the branch factor of the image** (any flag). -/
theorem fD3'_pullA (E : PieceEmb ι β) (S : Finset (GNode G.tree)) (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M : GBranch G.tree → ℝ)
    (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) (x : GBranch G'.tree) (ξ : Fin 4 → Mom d) :
    fD3' (pullS ι S) (fun z => ω (ι z)) (pullF β F) (fun y => ann (β y)) (fun y => M (β y)) (pullF β Fu)
        (fun y => Mu (β y)) x ξ =
      fD3' S ω F ann M Fu Mu (β x) ξ := by
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

/-- **The pulled-back multiplier** with a flag. -/
theorem pull_multA (E : PieceEmb ι β) (S : Finset (GNode G.tree)) (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M : GBranch G.tree → ℝ)
    (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) (K : GNode G'.tree → Mom d) :
    ∏ x, fD3' S ω F ann M Fu Mu (β x) (bstar K x) = pullMultA ι β S ω F ann M Fu Mu K := by
  unfold pullMultA gateMA
  rw [starFilt_local' (pullS ι S) (fun a ha _ => ((Finset.mem_filter.mp ha).2.2.2 ‹_›))]
  exact Finset.prod_congr rfl fun x _ => (fD3'_pullA E S ω F ann M Fu Mu x _).symm

end Emb

/-- **A branch factor with a flag is bounded by its star cost times `chiDSup`.** -/
theorem norm_fD3'_leA {G : Garden w} (S : Finset (GNode G.tree)) (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (c : GNode G.tree → ℝ) {J : ℕ} (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented J (ω a) (c a))
    (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M : GBranch G.tree → ℝ)
    (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) (b : GBranch G.tree) (ξ : Fin 4 → Mom d) :
    ‖fD3' S ω F ann M Fu Mu b ξ‖ ≤ costB S c b * FiltCoh.chiDSup := by
  have h1 := FiltCoh.one_le_chiDSup
  have hchiA : ∀ (p : Prop) [Decidable p] (q : Bool) (x : ℝ),
      ‖(if p then (((if q then chiD else chi0) x : ℝ) : ℂ) else 1)‖ ≤ FiltCoh.chiDSup := by
    intro p _ q x
    by_cases hp : p
    · rw [if_pos hp, Complex.norm_real, Real.norm_eq_abs]
      cases q
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg x)]
        exact (XChain.ProductCut.chi0_le_one x).trans h1
      · simp only [↓reduceIte]
        exact FiltCoh.abs_chiD_le_sup x
    · rw [if_neg hp]
      simpa using h1
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
  have hk0 : 0 ≤ ∏ i : Fin 3, (if b.child i ∈ S ∧ (b.child i).1.2 ∉ (G.tree (b.child i).1.1).branching then
      max (c (b.child i)) 0 else 1) := Finset.prod_nonneg fun i _ => by split_ifs <;> simp
  unfold fD3' fD3 leafKids costB
  simp only [norm_mul, Bool.false_eq_true, ↓reduceIte]
  have hF := hchiA (b ∈ F) (ann b) (|resFactor (ξ 1) (ξ 2) (ξ 3) (ξ 0)| / M b)
  have hFu := hchi (b ∈ Fu) (|resFactor (ξ 1) (ξ 2) (ξ 3) (ξ 0)| / Mu b)
  calc _ ≤ (if b.toNode ∈ S then max (c b.toNode) 0 else 1) * (FiltCoh.chiDSup * 1) *
        ∏ i : Fin 3, (if b.child i ∈ S ∧ (b.child i).1.2 ∉ (G.tree (b.child i).1.1).branching then
          max (c (b.child i)) 0 else 1) :=
        mul_le_mul (mul_le_mul hs (mul_le_mul hF hFu (norm_nonneg _) (by linarith))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hs0) hk (norm_nonneg _)
          (mul_nonneg hs0 (by linarith))
    _ = _ := by ring

end WaveTurbulence.Flower.ProtPin.Sel
