/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepLfClk1
import Mathlib.Tactic

/-!
# S2 REPRESENTS, F-LEAFCLK (`hind`): the class kernel does not see the clock of a leaf lower child

`unitHk_hind`: if every member of the canonical class has, at each lower child `i ∈ {1, 2}` flagged `leaf i`, a leaf of its
skeleton tree (hypothesis `hleaf`: this is what the common `G_sb` structure of the class members gives, `hclk = inl r`), then
the modulated class kernel `unitHk` is independent of the flagged clock coordinates.  The proof sums the V5 member statement
`clRecenteredLocalKernelModC_congr` through `recentered_class_sumMod`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C VineParamContract
open scoped ENNReal

variable {w : ℕ} {ι : Type*} [Fintype ι]

theorem reach_of_mem_canonFinsetK {p : ℕ} {kind : Bool} {A : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family}
    {x : Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family} (hx : x ∈ canonFinsetK p kind A c) :
    ∃ M : List ι, Reach p kind M A c x.1 x.2 := by
  classical
  unfold canonFinsetK at hx
  split_ifs at hx with h
  · obtain ⟨M, -, hM⟩ := (Set.Finite.mem_toFinset h).mp hx
    exact ⟨M, hM⟩
  · exact absurd hx (Finset.notMem_empty _)

/-- The modulated class kernel is independent of the clocks of lower children that are leaves in every member. -/
theorem twistedRecenteredModC_congr_leaf {d p : ℕ} {kind : Bool} {A : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} (lam : ℝ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d)
    (t0 t1 t2 t1' t2' : ℝ) (e f g k : Mom d)
    (hp : ∀ x ∈ canonFinsetK p kind A c,
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.2 ∉
          (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.1).branching ∨ t1 = t1')
    (hn : ∀ x ∈ canonFinsetK p kind A c,
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.2 ∉
          (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.1).branching ∨ t2 = t2') :
    WaveTurbulence.VineEstS5C.Cont.twistedRecenteredModC A.skeleton c.a (canonFinsetK p kind A c) L γ δ F base lam
        t0 t1 t2 e f g k =
      WaveTurbulence.VineEstS5C.Cont.twistedRecenteredModC A.skeleton c.a (canonFinsetK p kind A c) L γ δ F base lam
        t0 t1' t2' e f g k := by
  rw [WaveTurbulence.VineEstS5C.Cont.recentered_class_sumMod (p := p) lam (kind := kind) (A := A) (c := c)
      (canonFinsetK p kind A c) (fun x hx => reach_of_mem_canonFinsetK hx) L γ δ F base t0 t1 t2 e f g k,
    WaveTurbulence.VineEstS5C.Cont.recentered_class_sumMod (p := p) lam (kind := kind) (A := A) (c := c)
      (canonFinsetK p kind A c) (fun x hx => reach_of_mem_canonFinsetK hx) L γ δ F base t0 t1' t2' e f g k]
  refine Finset.sum_congr rfl fun x hx => ?_
  exact WaveTurbulence.VineEstS5C.Cont.clRecenteredLocalKernelModC_congr x.1.data x.1.plain
    (clRegionData x.1.skeleton x.2.block x.2.cl) L γ δ F (stateLayer x.1) (stateLayer_isLayering x.1) base lam
    t0 t1 t2 t1' t2' e f g k (hp x hx) (hn x hx)

/-- **`hind`** in the form consumed by `exists_hinge_data_units_leaf`. -/
theorem unitHk_hind (P : WTParams) (p : ℕ) {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} (B : CLChainAssembly G R n)
    (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (h : ℕ → Mom P.d → ℝ) (wBar : Mom P.d)
    (leaf : Fin 3 → Prop) (hl0 : ¬ leaf 0)
    (hleaf1 : leaf 1 → ∀ x ∈ canonFinsetK p (objKind w) (startState B RD hG layer hLayer) (chainStart B),
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.2 ∉
        (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.1).branching)
    (hleaf2 : leaf 2 → ∀ x ∈ canonFinsetK p (objKind w) (startState B RD hG layer hLayer) (chainStart B),
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.2 ∉
        (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.1).branching)
    (lam : ℤ) (t t' : Fin 3 → ℝ) (k : Fin 4 → Mom P.d) (ht : ∀ i, ¬ leaf i → t i = t' i) :
    unitHk P p B RD hG layer hLayer h wBar lam t k = unitHk P p B RD hG layer hLayer h wBar lam t' k := by
  have h0 : t 0 = t' 0 := ht 0 hl0
  unfold unitHk
  rw [h0]
  apply twistedRecenteredModC_congr_leaf (A := startState B RD hG layer hLayer) (c := chainStart B)
  · intro x hx
    by_cases h1 : leaf 1
    · exact Or.inl (hleaf1 h1 x hx)
    · exact Or.inr (ht 1 h1)
  · intro x hx
    by_cases h2 : leaf 2
    · exact Or.inl (hleaf2 h2 x hx)
    · exact Or.inr (ht 2 h2)

end WaveTurbulence.Represents
