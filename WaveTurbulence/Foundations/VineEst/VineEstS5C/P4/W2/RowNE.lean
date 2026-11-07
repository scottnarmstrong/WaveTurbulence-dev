/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.GlueBot
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.WinChain

/-! # P4-W2 (N1 → N2(b)): the native-except row form of every term

`RowFormNE RD … R ψ Dm Pex Bex Xq`: the row form of `ψ` on `R = (U, a, b)` whose weights are the NATIVE rows of the start data `RD`
(`qRow`/`tRow` with the layering `layer`, read at the exterior top clock `t 0`) at every pair outside `Pex` and every interior branch outside
`Bex`, the exceptional factor `Xq p` at the exceptional pairs `p ∈ Pex`, and `1` at the exceptional branches `v ∈ Bex`.

* `qRow_top`, `tRow_top`: the native rows of a region do not depend on the top clock (`cl_realization_parent`: realization nodes other than
  `a` are not roots).  `qRow_restrict`, `tRow_restrict`: they read the decoration only on the realization nodes.
* `stateLayer_lvl`: the layering of every level state is `layer` (`restrictState` keeps the data `RD`); `psiBase_eq`.
* `rowForm_congr`: the row form depends on the row weights only at the pairs and interior branches of the region.
* **`rowFormNE_termsB`**: every term of `Lvl.termsB` (BOT-DECOMP) has a native-except row form on its level's region, with `Pex ⊆` the
  pairs and `Bex ⊆` the interior branches; `Pex`, `Bex` collect the exceptional pair `p₀` and the lower joint `b` of every operative level
  (the split levels and the bottom level).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot

variable {w d : ℕ} {G : Garden w}

section Rows
variable (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
  {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem qRow_top (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) {p : SourcePair G}
    (hp : p ∈ clRegionalPairs hG U) (top top' : ℝ) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) :
    qRow D hG L γ δ F layer hLayer base top x u p = qRow D hG L γ δ F layer hLayer base top' x u p := by
  have hr := clRegionalPair_realization hG p hp
  have hne := pairLeaf_ne (a := a) hG ⟨p, hp⟩
  obtain ⟨h1, -⟩ := cl_realization_parent hU R _ hr.1 hne.1
  obtain ⟨h2, -⟩ := cl_realization_parent hU R _ hr.2 hne.2
  unfold qRow
  rw [parentClock_nonroot _ _ _ h1, parentClock_nonroot _ _ _ h2, parentClock_nonroot _ _ _ h1,
    parentClock_nonroot _ _ _ h2]

theorem tRow_top (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) {v : GBranch G.tree}
    (hv : v ∈ U.erase a) (top top' : ℝ) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) :
    tRow D hG L γ δ F layer hLayer base top x u v = tRow D hG L γ δ F layer hLayer base top' x u v := by
  have hr := (branch_mem_clRealizationNodes (U := U) v).mpr (Finset.mem_of_mem_erase hv)
  have hne : v.toNode ≠ a.toNode := fun h => (Finset.mem_erase.mp hv).1 (Mole.branch_toNode_injective h)
  obtain ⟨h1, -⟩ := cl_realization_parent hU R _ hr hne
  unfold tRow
  rw [parentClock_nonroot _ _ _ h1, parentClock_nonroot _ _ _ h1]

theorem qRow_restrict {p : SourcePair G} (hp : p ∈ clRegionalPairs hG U) (top : ℝ) {x x' : GNode G.tree → (Fin d → ℤ)}
    (hx : ∀ y ∈ clRealizationNodes G U, x y = x' y) (u : GBranch G.tree → ℝ) :
    qRow D hG L γ δ F layer hLayer base top x u p = qRow D hG L γ δ F layer hLayer base top x' u p := by
  unfold qRow cosetDecoration
  rw [hx _ (clRegionalPair_realization hG p hp).1]

theorem tRow_restrict {v : GBranch G.tree} (hv : v ∈ U) (top : ℝ) {x x' : GNode G.tree → (Fin d → ℤ)}
    (hx : ∀ y ∈ clRealizationNodes G U, x y = x' y) (u : GBranch G.tree → ℝ) :
    tRow D hG L γ δ F layer hLayer base top x u v = tRow D hG L γ δ F layer hLayer base top x' u v := by
  unfold tRow cosetDecoration
  rw [hx _ ((branch_mem_clRealizationNodes v).mpr hv)]

end Rows

theorem rA_real {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (RS : CLRegionData G S a b)
    (x : GNode G.tree → (Fin d → ℤ)) : ∀ y ∈ clRealizationNodes G S, rA RS x y = x y := fun y hy => by
  unfold rA splitA
  rw [if_pos (Finset.mem_union_left _ hy)]

theorem rB_real {T : Finset (GBranch G.tree)} {b c : GBranch G.tree} (RT : CLRegionData G T b c)
    (x : GNode G.tree → (Fin d → ℤ)) : ∀ y ∈ clRealizationNodes G T, rB RT x y = x y := fun y hy => by
  unfold rB clLocalSupport
  rw [if_pos (Finset.mem_union_left _ hy)]

/-- The row form depends on the row weights only at the pairs and the interior branches of the region. -/
theorem rowForm_congr (hG : G.IsPlain) {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (L γ δ : ℝ) (base : Mom d) (ψ : PsiT G d) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop)
    {Qw Qw' : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ}
    {Tw Tw' : GBranch G.tree → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ}
    (h : RowForm hG R L γ δ base ψ Dm Qw Tw)
    (hQ : ∀ p ∈ clRegionalPairs hG U, ∀ t u x, Qw p t u x = Qw' p t u x)
    (hT : ∀ v ∈ U.erase a, ∀ t u x, Tw v t u x = Tw' v t u x) :
    RowForm hG R L γ δ base ψ Dm Qw' Tw' := by
  intro β' κ t u
  rw [h β' κ t u, Finset.prod_congr rfl fun p hp => hQ p hp t u _, Finset.prod_congr rfl fun v hv => hT v hv t u _]

/-- **The native-except row form.** -/
def RowFormNE (RD : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b) (base : Mom d) (ψ : PsiT G d)
    (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop) (Pex : Finset (SourcePair G)) (Bex : Finset (GBranch G.tree))
    (Xq : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ) : Prop :=
  RowForm hG R L γ δ base ψ Dm
    (fun p t u x => if p ∈ Pex then Xq p t u x else qRow RD hG L γ δ F layer hLayer base (t 0) x u p)
    (fun v t u x => if v ∈ Bex then 1 else tRow RD hG L γ δ F layer hLayer base (t 0) x u v)

theorem rowFormNE_idx (RD : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    {U U' : Finset (GBranch G.tree)} {a a' b b' : GBranch G.tree} (hU : U = U') (ha : a = a') (hb : b = b')
    (R : CLRegionData G U a b) (R' : CLRegionData G U' a' b') (base : Mom d) (ψ : PsiT G d)
    (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop) (Pex : Finset (SourcePair G)) (Bex : Finset (GBranch G.tree))
    (Xq : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ)
    (h : RowFormNE RD hG L γ δ F layer hLayer R base ψ Dm Pex Bex Xq) :
    RowFormNE RD hG L γ δ F layer hLayer R' base ψ Dm Pex Bex Xq :=
  rowForm_idx hG hU ha hb R R' L γ δ base ψ Dm _ _ h

section Lvl
variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The layering of every level state is the start layering. -/
theorem stateLayer_lvl (lv : Lvl B) : stateLayer (lv.state B RD hG layer hLayer) = layer :=
  layeredReconstruction_inj RD hG (l₁ := stateLayer (lv.state B RD hG layer hLayer)) (l₂ := layer)
    (h₁ := stateLayer_isLayering (lv.state B RD hG layer hLayer)) (h₂ := hLayer) (stateLayer_spec (lv.state B RD hG layer hLayer))

theorem qRow_lvl (lv : Lvl B) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) :
    qRow (lv.state B RD hG layer hLayer).data (lv.state B RD hG layer hLayer).plain L γ δ F
      (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer)) base =
    qRow RD hG L γ δ F layer hLayer base := by
  have h := stateLayer_lvl B RD hG layer hLayer lv
  change qRow RD hG L γ δ F (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer)) base = _
  generalize stateLayer_isLayering (lv.state B RD hG layer hLayer) = hl
  revert hl
  rw [h]
  intro hl
  rfl

theorem tRow_lvl (lv : Lvl B) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) :
    tRow (lv.state B RD hG layer hLayer).data (lv.state B RD hG layer hLayer).plain L γ δ F
      (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer)) base =
    tRow RD hG L γ δ F layer hLayer base := by
  have h := stateLayer_lvl B RD hG layer hLayer lv
  change tRow RD hG L γ δ F (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer)) base = _
  generalize stateLayer_isLayering (lv.state B RD hG layer hLayer) = hl
  revert hl
  rw [h]
  intro hl
  rfl

theorem psiNat_lvl (lv : Lvl B) {U' : Finset (GBranch G.tree)} {a' b' : GBranch G.tree} (R' : CLRegionData G U' a' b')
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) :
    psiNat (lv.state B RD hG layer hLayer).data (lv.state B RD hG layer hLayer).plain R' L γ δ F
      (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer)) base =
    psiNat RD hG R' L γ δ F layer hLayer base := by
  have h := stateLayer_lvl B RD hG layer hLayer lv
  change psiNat RD hG R' L γ δ F (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer)) base = _
  generalize stateLayer_isLayering (lv.state B RD hG layer hLayer) = hl
  revert hl
  rw [h]
  intro hl
  rfl

end Lvl

end WaveTurbulence.VineEstS5C.P4.W2
