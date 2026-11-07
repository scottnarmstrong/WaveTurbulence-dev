/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.CoupleGate
public import WaveTurbulence.Foundations.Spine.PL234Draft.CohTransport
public import WaveTurbulence.Foundations.Spine.PL234Draft.TreeCoh
public import WaveTurbulence.Foundations.Spine.PL234Draft.SliceApp
public import WaveTurbulence.Foundations.Spine.PL234Draft.CoherentSlices
public import WaveTurbulence.Foundations.Spine.PL234Draft.SliceAlgebra
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.ZpSurjStmt
public import WaveTurbulence.Foundations.VineEst.VineEstS4c.Bs2Vanish
public import WaveTurbulence.Foundations.VineEst.VineEstS4c.SourceAppVanish

/-! # P1: the constant-extension lemma for the source approximants (TARGET L1893-L1925 (i))

For a coherent couple (resp. tree) at parent layers `(q, q')`, `q' ≤ q ≤ p`, with root layer `Lr`, the source approximant
`SourceApp.couple … q q'` on `[q, q+1]` is the constant extension (`extConst`) of the root-layer instance
`SourceApp.couple … Lr q'` on `[Lr, Lr+1]`, type by type (trivial, type 1, type 2).  No remainder, no hypothesis beyond
coherence.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P1
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.PL234 TTree WaveTurbulence.Reg WaveTurbulence.Links
  WaveTurbulence.VineEstS4c

theorem cplRootLayer_eq (LG : LayeredGarden 2) : cplRootLayer LG = layerAt LG ((0 : Fin 2), []) :=
  (layerAt_node LG (GNode.root LG.garden.tree 0)).symm

theorem treeRootLayer_eq (LG : LayeredGarden 1) : treeRootLayer LG = layerAt LG ((0 : Fin 1), []) :=
  (layerAt_node LG (GNode.root LG.garden.tree 0)).symm

/-- The root of a coherent type-2 couple lies in layer `q'` or on the positive chain (then `q' ≤` its layer). -/
theorem type2_root {p q q' : ℕ} {Xp Xm : RegChain} {Qlp : RegCpl} {LG : LayeredGarden 2} (hqq : q' ≤ q) (hqp : q ≤ p)
    (h : IsCoherentCoupleAt p q q' (.type2 Xp Xm Qlp) LG) :
    q' ≤ layerAt LG ((0 : Fin 2), []) ∧ (layerAt LG ((0 : Fin 2), []) ≠ q' → Xp ≠ RegChain.nil) := by
  have hQ := h.2.1
  have F := cohFacts_of_coherent hqq hqp h
  have hnode : ([] : Path) ∈ (LG.garden.tree 0).nodes := TTree.nil_mem_nodes _
  have ha := addrExt_mem_cplNodes hQ ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path))
    (⟨((0 : Fin 2), []), hnode⟩ : GNode LG.garden.tree)
  have hae : ((0 : Fin 2), ([] : Path)) ∈ cplNodes (RegCpl.type2 Xp Xm Qlp) ((0 : Fin 2), ([] : Path))
      ((1 : Fin 2), ([] : Path)) := by simpa [addrExt] using ha
  rcases mem_cplNodes_type2.mp hae with hx | hx | hx
  · refine ⟨F.low _ hx, fun _ hn => ?_⟩
    subst hn
    simp [chainNodesSet, pairEndpoints, RegChain.linksAt, RegChain.pairsAt] at hx
  · have := F.minus _ hx
    exact ⟨this.ge, fun hne => absurd this hne⟩
  · have := F.lp _ hx
    exact ⟨this.ge, fun hne => absurd this hne⟩

/-- Root layer bounds of a coherent couple: `q' ≤ Lr ≤ q`, and if `Lr ≠ q'` the couple has type 2 with nonempty `+` chain. -/
theorem cpl_root_bounds {p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2} (hqq : q' ≤ q) (hqp : q ≤ p)
    (h : IsCoherentCoupleAt p q q' Q LG) :
    q' ≤ cplRootLayer LG ∧ cplRootLayer LG ≤ q := by
  rw [cplRootLayer_eq]
  cases Q with
  | triv =>
    have := layers_type1 hqq h rfl (GNode.root LG.garden.tree 0)
    rw [← layerAt_node] at this
    exact ⟨this.ge, this.le.trans hqq⟩
  | type1 c Q₁ Q₂ Q₃ =>
    have := layers_type1 hqq h rfl (GNode.root LG.garden.tree 0)
    rw [← layerAt_node] at this
    exact ⟨this.ge, this.le.trans hqq⟩
  | type2 Xp Xm Qlp => exact ⟨(type2_root hqq hqp h).1, root_le_type2 hqq h⟩


theorem prod_split_Ioo {M : Type*} [CommMonoid M] (g : ℕ → M) {q' L q : ℕ} (hq' : q' < L) (hL : L < q)
    (h1 : ∀ r, L < r → g r = 1) :
    ∏ r ∈ Finset.Ioo q' q, g r = (∏ r ∈ Finset.Ioo q' L, g r) * g L := by
  have hsub : Finset.Ioc q' L ⊆ Finset.Ioo q' q := by
    intro r hr; simp only [Finset.mem_Ioc, Finset.mem_Ioo] at hr ⊢; omega
  rw [← Finset.prod_subset hsub (fun r hr hnot => h1 r (by
    simp only [Finset.mem_Ioc, Finset.mem_Ioo, not_and, not_le] at hr hnot; omega))]
  rw [← Finset.Ioo_insert_right hq', Finset.prod_insert (by simp), mul_comm]

theorem two_cast_aux {L q : ℕ} {t : ℝ} (hlt : L < q) (h1 : (q : ℝ) ≤ t) : (L : ℝ) + 1 ≤ t := by
  have : ((L + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hlt
  push_cast at this; linarith

/-- **The extension lemma for couples** (TARGET L1893-L1925 (i)): for `t ∈ [q, q+1]` the source approximant at the parent layers
`(q, q')` is the constant extension of the root-layer instance `(Lr, q')`. -/
theorem couple_eq_ext {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ) {p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2}
    (hqq : q' ≤ q) (hqp : q ≤ p) (hcoh : IsCoherentCoupleAt p q q' Q LG) (s : ℝ) (k : Mom d) {t : ℝ}
    (h1 : (q : ℝ) ≤ t) (h2 : t ≤ q + 1) :
    SourceApp.couple δ F LG Q q q' t s k =
      extConst (cplRootLayer LG : ℝ) (fun τ => SourceApp.couple δ F LG Q (cplRootLayer LG) q' τ s k) t := by
  obtain ⟨hlo, hhi⟩ := cpl_root_bounds hqq hqp hcoh
  rcases hhi.lt_or_eq with hlt | heq
  · rw [extConst_of_ge _ (two_cast_aux hlt h1)]
    have hq'q : q' < q := lt_of_le_of_lt hlo hlt
    have hne : q ≠ q' := Nat.ne_of_gt hq'q
    cases Q with
    | triv =>
      have hL : cplRootLayer LG = q' := layers_type1 hqq hcoh rfl _
      rw [hL]
      simp [SourceApp.couple, hne, hq'q]
    | type1 c Q₁ Q₂ Q₃ =>
      have hL : cplRootLayer LG = q' := layers_type1 hqq hcoh rfl _
      rw [hL]
      simp [SourceApp.couple, hne, hq'q]
    | type2 Xp Xm Qlp =>
      have F' := cohFacts_of_coherent hqq hqp hcoh
      obtain ⟨hlo2, hnil⟩ := type2_root hqq hqp hcoh
      have hnn : (Xp.isNil && Xm.isNil) = false := by
        have hwf := F'.wf
        simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hwf
        exact hwf.2
      have hsn : ∀ r, cplRootLayer LG < r → SourceApp.chainSlice LG ((0 : Fin 2), []) r Xp = .nil :=
        fun r hr => chainSlice_eq_nil LG _ Xp F'.sm (fun _ => by rw [← cplRootLayer_eq]; exact hr)
      have happ : ∀ r, cplRootLayer LG < r → ∀ (a b : ℝ),
          (SourceApp.chainSlice LG ((0 : Fin 2), []) r Xp).app δ r (F r) 1 a b k = 1 :=
        fun r hr a b => by rw [hsn r hr]; exact RegChain.app_nil' _ _ _ _ _ _ _
      by_cases hLq : cplRootLayer LG = q'
      · have hsn' : ∀ r, q' < r → SourceApp.chainSlice LG ((0 : Fin 2), []) r Xp = .nil := by
          rw [← hLq]; exact hsn
        have happ' : ∀ r, q' < r → ∀ (a b : ℝ),
            (SourceApp.chainSlice LG ((0 : Fin 2), []) r Xp).app δ r (F r) 1 a b k = 1 := by
          rw [← hLq]; exact happ
        have hTop : TopAll LG q' ((0 : Fin 2), []) Xp :=
          topAll_of_squeeze LG q' Xp 1 ((0 : Fin 2), []) F'.sm
            (fun _ => by rw [← cplRootLayer_eq, hLq]) F'.low
        have hfull : SourceApp.chainSlice LG ((0 : Fin 2), []) q' Xp = Xp := chainSlice_of_topAll LG q' Xp _ hTop
        rw [hLq]
        simp only [SourceApp.couple, hne, hq'q, ↓reduceIte]
        rw [Finset.prod_eq_one (fun r hr => happ' r (Finset.mem_Ioo.mp hr).1 _ _), happ' q hq'q, hfull]
        simp [SourceApp.closeCouple, hnn]
      · have hq'L : q' < cplRootLayer LG := lt_of_le_of_ne hlo (Ne.symm hLq)
        have hL0 : cplRootLayer LG ≠ q' := hLq
        simp only [SourceApp.couple, hne, hq'q, hL0, hq'L, ↓reduceIte]
        rw [prod_split_Ioo (fun r => (SourceApp.chainSlice LG ((0 : Fin 2), []) r Xp).app δ r (F r) 1 (r + 1) r k)
          hq'L hlt (fun r hr => happ r hr _ _), happ q hlt]
        ring
  · rw [heq]
    exact (extConst_of_mem (fun τ => SourceApp.couple δ F LG Q q q' τ s k) h1 h2).symm


/-- Root layer of a coherent tree: `q' ≤ Lr ≤ q`, and `Lr ≠ q'` forces a nonempty chain. -/
theorem tree_root_bounds {p q q' : ℕ} {X : RegChain} {LG : LayeredGarden 1} (hqq : q' ≤ q)
    (h : IsCoherentTreeAt p q q' X LG) :
    q' ≤ layerAt LG ((0 : Fin 1), []) ∧ layerAt LG ((0 : Fin 1), []) ≤ q ∧
      (layerAt LG ((0 : Fin 1), []) ≠ q' → X ≠ RegChain.nil) := by
  have F := treeCohFacts_of_coherent h
  cases X with
  | nil =>
    have hl := F.lone
    simp only [RegChain.lonePath] at hl
    have hl' : layerAt LG ((0 : Fin 1), []) = q' := by simpa [addrExt] using hl
    exact ⟨hl'.ge, hl'.le.trans hqq, fun hne => absurd hl' hne⟩
  | pair m Qr Qg inner rest =>
    have hr := Links.root_mem_chainNodesSet m Qr Qg inner rest (LG.garden.sig 0) ((0 : Fin 1), [])
    exact ⟨F.low _ hr, F.high _ hr, fun _ => by simp⟩

/-- **The extension lemma for trees** (TARGET L1893-L1925 (i)). -/
theorem tree_eq_ext {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ) {p q q' : ℕ} {X : RegChain} {LG : LayeredGarden 1}
    (hqq : q' ≤ q) (hcoh : IsCoherentTreeAt p q q' X LG) (s : ℝ) (k : Mom d) {t : ℝ}
    (h1 : (q : ℝ) ≤ t) (h2 : t ≤ q + 1) :
    SourceApp.tree δ F LG X q q' t s k =
      extConst (treeRootLayer LG : ℝ) (fun τ => SourceApp.tree δ F LG X (treeRootLayer LG) q' τ s k) t := by
  obtain ⟨hlo, hhi, hnil⟩ := tree_root_bounds hqq hcoh
  rw [treeRootLayer_eq]
  rcases hhi.lt_or_eq with hlt | heq
  · rw [extConst_of_ge _ (two_cast_aux hlt h1)]
    have hq'q : q' < q := lt_of_le_of_lt hlo hlt
    have hne : q ≠ q' := Nat.ne_of_gt hq'q
    have F' := treeCohFacts_of_coherent hcoh
    have hsn : ∀ r, layerAt LG ((0 : Fin 1), []) < r →
        SourceApp.chainSlice LG ((0 : Fin 1), []) r X = .nil :=
      fun r hr => chainSlice_eq_nil LG _ X F'.sm (fun _ => hr)
    have happ : ∀ r, layerAt LG ((0 : Fin 1), []) < r → ∀ (a b : ℝ),
        (SourceApp.chainSlice LG ((0 : Fin 1), []) r X).app δ r (F r) (LG.garden.sig 0) a b k = 1 :=
      fun r hr a b => by rw [hsn r hr]; exact RegChain.app_nil' _ _ _ _ _ _ _
    by_cases hLq : layerAt LG ((0 : Fin 1), []) = q'
    · have happ' : ∀ r, q' < r → ∀ (a b : ℝ),
          (SourceApp.chainSlice LG ((0 : Fin 1), []) r X).app δ r (F r) (LG.garden.sig 0) a b k = 1 := by
        rw [← hLq]; exact happ
      have hTop : TopAll LG q' ((0 : Fin 1), []) X :=
        topAll_of_squeeze LG q' X (LG.garden.sig 0) ((0 : Fin 1), []) F'.sm (fun _ => hLq.le) F'.low
      have hfull : SourceApp.chainSlice LG ((0 : Fin 1), []) q' X = X := chainSlice_of_topAll LG q' X _ hTop
      rw [hLq]
      simp only [SourceApp.tree, hne, ↓reduceIte]
      rw [Finset.prod_eq_one (fun r hr => happ' r (Finset.mem_Ioo.mp hr).1 _ _), happ' q hq'q, hfull]
      simp
    · have hq'L : q' < layerAt LG ((0 : Fin 1), []) := lt_of_le_of_ne hlo (Ne.symm hLq)
      have hL0 : layerAt LG ((0 : Fin 1), []) ≠ q' := hLq
      simp only [SourceApp.tree, hne, hL0, ↓reduceIte]
      rw [prod_split_Ioo (fun r => (SourceApp.chainSlice LG ((0 : Fin 1), []) r X).app δ r (F r) (LG.garden.sig 0)
        (r + 1) r k) hq'L hlt (fun r hr => happ r hr _ _), happ q hlt]
      ring
  · rw [heq]
    exact (extConst_of_mem (fun τ => SourceApp.tree δ F LG X q q' τ s k) h1 h2).symm


/-- **Endpoint vanishing of the root-layer instance above `q'`** (TARGET L1913 (ii), R35 repaired): if the root layer of a
coherent couple exceeds `q'`, the couple has type 2 with nonempty `+` chain and the root-layer instance vanishes at
`t = Lr` for every `s`. -/
theorem couple_root_vanish {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ) {p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2}
    (hqq : q' ≤ q) (hqp : q ≤ p) (hcoh : IsCoherentCoupleAt p q q' Q LG) (hgt : q' < cplRootLayer LG)
    (s : ℝ) (k : Mom d) :
    SourceApp.couple δ F LG Q (cplRootLayer LG) q' (cplRootLayer LG : ℝ) s k = 0 := by
  cases Q with
  | triv =>
    have := layers_type1 hqq hcoh rfl (GNode.root LG.garden.tree 0)
    exact absurd this (Nat.ne_of_gt hgt)
  | type1 c Q₁ Q₂ Q₃ =>
    have := layers_type1 hqq hcoh rfl (GNode.root LG.garden.tree 0)
    exact absurd this (Nat.ne_of_gt hgt)
  | type2 Xp Xm Qlp =>
    obtain ⟨-, hnil⟩ := type2_root hqq hqp hcoh
    have hne : layerAt LG ((0 : Fin 2), []) ≠ q' := by rw [← cplRootLayer_eq]; exact Nat.ne_of_gt hgt
    have hX := hnil hne
    cases Xp with
    | nil => exact absurd rfl hX
    | pair m Qr Qg inner rest =>
      refine VineEstS4c.SrcVanish.couple_type2_lt_zero δ F LG _ Xm Qlp (cplRootLayer LG) q' hgt ?_ s k
      rw [chainSlice_pair, ite_eq_left (by rw [← cplRootLayer_eq])]
      rfl

/-- The tree analogue: a coherent tree whose root layer exceeds `q'` has a nonempty chain, and the root-layer instance
vanishes at `t = Lr`. -/
theorem tree_root_vanish {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ) {p q q' : ℕ} {X : RegChain} {LG : LayeredGarden 1}
    (hqq : q' ≤ q) (hcoh : IsCoherentTreeAt p q q' X LG) (hgt : q' < treeRootLayer LG) (s : ℝ) (k : Mom d) :
    SourceApp.tree δ F LG X (treeRootLayer LG) q' (treeRootLayer LG : ℝ) s k = 0 := by
  obtain ⟨-, -, hnil⟩ := tree_root_bounds hqq hcoh
  have hne : layerAt LG ((0 : Fin 1), []) ≠ q' := by rw [← treeRootLayer_eq]; exact Nat.ne_of_gt hgt
  have hX := hnil hne
  cases X with
  | nil => exact absurd rfl hX
  | pair m Qr Qg inner rest =>
    refine VineEstS4c.SrcVanish.tree_lt_zero δ F LG _ (treeRootLayer LG) q' hgt ?_ s k
    rw [chainSlice_pair, ite_eq_left (by rw [← treeRootLayer_eq])]
    rfl

end WaveTurbulence.VineEstS5C.P1
