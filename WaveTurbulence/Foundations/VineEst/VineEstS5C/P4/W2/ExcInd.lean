/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcRec

/-! # P4-W2 (a): `rowFormNE_termsB` (the induction over the levels)

See `ExcRec` for the statement.  Generic in the bundle families `BE`, `BX` and in the explicit exceptional factors `XE`, `XB` with
`FrameShapeX`, `BotFrameShapeX` (for P4's `bundleFamOf` and BOT-DECOMP's `bundleBotFamOf`: module `ExcFam`).
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

theorem domX_idx {U U' : Finset (GBranch G.tree)} {a a' b b' : GBranch G.tree} (hU : U = U') (ha : a = a') (hb : b = b')
    (R : CLRegionData G U a b) (R' : CLRegionData G U' a' b') (lay : GBranch G.tree → ℕ) (Bex : Finset (GBranch G.tree))
    (t0 t1 t2 : ℝ) (u : GBranch G.tree → ℝ) : DomX R lay Bex t0 t1 t2 u ↔ DomX R' lay Bex t0 t1 t2 u := by
  subst hU ha hb
  rw [regionData_subsingleton R' R]

theorem domX_bot {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R R' : CLRegionData G U a b) (lay : GBranch G.tree → ℕ)
    (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) (hu : u a = t 0) :
    (DomF lay U a b u ∧ bTimeOK R' t u) ↔ DomX R lay {b} (t 0) (t 1) (t 2) u := by
  rw [regionData_subsingleton R' R]
  unfold DomF DomX bTimeOK clInteriorBranches
  rw [hu]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun v hv => ?_, h2, h3⟩
    obtain ⟨w1, w2, w3, w4⟩ := h1 v hv
    exact ⟨w1, w2, w3, fun hn => w4 (by simpa using hn)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun v hv => ?_, h2, h3⟩
    obtain ⟨w1, w2, w3, w4⟩ := h1 v hv
    exact ⟨w1, w2, w3, fun hn => w4 (by simpa using hn)⟩

theorem rowFormNE_congr' (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b) (base : Mom d)
    {ψ ψ' : PsiT G d} {Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop} {Pex : Finset (SourcePair G)}
    {Bex : Finset (GBranch G.tree)}
    {Xq Xq' : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ}
    (hψ : ∀ x t u, ψ x t u = ψ' x t u) (hX : ∀ p ∈ Pex, ∀ t u x, Xq p t u x = Xq' p t u x)
    (h : RowFormNE D hG L γ δ F layer hLayer R base ψ Dm Pex Bex Xq) :
    RowFormNE D hG L γ δ F layer hLayer R base ψ' Dm Pex Bex Xq' := by
  classical
  have h1 := rowForm_congr hG R L γ δ base ψ Dm h (Qw' := fun p t u x => if p ∈ Pex then Xq' p t u x else
      qRow D hG L γ δ F layer hLayer base (t 0) x u p) (Tw' := fun v t u x => if v ∈ Bex then 1 else
      tRow D hG L γ δ F layer hLayer base (t 0) x u v)
    (fun p _ t u x => by
      by_cases hp : p ∈ Pex
      · simp only [if_pos hp, hX p hp]
      · simp only [if_neg hp]) (fun v _ t u x => rfl)
  intro β' κ t u
  rw [← hψ]
  exact h1 β' κ t u

section Lvl
variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The layer of the core branches, at the start state. -/
noncomputable def layC : GBranch G.tree → ℕ := fun v => layer (RD.coreBranch hG v).toNode

theorem lay_lvl (lv : Lvl B) :
    (fun v : GBranch (lv.state B RD hG layer hLayer).skeleton.tree => stateLayer (lv.state B RD hG layer hLayer)
      ((lv.state B RD hG layer hLayer).data.coreBranch (lv.state B RD hG layer hLayer).plain v).toNode) =
      layC RD hG layer := by
  have h := stateLayer_lvl B RD hG layer hLayer lv
  funext v
  change stateLayer (lv.state B RD hG layer hLayer) (RD.coreBranch hG v).toNode = layer (RD.coreBranch hG v).toNode
  rw [h]

variable {κ0 : KPar d}

theorem rowFormNE_lvl (lv : Lvl B) {U' : Finset (GBranch G.tree)} {a' b' : GBranch G.tree} (R' : CLRegionData G U' a' b')
    (ψ : PsiT G d) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop) (Pex : Finset (SourcePair G)) (Bex : Finset (GBranch G.tree))
    (Xq : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (base : Mom d) :
    RowFormNE (lv.state B RD hG layer hLayer).data (lv.state B RD hG layer hLayer).plain L γ δ F
        (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer)) R' base ψ Dm Pex Bex Xq ↔
      RowFormNE RD hG L γ δ F layer hLayer R' base ψ Dm Pex Bex Xq := by
  unfold RowFormNE
  rw [qRow_lvl B RD hG layer hLayer lv L γ δ F base, tRow_lvl B RD hG layer hLayer lv L γ δ F base]
  exact Iff.rfl


variable {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
variable (BX : BotExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0)

/-- The frame shape with an explicit exceptional factor: at operative members every bundle summand is the frame times `XE`. -/
def FrameShapeX
    (XE : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), (BE lv pstar hk).Ch →
      (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ) : Prop :=
  ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar →
    ∀ (c : (BE lv pstar hk).Ch) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ),
      (BE lv pstar hk).term c x u =
        bundleFrame κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) x u * XE lv pstar hk c x u

/-- The bottom frame shape with an explicit exceptional factor. -/
def BotFrameShapeX
    (XB : ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      (BX lv pstar h0 hop hmax).Ch → (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ) : Prop :=
  ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (c : (BX lv pstar h0 hop hmax).Ch) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ),
    (BX lv pstar h0 hop hmax).term c x t u =
      botFrame κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u *
        bFac (botR (lv.state B RD hG layer hLayer) lv.c) κ0.L κ0.γ κ0.δ κ0.base x t u * XB lv pstar h0 hop hmax c x u

variable
  (XE : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), (BE lv pstar hk).Ch →
      (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
  (XB : ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      (BX lv pstar h0 hop hmax).Ch → (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)

/-- **A record comes from an operative member** of a level `lv'` whose realization nodes lie in those of `V`. -/
def ExcOf (V : Finset (GBranch G.tree)) (r : ExcRec G d) : Prop :=
  (∃ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (_ : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (c : (BE lv pstar hk).Ch) (f : (GNode G.tree → (Fin d → ℤ)) → (GNode G.tree → (Fin d → ℤ))),
      (∀ y ∈ clRealizationNodes G lv.c.U, y ∈ clRealizationNodes G V) ∧
      (∀ x, ∀ y ∈ clRealizationNodes G lv.c.U, f x y = x y) ∧
      r.p0 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
        ((lv.state B RD hG layer hLayer).family.placement pstar).retained ∧
      r.bj = (lv.split B RD hG layer hLayer pstar hk).sb.b ∧ r.blk = (lv.e pstar).1.val ∧
      ∀ x u, r.X x u = XE lv pstar hk c (rA (lv.split B RD hG layer hLayer pstar hk).RS (f x)) u) ∨
    (∃ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
      (c : (BX lv pstar h0 hop hmax).Ch) (f : (GNode G.tree → (Fin d → ℤ)) → (GNode G.tree → (Fin d → ℤ))),
      (∀ y ∈ clRealizationNodes G lv.c.U, y ∈ clRealizationNodes G V) ∧
      (∀ x, ∀ y ∈ clRealizationNodes G lv.c.U, f x y = x y) ∧
      r.p0 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
        ((lv.state B RD hG layer hLayer).family.placement pstar).retained ∧
      r.bj = lv.c.b ∧ r.blk = 0 ∧ ∀ x u, r.X x u = XB lv pstar h0 hop hmax c (f x) u)

/-- The statement proved by the induction over the levels. -/
def QNE (lv : Lvl B) (ψ : PsiT G d) : Prop :=
  ∃ (recs : List (ExcRec G d)) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop),
    (∀ r ∈ recs, ExcOf B RD hG layer hLayer BE BX XE XB lv.c.U r ∧ r.p0 ∈ clRegionalPairs hG lv.c.U ∧
      r.bj ∈ lv.c.U.erase lv.c.a) ∧
    (recs.map ExcRec.p0).Nodup ∧ (recs.map ExcRec.bj).Nodup ∧
    (∀ t u, u lv.c.a = t 0 → (Dm t u ↔ DomX lv.region (layC RD hG layer) (bexOf recs) (t 0) (t 1) (t 2) u)) ∧
    RowFormNE RD hG κ0.L κ0.γ κ0.δ κ0.F layer hLayer lv.region κ0.base ψ Dm (pexOf recs) (bexOf recs) (xqOf recs)


theorem qne_base (lv : Lvl B) :
    QNE B RD hG layer hLayer BE BX XE XB lv (lv.psiBase B RD hG layer hLayer κ0) := by
  classical
  refine ⟨[], ClDom lv.region (layC RD hG layer), by simp, by simp, by simp, ?_, ?_⟩
  · intro t u _
    rw [bexOf_nil]
    exact (domX_empty lv.region (layC RD hG layer) t u).symm
  · rw [pexOf_nil, bexOf_nil]
    have h := rowForm_psiNat (lv.state B RD hG layer hLayer).data (lv.state B RD hG layer hLayer).plain lv.region
      κ0.L κ0.γ κ0.δ κ0.F (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering (lv.state B RD hG layer hLayer))
      κ0.base
    have hl := lay_lvl B RD hG layer hLayer lv
    rw [hl] at h
    refine (rowFormNE_lvl B RD hG layer hLayer lv lv.region _ _ _ _ _ κ0.L κ0.γ κ0.δ κ0.F κ0.base).mp ?_
    unfold RowFormNE
    exact rowForm_congr hG lv.region κ0.L κ0.γ κ0.δ κ0.base _ _ h (fun p _ t u x => (if_neg (Finset.notMem_empty p)).symm) (fun v _ t u x => (if_neg (Finset.notMem_empty v)).symm)


theorem qne_bot (hXB : BotFrameShapeX B RD hG layer hLayer BX XB) (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (c : (BX lv pstar h0 hop hmax).Ch) :
    QNE B RD hG layer hLayer BE BX XE XB lv (fun x t u => (BX lv pstar h0 hop hmax).term c x t u) := by
  classical
  set A := lv.state B RD hG layer hLayer with hA
  have hSlow := chain_slow lv.c pstar (Lvl.bottom_hb0 B RD hG layer hLayer lv pstar h0)
  set p0 := pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained with hp0
  have hp0U : p0 ∈ clRegionalPairs hG lv.c.U := hSlow.p0_mem
  have hbU : lv.c.b ∈ lv.c.U.erase lv.c.a := hSlow.b_mem_erase
  let rec0 : ExcRec G d := ⟨p0, lv.c.b, 0, fun x u => XB lv pstar h0 hop hmax c x u⟩
  have hNE := rowFormNE_bot A.data A.plain κ0.L κ0.γ κ0.δ κ0.F (stateLayer A) (stateLayer_isLayering A) κ0.base lv.c.block
    (botR A lv.c) p0 hSlow.p0_mem hSlow.b_mem_erase (fun x u => XB lv pstar h0 hop hmax c x u)
  refine ⟨[rec0], fun t u => DomF (fun v => stateLayer A (A.data.coreBranch A.plain v).toNode) lv.c.U lv.c.a lv.c.b u ∧
    bTimeOK (botR A lv.c) t u, ?_, by simp, by simp, ?_, ?_⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨Or.inr ⟨lv, pstar, h0, hop, hmax, c, id, fun y hy => hy, fun x y _ => rfl, rfl, rfl, rfl, fun x u => rfl⟩, hp0U, hbU⟩
  · intro t u hu
    have hb : bexOf [rec0] = {lv.c.b} := by
      rw [bexOf_cons, bexOf_nil]
      exact Finset.insert_empty
    rw [hb, ← lay_lvl B RD hG layer hLayer lv]
    exact domX_bot lv.region (botR A lv.c) _ t u hu
  · have hb : bexOf [rec0] = {lv.c.b} := by
      unfold bexOf
      simp [rec0]
    have hp : pexOf [rec0] = {p0} := by
      rw [pexOf_cons, pexOf_nil]
      exact Finset.insert_empty
    rw [hb, hp]
    have h1 := (rowFormNE_lvl B RD hG layer hLayer lv (botR A lv.c) _ _ _ _ _ κ0.L κ0.γ κ0.δ κ0.F κ0.base).mp hNE
    have h2 := rowFormNE_idx RD hG κ0.L κ0.γ κ0.δ κ0.F layer hLayer rfl rfl rfl (botR A lv.c) lv.region κ0.base _ _ _ _ _ h1
    refine rowFormNE_congr' RD hG κ0.L κ0.γ κ0.δ κ0.F layer hLayer lv.region κ0.base ?_ ?_ h2
    · intro x t u
      rw [hXB lv pstar h0 hop hmax c x t u]
      rfl
    · intro p hp' t u x
      have : p = p0 := Finset.mem_singleton.mp hp'
      subst this
      exact (xqOf_cons_self rec0 [] (by simp) t u x).symm


theorem qne_step (hL : κ0.L ≠ 0) (hXE : FrameShapeX B RD hG layer hLayer BE XE) (lv : Lvl B) (pstar : lv.ι)
    (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar) (c : (BE lv pstar hk).Ch) (Ψ' : PsiT G d)
    (hΨ : QNE B RD hG layer hLayer BE BX XE XB (lv.next B RD hG layer hLayer pstar hk) Ψ') :
    QNE B RD hG layer hLayer BE BX XE XB lv
      (fun x t u => (BE lv pstar hk).term c (rA (lv.split B RD hG layer hLayer pstar hk).RS x) u *
        Ψ' (rB (lv.split B RD hG layer hLayer pstar hk).RT x) ![u (lv.split B RD hG layer hLayer pstar hk).sb.b, t 1, t 2] u) := by
  classical
  obtain ⟨recs', Dm', hrecs', hnd1, hnd2, hDm', hrf'⟩ := hΨ
  set A := lv.state B RD hG layer hLayer with hA
  set sp := lv.split B RD hG layer hLayer pstar hk with hsp
  set p0 := pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained with hp0
  have hSl := SplitAt.slow sp
  have hp0S : p0 ∈ clRegionalPairs hG sp.sb.U := hSl.p0_mem
  have hbS : sp.sb.b ∈ sp.sb.U.erase sp.sb.a := hSl.b_mem_erase
  have hdisP := split_pairs_disjoint sp.sb.block sp.hT sp.hi sp.hU hG
  have hdisI := split_interior_disjoint sp.sb.block sp.hT sp.hi sp.hU
  have hjoint : sp.tb.a = sp.sb.b := sp.joint.symm
  have hUeq : lv.c.U = sp.sb.U ∪ sp.tb.U := sp.union
  have hsa : sp.sb.a = lv.c.a := sp.sa
  -- facts about the records of the next level
  have hpT : ∀ r ∈ recs', r.p0 ∈ clRegionalPairs hG sp.tb.U := fun r hr => (hrecs' r hr).2.1
  have hbT : ∀ r ∈ recs', r.bj ∈ sp.tb.U.erase sp.sb.b := fun r hr => by
    have := (hrecs' r hr).2.2
    rw [← hjoint]
    exact this
  let new : ExcRec G d := ⟨p0, sp.sb.b, (lv.e pstar).1.val, fun x u => XE lv pstar hk c (rA sp.RS x) u⟩
  let g : (GNode G.tree → (Fin d → ℤ)) → (GNode G.tree → (Fin d → ℤ)) := rB sp.RT
  have hpU : ∀ q ∈ clRegionalPairs hG sp.tb.U, q ∈ clRegionalPairs hG lv.c.U := fun q hq => by
    rw [hUeq]
    exact (Finset.ext_iff.mp (split_pairs sp.sb.block sp.hT sp.hi sp.hU hG) q).mpr (Finset.mem_union_right _ hq)
  have hbU : ∀ v ∈ sp.tb.U.erase sp.sb.b, v ∈ lv.c.U.erase lv.c.a := fun v hv => by
    rw [hUeq, ← hsa]
    exact mem_interior_of_T sp.sb.block sp.hT sp.hi sp.hU hv
  have hrealU : ∀ y ∈ clRealizationNodes G sp.tb.U, y ∈ clRealizationNodes G lv.c.U := fun y hy => by
    rw [hUeq]
    exact (split_realization sp.sb.block sp.hT sp.hi sp.hU y).mpr (Or.inr hy)
  -- the records
  have hrecs : ∀ r ∈ new :: recs'.map (fun r => r.comp g), ExcOf B RD hG layer hLayer BE BX XE XB lv.c.U r ∧
      r.p0 ∈ clRegionalPairs hG lv.c.U ∧ r.bj ∈ lv.c.U.erase lv.c.a := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨Or.inl ⟨lv, pstar, hk, hop, c, id, fun y hy => hy, fun x y _ => rfl, rfl, rfl, rfl, fun x u => rfl⟩, ?_, ?_⟩
      · rw [hUeq]
        exact (Finset.ext_iff.mp (split_pairs sp.sb.block sp.hT sp.hi sp.hU hG) _).mpr (Finset.mem_union_left _ hp0S)
      · rw [hUeq, ← hsa]
        exact mem_interior_of_S sp.sb.block sp.hT sp.hi sp.hU hbS
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      obtain ⟨hex, hp, hb⟩ := hrecs' r' hr'
      refine ⟨?_, hpU _ (hpT r' hr'), hbU _ (hbT r' hr')⟩
      rcases hex with ⟨lv'', ps'', hk'', hop'', c'', f'', hsub, hagr, hp0e, hbje, hblk, hX⟩ |
          ⟨lv'', ps'', h0'', hop'', hmax'', c'', f'', hsub, hagr, hp0e, hbje, hblk, hX⟩
      · refine Or.inl ⟨lv'', ps'', hk'', hop'', c'', fun x => f'' (g x), fun y hy => hrealU y (hsub y hy),
          fun x y hy => ?_, hp0e, hbje, hblk, fun x u => hX (g x) u⟩
        show f'' (g x) y = x y
        rw [hagr (g x) y hy]
        exact rB_real sp.RT x y (hsub y hy)
      · refine Or.inr ⟨lv'', ps'', h0'', hop'', hmax'', c'', fun x => f'' (g x), fun y hy => hrealU y (hsub y hy),
          fun x y hy => ?_, hp0e, hbje, hblk, fun x u => hX (g x) u⟩
        show f'' (g x) y = x y
        rw [hagr (g x) y hy]
        exact rB_real sp.RT x y (hsub y hy)
  have hmapP : (new :: recs'.map (fun r => r.comp g)).map ExcRec.p0 = p0 :: recs'.map ExcRec.p0 := by
    simp [new, ExcRec.comp, List.map_map, Function.comp_def]
    rfl
  have hmapB : (new :: recs'.map (fun r => r.comp g)).map ExcRec.bj = sp.sb.b :: recs'.map ExcRec.bj := by
    simp [new, ExcRec.comp, List.map_map, Function.comp_def]
    rfl
  have hPex' : pexOf recs' ⊆ clRegionalPairs hG sp.tb.U := fun q hq => by
    obtain ⟨r, hr, rfl⟩ := mem_pexOf.mp hq
    exact hpT r hr
  have hBex' : bexOf recs' ⊆ sp.tb.U.erase sp.sb.b := fun v hv => by
    obtain ⟨r, hr, rfl⟩ := mem_bexOf.mp hv
    exact hbT r hr
  have hneP : ∀ r' ∈ recs'.map (fun r => r.comp g), r'.p0 ≠ p0 := fun r' hr' h => by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
    exact Finset.disjoint_left.mp hdisP hp0S (h ▸ hpT r hr)
  refine ⟨new :: recs'.map (fun r => r.comp g), fun t u =>
    DomF (fun v => stateLayer A (A.data.coreBranch A.plain v).toNode) sp.sb.U sp.sb.a sp.sb.b u ∧
      Dm' ![u sp.sb.b, t 1, t 2] u, hrecs, ?_, ?_, ?_, ?_⟩
  · rw [hmapP]
    refine List.nodup_cons.mpr ⟨fun h => ?_, hnd1⟩
    obtain ⟨r', hr', e⟩ := List.mem_map.mp h
    exact Finset.disjoint_left.mp hdisP hp0S (e ▸ hpT r' hr')
  · rw [hmapB]
    refine List.nodup_cons.mpr ⟨fun h => ?_, hnd2⟩
    obtain ⟨r', hr', e⟩ := List.mem_map.mp h
    exact (Finset.mem_erase.mp (hbT r' hr')).1 e
  · intro t u hu
    have hu' : u sp.sb.a = t 0 := by rw [hsa]; exact hu
    have hn : u (lv.next B RD hG layer hLayer pstar hk).c.a = (![u sp.sb.b, t 1, t 2] : Fin 3 → ℝ) 0 := by
      show u sp.tb.a = u sp.sb.b
      rw [hjoint]
    have hIH := hDm' ![u sp.sb.b, t 1, t 2] u hn
    have hglue := domX_glue sp.sb.block sp.hT sp.hi sp.hU sp.RU sp.RT (layC RD hG layer) (bexOf recs') hBex' (t 0) (t 1) (t 2) u hu'
    rw [bexOf_cons, bexOf_map_comp]
    beta_reduce
    rw [lay_lvl B RD hG layer hLayer lv, hIH]
    have e1 := domX_idx (rfl : (lv.next B RD hG layer hLayer pstar hk).c.U = sp.tb.U) hjoint (rfl : (lv.next B RD hG layer hLayer pstar hk).c.b = sp.tb.b)
      (lv.next B RD hG layer hLayer pstar hk).region sp.RT (layC RD hG layer) (bexOf recs') (u sp.sb.b) (t 1) (t 2) u
    have e2 := domX_idx hUeq.symm hsa sp.tbb sp.RU lv.region (layC RD hG layer) (insert sp.sb.b (bexOf recs')) (t 0) (t 1) (t 2) u
    exact (and_congr Iff.rfl e1).trans (hglue.trans e2)
  · have hNE0 := rowFormNE_idx RD hG κ0.L κ0.γ κ0.δ κ0.F layer hLayer rfl hjoint rfl (lv.next B RD hG layer hLayer pstar hk).region
      sp.RT κ0.base _ _ _ _ _ hrf'
    have hNE := (rowFormNE_lvl B RD hG layer hLayer lv sp.RT _ _ _ _ _ κ0.L κ0.γ κ0.δ κ0.F κ0.base).mpr hNE0
    have hstep := rowFormNE_step sp.sb.block sp.hT sp.hi sp.hU A.data A.plain κ0.L κ0.γ κ0.δ hL κ0.F (stateLayer A)
      (stateLayer_isLayering A) κ0.base sp.RU sp.RS sp.RT p0 hp0S hbS (XE lv pstar hk c) Ψ' hPex' hBex' hNE
    have h1 := (rowFormNE_lvl B RD hG layer hLayer lv sp.RU _ _ _ _ _ κ0.L κ0.γ κ0.δ κ0.F κ0.base).mp hstep
    have h2 := rowFormNE_idx RD hG κ0.L κ0.γ κ0.δ κ0.F layer hLayer hUeq.symm hsa sp.tbb sp.RU lv.region κ0.base _ _ _ _ _ h1
    rw [pexOf_cons, pexOf_map_comp, bexOf_cons, bexOf_map_comp]
    refine rowFormNE_congr' RD hG κ0.L κ0.γ κ0.δ κ0.F layer hLayer lv.region κ0.base ?_ ?_ h2
    · intro x t u
      rw [hXE lv pstar hk hop c (rA sp.RS x) u]
      rfl
    · intro q hq t u x
      by_cases hqp : q = p0
      · subst hqp
        rw [if_pos rfl]
        exact (xqOf_cons_self new (recs'.map (fun r => r.comp g)) hneP t u x).symm
      · have := xqOf_cons_ne new (recs'.map (fun r => r.comp g)) (p := q) hqp t u x
        rw [this, xqOf_comp]
        exact if_neg hqp


/-- **`rowFormNE_termsB`**: every term of `Lvl.termsB` has a native-except row form with exceptional records. -/
theorem rowFormNE_termsB (hL : κ0.L ≠ 0) (hXE : FrameShapeX B RD hG layer hLayer BE XE)
    (hXB : BotFrameShapeX B RD hG layer hLayer BX XB) :
    ∀ (m : ℕ) (lv : Lvl B), ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX m lv,
      QNE B RD hG layer hLayer BE BX XE XB lv ψ := by
  refine Lvl.termsB_induction B RD hG layer hLayer BE BX (QNE B RD hG layer hLayer BE BX XE XB)
    (qne_base B RD hG layer hLayer BE BX XE XB) ?_ ?_
  · intro lv pstar h0 hop hmax c
    exact qne_bot B RD hG layer hLayer BE BX XE XB hXB lv pstar h0 hop hmax c
  · intro lv pstar hk hop _ c Ψ' hΨ
    exact qne_step B RD hG layer hLayer BE BX XE XB hL hXE lv pstar hk hop c Ψ' hΨ

end Lvl

end WaveTurbulence.VineEstS5C.P4.W2
