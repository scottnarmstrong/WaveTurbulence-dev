/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.HFree

/-! # W2-HFREE (3): `qne_bot`/`qne_step` with the record provenance

`qneR_bot`, `qneR_step` are the proofs of `qne_bot`, `qne_step` (ExcInd.lean, sha256 in COPIED-SHA256SUMS) with the extra conclusion on the
record list: the new record has `p0` = the pair of the retained leaf of the processed member, and every record of the next level is
kept (up to `ExcRec.comp`, which does not change `p0`).  The step takes the witness `recs'`, `Dm'` of the next level explicitly.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
variable (BX : BotExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0)
variable
  (XE : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), (BE lv pstar hk).Ch →
      (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
  (XB : ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      (BX lv pstar h0 hop hmax).Ch → (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)


theorem qneR_bot (hXB : BotFrameShapeX B RD hG layer hLayer BX XB) (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (c : (BX lv pstar h0 hop hmax).Ch) :
    ∃ (recs : List (ExcRec G d)) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop),
      QNEBody B RD hG layer hLayer BE BX XE XB lv (fun x t u => (BX lv pstar h0 hop hmax).term c x t u) recs Dm ∧
      ∃ r ∈ recs, r.p0 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
      ((lv.state B RD hG layer hLayer).family.placement pstar).retained := by
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
    bTimeOK (botR A lv.c) t u, ?_, ⟨rec0, List.mem_singleton_self _, rfl⟩⟩
  unfold QNEBody
  refine ⟨?_, by simp, by simp, ?_, ?_⟩
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



theorem qneR_step (hL : κ0.L ≠ 0) (hXE : FrameShapeX B RD hG layer hLayer BE XE) (lv : Lvl B) (pstar : lv.ι)
    (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar) (c : (BE lv pstar hk).Ch) (Ψ' : PsiT G d)
    (recs' : List (ExcRec G d)) (Dm' : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop)
    (hΨ : QNEBody B RD hG layer hLayer BE BX XE XB (lv.next B RD hG layer hLayer pstar hk) Ψ' recs' Dm') :
    ∃ (recs : List (ExcRec G d)) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop),
      QNEBody B RD hG layer hLayer BE BX XE XB lv
        (fun x t u => (BE lv pstar hk).term c (rA (lv.split B RD hG layer hLayer pstar hk).RS x) u *
          Ψ' (rB (lv.split B RD hG layer hLayer pstar hk).RT x) ![u (lv.split B RD hG layer hLayer pstar hk).sb.b, t 1, t 2] u) recs Dm ∧
      (∃ r ∈ recs, r.p0 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
      ((lv.state B RD hG layer hLayer).family.placement pstar).retained) ∧ ∀ r' ∈ recs', ∃ r ∈ recs, r.p0 = r'.p0 := by
  classical
  obtain ⟨hrecs', hnd1, hnd2, hDm', hrf'⟩ := hΨ
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
      Dm' ![u sp.sb.b, t 1, t 2] u, ?_, ⟨new, List.mem_cons_self, rfl⟩, fun r' hr' =>
        ⟨r'.comp g, List.mem_cons_of_mem _ (List.mem_map_of_mem hr'), rfl⟩⟩
  unfold QNEBody
  refine ⟨hrecs, ?_, ?_, ?_, ?_⟩
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



end WaveTurbulence.VineEstS5C.P4.W2
