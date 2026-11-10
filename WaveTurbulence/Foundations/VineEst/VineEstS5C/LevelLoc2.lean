/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelLoc
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelBase
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelRecurse

/-! # Clock locality of the level summands (V5 Step 4d part C, WP-I)

`ClDom_congr`, `psiNat_congr`: the native summand of a CL region reads the clock only on its region; `Lvl.psiBase_congr`,
**`Lvl.psiFuel_congr`**: `psiFuel` reads the clock only on the chain region of the level (hypothesis `hlocPsi` of `Lvl.classSum_flat`);
`Lvl.op_start`: an operation at a member of a level is an operation at the start state.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem ClDom_congr (hS : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (lay : GBranch G.tree → ℕ)
    (t : Fin 3 → ℝ) {u u' : GBranch G.tree → ℝ} (h : ∀ v ∈ U, u v = u' v) :
    ClDom R lay t u ↔ ClDom R lay t u' := by
  have hb : u b = u' b := h b hS.2.2.1
  have key : ∀ v ∈ U.erase a, parentClock (t 0) u v.toNode = parentClock (t 0) u' v.toNode := by
    intro v hv
    obtain ⟨hva, hvS⟩ := Finset.mem_erase.mp hv
    exact parentClock_congr_S hS R h ((branch_mem_clRealizationNodes v).mpr hvS)
      (fun e => hva (Mole.branch_toNode_injective e))
  unfold ClDom
  have hint : (∀ v ∈ clInteriorBranches R, (lay v : ℝ) < u v ∧ u v < lay v + 1 ∧ 0 < u v ∧
        u v < parentClock (t 0) u v.toNode) ↔
      (∀ v ∈ clInteriorBranches R, (lay v : ℝ) < u' v ∧ u' v < lay v + 1 ∧ 0 < u' v ∧
        u' v < parentClock (t 0) u' v.toNode) := by
    refine forall₂_congr fun v hv => ?_
    have hv' : v ∈ U.erase a := hv
    have e := h v (Finset.mem_of_mem_erase hv')
    rw [e, key v hv']
  rw [hint, hb]

theorem psiNat_congr (hS : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (D : ReconstructionData G)
    (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    {u u' : GBranch G.tree → ℝ} (h : ∀ v ∈ U, u v = u' v) :
    psiNat D hG R L γ δ F layer hLayer base x t u = psiNat D hG R L γ δ F layer hLayer base x t u' := by
  classical
  unfold psiNat
  have h1 := ClDom_congr hS R (fun v => layer (D.coreBranch hG v).toNode) t h
  rw [clRegionalPhase_congr U L γ δ (k := cosetDecoration G L base x) (u := u) (u' := u')
      (fun _ _ => rfl) (fun _ _ _ => rfl) h,
    starProd_congr_S D hG L γ δ F layer hLayer base hS R x h]
  by_cases hd : ClDom R (fun v => layer (D.coreBranch hG v).toNode) t u
  · simp [hd, h1.mp hd]
  · have hd' : ¬ ClDom R (fun v => layer (D.coreBranch hG v).toNode) t u' := fun h' => hd (h1.mpr h')
    simp [hd, hd']


section Fuel
variable {U : Finset (GBranch G.tree)} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem Lvl.psiBase_congr (κ0 : KPar d) (lv : Lvl B) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    {u u' : GBranch G.tree → ℝ} (h : ∀ v ∈ lv.c.U, u v = u' v) :
    lv.psiBase B RD hG layer hLayer κ0 x t u = lv.psiBase B RD hG layer hLayer κ0 x t u' :=
  psiNat_congr lv.c.block lv.region _ _ _ _ _ _ _ _ _ x t h

open Classical in
/-- **Clock locality of the summand of a level**: `psiFuel` reads the clock only on the chain region. -/
theorem Lvl.psiFuel_congr (κ0 : KPar d) (hprime : IsPrimeGarden G) :
    ∀ (m : ℕ) (lv : Lvl B) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) {u u' : GBranch G.tree → ℝ},
      (∀ v ∈ lv.c.U, u v = u' v) →
      Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u =
        Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u' := by
  intro m
  induction m with
  | zero => intro lv x t u u' h; exact Lvl.psiBase_congr B RD hG layer hLayer κ0 lv x t h
  | succ m ih =>
    intro lv x t u u' h
    by_cases hop : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j
    · set pstar := Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop) with hpstar
      by_cases hk : 1 ≤ (lv.e pstar).1.val
      · have hstep : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv =
            Lvl.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
              (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk)) := by
          rw [Lvl.psiFuel, dif_pos hop]
          exact dif_pos hk
        rw [hstep]
        set sp := lv.split B RD hG layer hLayer pstar hk with hsp
        have hsub1 : ∀ v ∈ sp.sb.U, u v = u' v := fun v hv =>
          h v (by rw [show lv.c.U = sp.sb.U ∪ sp.tb.U from sp.union]; exact Finset.mem_union_left _ hv)
        have hsub2 : ∀ v ∈ (lv.next B RD hG layer hLayer pstar hk).c.U, u v = u' v := fun v hv =>
          h v (by rw [show lv.c.U = sp.sb.U ∪ sp.tb.U from sp.union]; exact Finset.mem_union_right _ hv)
        have hb : u sp.sb.b = u' sp.sb.b := hsub1 _ sp.sb.block.2.2.1
        unfold Lvl.psiStep psiStepSp
        beta_reduce
        congr 1
        · exact psiSB_congr (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) sp hprime _ hsub1
        · have e2 := ih (lv.next B RD hG layer hLayer pstar hk) (rB sp.RT x) ![u sp.sb.b, t 1, t 2] hsub2
          have e3 : (![u sp.sb.b, t 1, t 2] : Fin 3 → ℝ) = ![u' sp.sb.b, t 1, t 2] := by rw [hb]
          exact e2.trans (congrArg (fun tt => Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m
            (lv.next B RD hG layer hLayer pstar hk) (rB sp.RT x) tt u') e3)
      · have hstep : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv =
            WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar := by
          rw [Lvl.psiFuel, dif_pos hop]
          exact dif_neg hk
        rw [hstep]
        exact WaveTurbulence.VineEstS5B2.psiBot_congr κ0 (lv.state B RD hG layer hLayer) lv.c
          (Lvl.bottom_hb0 B RD hG layer hLayer lv pstar (by omega)) x t h
    · have hstep : Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv = lv.psiBase B RD hG layer hLayer κ0 := by
        simp only [Lvl.psiFuel, hop, dite_false]
      rw [hstep]
      exact Lvl.psiBase_congr B RD hG layer hLayer κ0 lv x t h

end Fuel

section Bottom
variable {U : Finset (GBranch G.tree)} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

end Bottom

end WaveTurbulence.VineEstS5C
