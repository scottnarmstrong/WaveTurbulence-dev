/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.SFF

/-! # P4-W1: `SepFamFam` from the gates, and `SepFamFam.Bounded` (the W1 export)

`sffOf E hord`: at every level `lv` and operative member `pstar` (`h : lv.Op pstar`), the separated expansions `sepFamOf` of the
state of the level, with the operation preconditions taken from the `FamilyOperation` fields of `h.some` (`canonical`, `eligible`,
`treeCoherent`, `coupleCoherent`, exactly as `P4.Family` does for `ZpSurj`/`ZpLayers`), and the order bound `zpN ≤ N_{p+1}^4` from
the garden-order premise of the statement (`zpN_start_le`: `2 zpN ≤ RD.size ≤ order`).

`sffOf_bounded`: `SepFamFam.Bounded` (every expansion has at most `2^{zpN}` terms; P4 `card_terms_le_wt` consumes it).
`sffOf_sQ`, `sffOf_sT`: the terms are those of the certified expansions `certC`, `certT` (definitional), so the per-term
certificates (W2) read the `SepT` data `(certC …).lo i`, `(certC …).hi i` (windows `timeBox L₄ L₂`, `timeBox Lₕ L₂`; trees `timeBoxGt`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W13
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {P : WTParams} {κ0 : KPar P.d} {Bh : ℕ → ℝ} {hprime : IsPrimeGarden G}

/-- The exceptional pair of a core vine of the start state is part of the reconstruction: `zpN ≤ RD.size/2 ≤ order`. -/
theorem zpN_start_le (i : (assemblySourceFamily B).CoreIndex) :
    2 * zpN (startState B RD hG layer hLayer) i ≤ (RD.garden hG).order := by
  classical
  have h2 := WaveTurbulence.ZpSurj.two_zpN (startState B RD hG layer hLayer) (pstar := i)
  have hd := RD.decoded_order hG (RD.garden_decodes hG)
  have ht : (RD.tree ((startState B RD hG layer hLayer).family.placement i).lower).size ≤ ∑ c, (RD.tree c).size :=
    Finset.single_le_sum (f := fun c => (RD.tree c).size) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hc : (RD.couple (pairOfLeaf G hG ((startState B RD hG layer hLayer).family.placement i).retained)).size ≤
      ∑ q, (RD.couple q).size :=
    Finset.single_le_sum (f := fun q => (RD.couple q).size) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hs : RD.size = (∑ c, (RD.tree c).size) + ∑ q, (RD.couple q).size := rfl
  change 2 * zpN (startState B RD hG layer hLayer) i = (RD.tree ((startState B RD hG layer hLayer).family.placement i).lower).size +
    (RD.couple (pairOfLeaf G hG ((startState B RD hG layer hLayer).family.placement i).retained)).size at h2
  omega

theorem zpN_lvl_le (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (lv : Lvl B) (pstar : lv.ι) :
    zpN (lv.state B RD hG layer hLayer) pstar ≤ P.N (p + 1) ^ 4 := by
  rw [zpN_lvl]
  have := zpN_start_le B RD hG layer hLayer (lv.e pstar)
  omega

/-- **`SepFamFam` from the gates** (W1). -/
noncomputable def sffOf (E : GateEnv P κ0 p Bh) (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) :
    SepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime :=
  fun lv pstar hk h => sepFamOf (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
    h.some.canonical h.some.eligible h.some.treeCoherent h.some.coupleCoherent E
    (zpN_lvl_le B RD hG layer hLayer hord lv pstar)

/-- **`SepFamFam.Bounded` of `sffOf`.** -/
theorem sffOf_bounded (E : GateEnv P κ0 p Bh) (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) :
    SepFamFam.Bounded (kind := kind) B RD hG layer hLayer (sffOf (hprime := hprime) (kind := kind) B RD hG layer hLayer E hord) :=
  fun lv pstar hk h b =>
    ⟨certC_m_le (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
        h.some.canonical h.some.eligible h.some.treeCoherent h.some.coupleCoherent E
        (zpN_lvl_le B RD hG layer hLayer hord lv pstar) b,
      certT_m_le (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
        h.some.canonical h.some.eligible h.some.treeCoherent h.some.coupleCoherent E
        (zpN_lvl_le B RD hG layer hLayer hord lv pstar) b⟩

/-- The couple terms of `sffOf` are those of `certC`. -/
theorem sffOf_sQ (E : GateEnv P κ0 p Bh) (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (lv : Lvl B) (pstar : lv.ι)
    (hk : 1 ≤ (lv.e pstar).1.val) (h : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar) (b) :
    (sffOf (hprime := hprime) B RD hG layer hLayer E hord lv pstar hk h).S.sQ b =
      (certC (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
        h.some.canonical h.some.eligible h.some.treeCoherent h.some.coupleCoherent E
        (zpN_lvl_le B RD hG layer hLayer hord lv pstar) b).term := rfl

/-- The tree terms of `sffOf` are those of `certT`. -/
theorem sffOf_sT (E : GateEnv P κ0 p Bh) (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (lv : Lvl B) (pstar : lv.ι)
    (hk : 1 ≤ (lv.e pstar).1.val) (h : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar) (b) :
    (sffOf (hprime := hprime) B RD hG layer hLayer E hord lv pstar hk h).S.sT b =
      (certT (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
        h.some.canonical h.some.eligible h.some.treeCoherent h.some.coupleCoherent E
        (zpN_lvl_le B RD hG layer hLayer hord lv pstar) b).term := rfl

end WaveTurbulence.VineEstS5C.P4.W13
