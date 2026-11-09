/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.SFF
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.SFFam
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.ChCount
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.SFFam` (sha256 bddaee1b04d3ce40…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

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
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W13
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
variable {γF : ℝ}
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree WaveTurbulence.GammaLow.Famb.VineEstS4
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {P : WTParams} {κ0 : KPar P.d} {Bh : ℕ → ℝ} {hprime : IsPrimeGarden G}

/-- The exceptional pair of a core vine of the start state is part of the reconstruction: `zpN ≤ RD.size/2 ≤ order`. -/
theorem zpN_start_leΓ (i : (assemblySourceFamilyΓ B).CoreIndex) :
    2 * zpN (startStateΓ B RD hG layer hLayer) i ≤ (RD.garden hG).order := by
  classical
  have h2 := WaveTurbulence.ZpSurj.two_zpN (startStateΓ B RD hG layer hLayer) (pstar := i)
  have hd := RD.decoded_order hG (RD.garden_decodes hG)
  have ht : (RD.tree ((startStateΓ B RD hG layer hLayer).family.placement i).lower).size ≤ ∑ c, (RD.tree c).size :=
    Finset.single_le_sum (f := fun c => (RD.tree c).size) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hc : (RD.couple (pairOfLeaf G hG ((startStateΓ B RD hG layer hLayer).family.placement i).retained)).size ≤
      ∑ q, (RD.couple q).size :=
    Finset.single_le_sum (f := fun q => (RD.couple q).size) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hs : RD.size = (∑ c, (RD.tree c).size) + ∑ q, (RD.couple q).size := rfl
  change 2 * zpN (startStateΓ B RD hG layer hLayer) i = (RD.tree ((startStateΓ B RD hG layer hLayer).family.placement i).lower).size +
    (RD.couple (pairOfLeaf G hG ((startStateΓ B RD hG layer hLayer).family.placement i).retained)).size at h2
  omega

theorem zpN_lvl_leΓ (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (lv : LvlΓ B) (pstar : lv.ι) :
    zpN (lv.state B RD hG layer hLayer) pstar ≤ P.N (p + 1) ^ 4 := by
  rw [zpN_lvlΓ]
  have := zpN_start_leΓ B RD hG layer hLayer (lv.e pstar)
  omega

/-- **`SepFamFam` from the gates** (W1). -/
noncomputable def sffOfΓ (E : GateEnv P κ0 p Bh) (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) :
    SepFamFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime :=
  fun lv pstar hk h => sepFamOf (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
    h.some.canonical h.some.eligible h.some.treeCoherent h.some.coupleCoherent E
    (zpN_lvl_leΓ B RD hG layer hLayer hord lv pstar)

/-- **`SepFamFam.Bounded` of `sffOf`.** -/
theorem sffOf_boundedΓ (E : GateEnv P κ0 p Bh) (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) :
    SepFamFamΓ.Bounded (kind := kind) B RD hG layer hLayer (sffOfΓ (hprime := hprime) (kind := kind) B RD hG layer hLayer E hord) :=
  fun lv pstar hk h b =>
    ⟨certC_m_le (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
        h.some.canonical h.some.eligible h.some.treeCoherent h.some.coupleCoherent E
        (zpN_lvl_leΓ B RD hG layer hLayer hord lv pstar) b,
      certT_m_le (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
        h.some.canonical h.some.eligible h.some.treeCoherent h.some.coupleCoherent E
        (zpN_lvl_leΓ B RD hG layer hLayer hord lv pstar) b⟩

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W13
