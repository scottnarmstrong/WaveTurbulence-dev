/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcInd
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClause

/-! # P4-W2 (session 11, F1 = F-BADD, R100): the staged statement `HFreeAt`

Clause (d) of `BadClauseP` at a block `i` of the engine datum of a term `ψ` that carries NO exceptional record: `bk i = canonBadKind i = 3`
(not `AClause i`), and one needs a row `v` of block `i` with `1 ≤ max (rowCoupleG v) (rowTreeG v)`.  The only proof in the code base
(`VineEstS3.bad_d`) needs `CoreVinesNoTwist` (deleted, false at operative vines).  The needed fact is that every eligible and coherent core
vine carries a record: a bad vine `i` that is not `AClause` is source-layer eligible, so if all rows of block `i` are coherent
(`rowCoupleG = rowTreeG = 0`) the vine is operative at the start state, and must be processed by some level of the descent (the twists of the
other members do not change eligibility and coherence of a non-processed member: `tree_other`/`couple_other`).

`QNEBody lv ψ recs Dm` is the body of `QNE` (`qne_iff`).  `HFreeAt ..` says: every term of the top-level `Lvl.termsB` has a record list
`recs`/domain `Dm` witnessing `QNE` such that every bad vine `i` that is not `AClause` either carries a record of `recs` (the block of a record
is that of its pair `r.p0` under `assemblyPairBij`) or has a row of block `i` with `1 ≤ max (rowCoupleG, rowTreeG)`.
It is carried as the hypothesis `hfree` of the internal assembly; instantiated at the actual families it is
`HFreeAt hM9 B RD hG layer hLayer (bundleFamOf ..) (bundleBotFamOf ..) (stepX ..) (botX ..)`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
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

/-- The body of `QNE`: the record list `recs` and the domain `Dm` of a term. -/
def QNEBody (lv : Lvl B) (ψ : PsiT G d) (recs : List (ExcRec G d)) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop) : Prop :=
  (∀ r ∈ recs, ExcOf B RD hG layer hLayer BE BX XE XB lv.c.U r ∧ r.p0 ∈ clRegionalPairs hG lv.c.U ∧
      r.bj ∈ lv.c.U.erase lv.c.a) ∧
    (recs.map ExcRec.p0).Nodup ∧ (recs.map ExcRec.bj).Nodup ∧
    (∀ t u, u lv.c.a = t 0 → (Dm t u ↔ DomX lv.region (layC RD hG layer) (bexOf recs) (t 0) (t 1) (t 2) u)) ∧
    RowFormNE RD hG κ0.L κ0.γ κ0.δ κ0.F layer hLayer lv.region κ0.base ψ Dm (pexOf recs) (bexOf recs) (xqOf recs)

theorem qne_iff (lv : Lvl B) (ψ : PsiT G d) :
    QNE B RD hG layer hLayer BE BX XE XB lv ψ ↔
      ∃ (recs : List (ExcRec G d)) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop),
        QNEBody B RD hG layer hLayer BE BX XE XB lv ψ recs Dm := Iff.rfl

/-- **`HFreeAt`** (staged hypothesis `hfree`, R100 F1): every term of the top-level `Lvl.termsB` has a `QNE` witness `(recs, Dm)` such that
every bad vine `i` that is not `AClause` carries a record of `recs` (at the block `i` of its pair `r.p0`) or has a row `v` of block `i`
with `1 ≤ max (rowCoupleG v) (rowTreeG v)` (i.e. a record-free eligible vine is incoherent: clause (d) of `BadClauseP`). -/
def HFreeAt (hM9 : VINEPARAM) : Prop :=
  ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B),
    ∃ (recs : List (ExcRec G d)) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop),
      QNEBody B RD hG layer hLayer BE BX XE XB (Lvl.top B) ψ recs Dm ∧
      ∀ i : Fin n, (assemblyPieceAt B i).vineType.IsBad = true → ¬ AClause hM9 B RD hG layer i →
        (∃ r ∈ recs, ∃ h : r.p0 ∈ clRegionalPairs hG U, (assemblyPairBij hG B hM9 ⟨r.p0, h⟩).1 = i) ∨
        ∃ v : (assemblyShape hM9 B).VIdx, v.1 = i ∧
          1 ≤ max (rowCoupleG hM9 B RD hG layer hLayer v) (rowTreeG hM9 B RD hG layer hLayer v)

end WaveTurbulence.VineEstS5C.P4.W2
