/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.HFree.Ready
public import WaveTurbulence.Foundations.VineEst.HFree.QneRec

/-! # W2-HFREE (4): every operative member of a level carries a record

`RecCov lv recs`: every member `j` of the level that is operative at the start state has a record in `recs` whose pair is the pair of the
retained leaf of its designated placement.  `exists_qneR`: by induction on the fuel, every term of `Lvl.termsB m lv` (with `card lv.ι ≤ m`)
has a `QNE` witness with this property.
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


def RecCov (lv : Lvl B) (recs : List (ExcRec G d)) : Prop :=
  ∀ j : lv.ι, TopOp (p := p) (kind := kind) B RD hG layer hLayer (lv.e j) →
    ∃ r ∈ recs, r.p0 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
      ((lv.state B RD hG layer hLayer).family.placement j).retained

theorem exists_qneR (hL : κ0.L ≠ 0) (hXE : FrameShapeX B RD hG layer hLayer BE XE)
    (hXB : BotFrameShapeX B RD hG layer hLayer BX XB) :
    ∀ (m : ℕ) (lv : Lvl B), Fintype.card lv.ι ≤ m → ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer BE BX m lv,
      ∃ (recs : List (ExcRec G d)) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop),
        QNEBody B RD hG layer hLayer BE BX XE XB lv ψ recs Dm ∧ RecCov (p := p) (kind := kind) B RD hG layer hLayer lv recs := by
  intro m
  induction m with
  | zero =>
    intro lv hc ψ hψ
    have hE : IsEmpty lv.ι := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hc)
    rw [(Lvl.mem_termsB_zero B RD hG layer hLayer BE BX lv ψ).mp hψ]
    obtain ⟨recs, Dm, hb⟩ := (qne_iff B RD hG layer hLayer BE BX XE XB lv _).mp
      (qne_base B RD hG layer hLayer BE BX XE XB lv)
    exact ⟨recs, Dm, hb, fun j => (hE.false j).elim⟩
  | succ m ih =>
    intro lv hc ψ hψ
    rcases Lvl.mem_termsB_succ B RD hG layer hLayer BE BX m lv ψ hψ with ⟨hno, rfl⟩ | ⟨ps, h0, hop, hmax, c, rfl⟩ |
        ⟨ps, hk, hop, hmax, c, Ψ', hΨ', rfl⟩
    · obtain ⟨recs, Dm, hb⟩ := (qne_iff B RD hG layer hLayer BE BX XE XB lv _).mp
        (qne_base B RD hG layer hLayer BE BX XE XB lv)
      exact ⟨recs, Dm, hb, fun j hj => (hno ⟨j, (lvOp_iff B RD hG layer hLayer lv j).mpr hj⟩).elim⟩
    · obtain ⟨recs, Dm, hb, r, hr, hp⟩ := qneR_bot B RD hG layer hLayer BE BX XE XB hXB lv ps h0 hop hmax c
      refine ⟨recs, Dm, hb, fun j hj => ?_⟩
      have hjop := (lvOp_iff B RD hG layer hLayer lv j).mpr hj
      have h1 := hmax j hjop
      have h2 : lv.e j = lv.e ps := Subtype.ext (Fin.ext (by omega))
      have h3 : j = ps := lv.he h2
      subst h3
      exact ⟨r, hr, hp⟩
    · obtain ⟨recs', Dm', hb', hcov'⟩ := ih (lv.next B RD hG layer hLayer ps hk)
        (Nat.lt_succ_iff.mp ((Lvl.card_next_lt B RD hG layer hLayer lv ps hk).trans_le hc)) Ψ' hΨ'
      obtain ⟨recs, Dm, hb, ⟨r, hr, hp⟩, hkeep⟩ := qneR_step B RD hG layer hLayer BE BX XE XB hL hXE lv ps hk hop c Ψ'
        recs' Dm' hb'
      refine ⟨recs, Dm, hb, fun j hj => ?_⟩
      rcases lt_trichotomy (lv.e j).1.val (lv.e ps).1.val with hlt | heq | hgt
      · obtain ⟨r', hr', hp'⟩ := hcov' ⟨j, hlt⟩ hj
        obtain ⟨r'', hr'', hp''⟩ := hkeep r' hr'
        exact ⟨r'', hr'', hp''.trans hp'⟩
      · have h2 : lv.e j = lv.e ps := Subtype.ext (Fin.ext heq)
        have h3 : j = ps := lv.he h2
        subst h3
        exact ⟨r, hr, hp⟩
      · exact absurd (hmax j ((lvOp_iff B RD hG layer hLayer lv j).mpr hj)) (by omega)

end WaveTurbulence.VineEstS5C.P4.W2
