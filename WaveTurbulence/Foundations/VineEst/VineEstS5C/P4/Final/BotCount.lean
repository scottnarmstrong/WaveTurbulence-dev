/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.BotSFF
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.SFFam
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Count

/-! # (V5 FINAL copy of W13's `BotSFFam`, with the one `omega` -> `linarith` repair at `hsum`; namespace `P4.Final`.) P4-W1/W3 (bottom): `BotSepFamFam` from the gates, the bottom bundle size, and the count of `Lvl.termsB`

* **`botSffOf E hord hprime`** : `Bot.BotSepFamFam` (W1 for BOT-DECOMP): at every bottom level (operative member of piece index `0`,
  maximal among the operative members), `botSepFamOf` with the operation preconditions from `hop.some` and `hup := Bot.hup_of_max`.
* `botSffOf_bounded`: every bottom expansion has at most `2^{zpN}` terms.
* **`card_bundleBotFamOf_le`**: the bottom bundle size `≤ wtOf p (lv.e pstar)` (`Bot.card_bundleBotExpOf` + `card_canonFinset_le`): the
  hypothesis `hChB` of `Bot.Lvl.card_termsB_le_prod` (R60: the bottom member is counted like the others).
* **`card_termsB_le_wt`**: `#Lvl.termsB ≤ ∏_{members} wtOf` for the families `bundleFamOf hR (sffOf ..)`, `bundleBotFamOf hR (botSffOf ..)`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.Final
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {P : WTParams} {κ0 : KPar P.d} {Bh : ℕ → ℝ}

/-- **`BotSepFamFam` from the gates** (W1 for BOT-DECOMP). -/
noncomputable def botSffOf (hprime : IsPrimeGarden G) (E : GateEnv P κ0 p Bh) (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) :
    BotSepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0 :=
  fun lv pstar h0 hop hmax => botSepFamOf (lv.state B RD hG layer hLayer) lv.c hprime
    hop.some.canonical hop.some.eligible hop.some.treeCoherent hop.some.coupleCoherent
    (hup_of_max B RD hG layer hLayer lv pstar h0 hmax) E (zpN_lvl_le B RD hG layer hLayer hord lv pstar)

/-- Every bottom expansion has at most `2^{zpN}` terms. -/
theorem botSffOf_bounded (hprime : IsPrimeGarden G) (E : GateEnv P κ0 p Bh)
    (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) (b : BT w lv.ι) :
    (botSffOf B RD hG layer hLayer hprime E hord lv pstar h0 hop hmax).S.mQ b ≤ 2 ^ zpN (lv.state B RD hG layer hLayer) pstar ∧
      (botSffOf B RD hG layer hLayer hprime E hord lv pstar h0 hop hmax).S.mT b ≤ 2 ^ zpN (lv.state B RD hG layer hLayer) pstar :=
  ⟨botCertC_m_le (lv.state B RD hG layer hLayer) lv.c hprime hop.some.canonical hop.some.eligible hop.some.treeCoherent
      hop.some.coupleCoherent (hup_of_max B RD hG layer hLayer lv pstar h0 hmax) E (zpN_lvl_le B RD hG layer hLayer hord lv pstar) b,
    botCertT_m_le (lv.state B RD hG layer hLayer) lv.c hprime hop.some.canonical hop.some.eligible hop.some.treeCoherent
      hop.some.coupleCoherent (hup_of_max B RD hG layer hLayer lv pstar h0 hmax) E (zpN_lvl_le B RD hG layer hLayer hord lv pstar) b⟩

open Classical in
/-- **The bottom bundle size** is at most `wtOf p (lv.e pstar)` (the hypothesis `hChB` of `Lvl.card_termsB_le_prod`). -/
theorem card_bundleBotFamOf_le (hprime : IsPrimeGarden G) (hR : RealityAll) (E : GateEnv P κ0 p Bh)
    (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) :
    Fintype.card (bundleBotFamOf B RD hG layer hLayer hprime hR (botSffOf B RD hG layer hLayer hprime E hord)
      lv pstar h0 hop hmax).Ch ≤ wtOf B RD hG layer hLayer p (lv.e pstar) := by
  set SF := botSffOf B RD hG layer hLayer hprime E hord lv pstar h0 hop hmax with hSF
  have hcard : Fintype.card (bundleBotFamOf B RD hG layer hLayer hprime hR (botSffOf B RD hG layer hLayer hprime E hord)
      lv pstar h0 hop hmax).Ch = _ := card_bundleBotExpOf B RD hG layer hLayer hprime hR lv pstar h0 hop hmax SF
  rw [hcard]
  set N := zpN (lv.state B RD hG layer hLayer) pstar with hN
  set Z := canonFinsetK p kind (lv.state B RD hG layer hLayer) lv.c with hZ
  set sA := botA p kind pstar (lv.state B RD hG layer hLayer) lv.c with hsA
  set sB := botB p kind pstar (lv.state B RD hG layer hLayer) lv.c with hsB
  have hA : sA.card ≤ Z.card := Finset.card_filter_le _ _
  have hB : sB.card ≤ Z.card := Finset.card_filter_le _ _
  have hbd := botSffOf_bounded B RD hG layer hLayer hprime E hord lv pstar h0 hop hmax
  have hmm : ∀ b, SF.S.mQ b * SF.S.mT b ≤ 4 ^ N := fun b => by
    obtain ⟨h1, h2⟩ := hbd b
    calc _ ≤ 2 ^ N * 2 ^ N := Nat.mul_le_mul h1 h2
      _ = 4 ^ N := by rw [← mul_pow]; norm_num
  have hpp : ∀ b, SF.S.mQ b + SF.S.mT b + 1 ≤ 3 * 4 ^ N := fun b => by
    obtain ⟨h1, h2⟩ := hbd b
    have h1' : SF.S.mQ b ≤ 2 ^ N := h1
    have h2' : SF.S.mT b ≤ 2 ^ N := h2
    have : 2 ^ N ≤ 4 ^ N := Nat.pow_le_pow_left (by norm_num) N
    have : 1 ≤ 4 ^ N := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hZc := card_canonFinset_le (lv.state B RD hG layer hLayer) lv.c hprime
    hop.some.canonical hop.some.eligible hop.some.treeCoherent hop.some.coupleCoherent
    (hup_of_max B RD hG layer hLayer lv pstar h0 hmax)
  rw [← hZ, ← hN] at hZc
  have s1 := sum_le_of_bound sA _ _ fun b _ => hmm b
  have s2 := sum_le_of_bound sB _ _ fun b _ => hmm b
  have s3 := sum_le_of_bound sA _ _ fun b _ => hpp b
  have s4 := sum_le_of_bound sB _ _ fun b _ => hpp b
  have key : 3 * (sA.card * 4 ^ N + sB.card * 4 ^ N) + (sA.card * (3 * 4 ^ N) + sB.card * (3 * 4 ^ N)) ≤
      12 * Z.card * 4 ^ N := by
    have := Nat.mul_le_mul_right (4 ^ N) hA
    have := Nat.mul_le_mul_right (4 ^ N) hB
    nlinarith
  have hsum : 3 * ((∑ b ∈ sA, SF.S.mQ b * SF.S.mT b) + ∑ b ∈ sB, SF.S.mQ b * SF.S.mT b) +
      ((∑ b ∈ sA, (SF.S.mQ b + SF.S.mT b + 1)) + ∑ b ∈ sB, (SF.S.mQ b + SF.S.mT b + 1)) ≤ 12 * Z.card * 4 ^ N :=
    le_trans (by linarith) key
  have hNe : zpN (startState B RD hG layer hLayer) (lv.e pstar) = N := by rw [hN]; rfl
  have hfin : 12 * Z.card * 4 ^ N ≤ wtOf B RD hG layer hLayer p (lv.e pstar) := by
    unfold wtOf
    rw [hNe]
    calc 12 * Z.card * 4 ^ N ≤ 12 * (16 * (N + 1) * ((4 * 12 ^ 9) ^ N * 4 ^ p)) * 4 ^ N :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hZc)
      _ = 192 * (N + 1) * ((16 * 12 ^ 9) ^ N * 4 ^ p) := by
          rw [show (16 : ℕ) * 12 ^ 9 = 4 * 4 * 12 ^ 9 by norm_num]; simp only [mul_pow]; ring
  exact hsum.trans hfin

/-- **The number of unrolled terms with the bottom bundle expanded** (`Lvl.termsB`, R60) is at most `∏_{members} wtOf`. -/
theorem card_termsB_le_wt (hprime : IsPrimeGarden G) (hR : RealityAll) (E : GateEnv P κ0 p Bh)
    (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (m : ℕ) (lv : Lvl B) (hm : Fintype.card lv.ι ≤ m) :
    Multiset.card (Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer
        (bundleFamOf B RD hG layer hLayer hR (sffOf (hprime := hprime) B RD hG layer hLayer E hord))
        (bundleBotFamOf B RD hG layer hLayer hprime hR (botSffOf B RD hG layer hLayer hprime E hord)) m lv) ≤
      ∏ j : lv.ι, wtOf B RD hG layer hLayer p (lv.e j) :=
  Lvl.card_termsB_le_prod (p := p) (kind := kind) B RD hG layer hLayer _ _ (wtOf B RD hG layer hLayer p) (one_le_wtOf B RD hG layer hLayer p)
    (card_bundleFamOf_le B RD hG layer hLayer hR _ (sffOf_bounded B RD hG layer hLayer E hord))
    (card_bundleBotFamOf_le B RD hG layer hLayer hprime hR E hord) m lv hm

end WaveTurbulence.VineEstS5C.P4.Final
