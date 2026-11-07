/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.ZpCount

/-! # P4 count bridge (4): the number of summands of the bundle family, per vine (TARGET `4^b ∏ |Bs_i|`, L1919-L1922)

At an operative member `pstar` of a level, the bundle expansion of `bundleFamOf` has
`3 (∑_{bsA} m_Q m_T + ∑_{bsB} m_Q m_T) + ∑_{bsA} (m_Q + m_T + 1) + ∑_{bsB} (m_Q + m_T + 1)` summands (`card_bundleFamOf`).  With
`m_Q, m_T ≤ 2^N` (the separated expansions of P2's gate data, `sepFam_of_leafwise`: `m ≤ 2^{n}`, `n ≤ N = zpN`; the predicate
`SepFamFam.Bounded`) and `bsA, bsB ⊆ Zp(A)`, `card_zpFinset_le` gives

  `#Ch ≤ wtOf p (e pstar) = 192 (N + 1) (16·12⁹)^N 4^p`,  `N = zpN (startState) (e pstar)`

which depends on the core index only (`zpN` of a restricted state is that of the start state).  `Lvl.card_terms_le_prod` then bounds the
number of unrolled terms by `∏_{members} wtOf` (`card_terms_le_wt`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}

/-- The separated expansions have at most `2^N` terms, `N = zpN` (P2's `sepFam_of_leafwise`: `m ≤ 2^{n}` with `n ≤ zpN`). -/
def SepFamFam.Bounded (SFF : SepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime) : Prop :=
  ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (h : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar) b,
    (SFF lv pstar hk h).S.mQ b ≤ 2 ^ zpN (lv.state B RD hG layer hLayer) pstar ∧
      (SFF lv pstar hk h).S.mT b ≤ 2 ^ zpN (lv.state B RD hG layer hLayer) pstar

/-- The per-vine weight of the count. -/
noncomputable def wtOf (p : ℕ) (i : (assemblySourceFamily B).CoreIndex) : ℕ :=
  192 * (zpN (startState B RD hG layer hLayer) i + 1) * ((16 * 12 ^ 9) ^ zpN (startState B RD hG layer hLayer) i * 4 ^ p)

theorem one_le_wtOf (p : ℕ) (i : (assemblySourceFamily B).CoreIndex) : 1 ≤ wtOf B RD hG layer hLayer p i := by
  unfold wtOf
  have h1 : 1 ≤ (16 * 12 ^ 9) ^ zpN (startState B RD hG layer hLayer) i * 4 ^ p :=
    Nat.one_le_iff_ne_zero.2 (by positivity)
  nlinarith

/-- `zpN` of the state of a level is that of the start state at the core index. -/
theorem zpN_lvl (lv : Lvl B) (pstar : lv.ι) :
    zpN (lv.state B RD hG layer hLayer) pstar = zpN (startState B RD hG layer hLayer) (lv.e pstar) := rfl

theorem sum_le_of_bound {β : Type*} (s : Finset β) (f : β → ℕ) (c : ℕ) (h : ∀ b ∈ s, f b ≤ c) :
    ∑ b ∈ s, f b ≤ s.card * c := by
  simpa using Finset.sum_le_card_nsmul s f c h

open Classical in
/-- **The count per level and member.** -/
theorem card_bundleFamOf_le (hR : RealityAll) (SFF : SepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
    (hSB : SepFamFam.Bounded B RD hG layer hLayer SFF) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) :
    Fintype.card (bundleFamOf B RD hG layer hLayer hR SFF lv pstar hk).Ch ≤ wtOf B RD hG layer hLayer p (lv.e pstar) := by
  rw [card_bundleFamOf]
  split_ifs with h
  · set N := zpN (lv.state B RD hG layer hLayer) pstar with hN
    set Z := zpFinset p kind pstar {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime with hZ
    have hA : (bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
        (lv.split B RD hG layer hLayer pstar hk) hprime).card ≤ Z.card := Finset.card_filter_le _ _
    have hB : (bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
        (lv.split B RD hG layer hLayer pstar hk) hprime).card ≤ Z.card := Finset.card_filter_le _ _
    have hmm : ∀ b, (SFF lv pstar hk h).S.mQ b * (SFF lv pstar hk h).S.mT b ≤ 4 ^ N := fun b => by
      obtain ⟨h1, h2⟩ := hSB lv pstar hk h b
      rw [← hN] at h1 h2
      calc _ ≤ 2 ^ N * 2 ^ N := Nat.mul_le_mul h1 h2
        _ = 4 ^ N := by rw [← mul_pow]; norm_num
    have hpp : ∀ b, (SFF lv pstar hk h).S.mQ b + (SFF lv pstar hk h).S.mT b + 1 ≤ 3 * 4 ^ N := fun b => by
      obtain ⟨h1, h2⟩ := hSB lv pstar hk h b
      rw [← hN] at h1 h2
      have : 2 ^ N ≤ 4 ^ N := Nat.pow_le_pow_left (by norm_num) N
      have : 1 ≤ 4 ^ N := Nat.one_le_pow _ _ (by norm_num)
      omega
    have hZc := card_zpFinset_le (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
      h.some.canonical h.some.eligible h.some.treeCoherent h.some.coupleCoherent
    rw [← hZ, ← hN] at hZc
    set sA := bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime with hsA
    set sB := bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime with hsB
    have s1 := sum_le_of_bound sA _ _ fun b _ => hmm b
    have s2 := sum_le_of_bound sB _ _ fun b _ => hmm b
    have s3 := sum_le_of_bound sA _ _ fun b _ => hpp b
    have s4 := sum_le_of_bound sB _ _ fun b _ => hpp b
    have key : 3 * (sA.card * 4 ^ N + sB.card * 4 ^ N) + (sA.card * (3 * 4 ^ N) + sB.card * (3 * 4 ^ N)) ≤
        12 * Z.card * 4 ^ N := by
      have := Nat.mul_le_mul_right (4 ^ N) hA
      have := Nat.mul_le_mul_right (4 ^ N) hB
      nlinarith
    have hsum : 3 * ((∑ b ∈ sA, (SFF lv pstar hk h).S.mQ b * (SFF lv pstar hk h).S.mT b) +
          ∑ b ∈ sB, (SFF lv pstar hk h).S.mQ b * (SFF lv pstar hk h).S.mT b) +
        ((∑ b ∈ sA, ((SFF lv pstar hk h).S.mQ b + (SFF lv pstar hk h).S.mT b + 1)) +
          ∑ b ∈ sB, ((SFF lv pstar hk h).S.mQ b + (SFF lv pstar hk h).S.mT b + 1)) ≤ 12 * Z.card * 4 ^ N :=
      le_trans (by omega) key
    have hNe : zpN (startState B RD hG layer hLayer) (lv.e pstar) = N := by rw [hN]; rfl
    have hfin : 12 * Z.card * 4 ^ N ≤ wtOf B RD hG layer hLayer p (lv.e pstar) := by
      unfold wtOf
      rw [hNe]
      calc 12 * Z.card * 4 ^ N ≤ 12 * (16 * (N + 1) * ((4 * 12 ^ 9) ^ N * 4 ^ p)) * 4 ^ N :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hZc)
        _ = 192 * (N + 1) * ((16 * 12 ^ 9) ^ N * 4 ^ p) := by
            rw [show (16 : ℕ) * 12 ^ 9 = 4 * 4 * 12 ^ 9 by norm_num]; simp only [mul_pow]; ring
    exact hsum.trans hfin
  · exact one_le_wtOf B RD hG layer hLayer p _

/-- **The number of unrolled terms** is at most `∏_{members} wtOf`. -/
theorem card_terms_le_wt (hR : RealityAll) (SFF : SepFamFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
    (hSB : SepFamFam.Bounded B RD hG layer hLayer SFF) (m : ℕ) (lv : Lvl B) (hm : Fintype.card lv.ι ≤ m) :
    Multiset.card (Lvl.terms (p := p) (kind := kind) B RD hG layer hLayer (bundleFamOf B RD hG layer hLayer hR SFF) m lv) ≤
      ∏ j : lv.ι, wtOf B RD hG layer hLayer p (lv.e j) :=
  Lvl.card_terms_le_prod (p := p) (kind := kind) B RD hG layer hLayer (bundleFamOf B RD hG layer hLayer hR SFF) (wtOf B RD hG layer hLayer p)
    (one_le_wtOf B RD hG layer hLayer p) (card_bundleFamOf_le B RD hG layer hLayer hR SFF hSB) m lv hm

end WaveTurbulence.VineEstS5C.P4
