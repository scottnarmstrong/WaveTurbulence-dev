/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.GateData
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P1.Rem

/-! # P2: the gate data at the indices `b` of the bundle (step 7 (1), identification with P1's `Qf`, `Tf`, `remQ`, `remT`)

`zp_couple_gate`, `zp_tree_gate`: for `b ∈ zpFinset`, the separated expansion (`SepFam`) of the source approximant `srcQ κ b` (`srcT κ b`) on the native box and the
`RemT` whose kernel `f` is `K* - srcQ` (`K* - srcT`); and (`rem_eq`) on the native window, away from `t = Lr` of a trivial object (`hne`), `remQ κ (zpQfam κ A) b = f`
(P1's `zp_remQ_eq`), and `zpQfam κ A b = srcQ κ b` (`zp_Qf_eq_srcQ`), so the pieces built from `Qf`/`remQ` are the pieces of the `SepFam`/`RemT`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P2
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.ConjCoh TTree
  WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1
open scoped ENNReal

section
variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι] {P : WTParams}
  (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)

/-- **Gate data of the couple of the index `b`.** -/
theorem zp_couple_gate (hZ : ZpSurj p kind pstar J A sp0 hA) (hL : ZpLayers p kind J A sp0 hA) (κ : KPar P.d) (hκδ : κ.δ = P.δ)
    (hκL : κ.L = P.L) (hκγ : κ.γ = P.γ) (hg : CoherentGateH P) {Bh : ℕ → ℝ} (hB : ProfileBound P κ.F Bh p) (hd : 1 ≤ P.d)
    (hL1 : 1 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hη : P.η ≤ 1) (hθ : 6 * P.η ^ 6 ≤ P.η) (hp : p < P.D)
    {b : ST w ι pstar J} (hb : b ∈ zpFinset p kind pstar J A sp0 hA) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4)
    (hsize : (zpCodeC b.1 pstar).size = 2 * n)
    {CR : ℝ} (hCR : P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
      layerCost Bh (zpObjC b.1 pstar) < CR) :
    ∃ sf : SepFam P (30 * P.d) (timeBox (zpQQ b.1 pstar).1 (zpQQ b.1 pstar).2)
        ![((zpQQ b.1 pstar).1 : ℝ), (zpQQ b.1 pstar).2] (2 * (P.C₁ * P.C₁ ^ n))
        (P.C₁ * P.C₁ ^ n * layerCost Bh (zpObjC b.1 pstar)) (srcQ κ b),
      sf.m ≤ 2 ^ n ∧ (∀ i, (sf.term i).c = P.δ ^ n) ∧
      ∃ R : RemT P (30 * P.d) (timeBox (zpQQ b.1 pstar).1 (zpQQ b.1 pstar).2)
        ![((zpQQ b.1 pstar).1 : ℝ), (zpQQ b.1 pstar).2] CR,
        (R.f = fun ts k => KQstar κ.L κ.γ κ.δ κ.F (zpObjC b.1 pstar) (ts 0) (ts 1) k - srcQ κ b (ts 0) (ts 1) k) ∧
        ∀ (t s : ℝ), ((zpQQ b.1 pstar).1 : ℝ) ≤ t → t ≤ (zpQQ b.1 pstar).1 + 1 →
          ((zpLq b : ℝ) < t ∨ ¬ zpTrQ b) → ∀ k, remQ κ (zpQfam κ A) b t s k = R.f ![t, s] k := by
  obtain ⟨-, hle, hp'⟩ := hL.pair b hb
  have hc := (hZ.coherent b hb).1
  obtain ⟨κL, κγ, κδ, κF, κbase, κt0, κt1, κt2⟩ := κ
  simp only at hκδ hκL hκγ
  subst hκδ hκL hκγ
  obtain ⟨sf, hm, hcc, R, hR⟩ := couple_gate_data hg hB hd hL1 hC1 hδ hη hθ hp hn hle hp' hsize hc hCR
  refine ⟨sf, hm, hcc, R, hR, ?_⟩
  intro t s h1 h2 hne k
  rw [zp_remQ_eq A sp0 hA hZ hL _ hb h1 h2 hne s k, hR]
  rfl

/-- **Gate data of the tree of the index `b`** (`hqp : q ≤ p` is an input: `ZpLayers.branch` does not give it). -/
theorem zp_tree_gate (hZ : ZpSurj p kind pstar J A sp0 hA) (hL : ZpLayers p kind J A sp0 hA) (κ : KPar P.d) (hκδ : κ.δ = P.δ)
    (hκL : κ.L = P.L) (hκγ : κ.γ = P.γ) (hg : CoherentGateH P) {Bh : ℕ → ℝ} (hB : ProfileBound P κ.F Bh p) (hd : 1 ≤ P.d)
    (hL1 : 1 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hη : P.η ≤ 1) (hθ : 6 * P.η ^ 6 ≤ P.η) (hp : p < P.D)
    {b : ST w ι pstar J} (hb : b ∈ zpFinset p kind pstar J A sp0 hA) (hqp : (zpBranchQ b.1 pstar).1 ≤ p) {n : ℕ}
    (hn : n ≤ P.N (p + 1) ^ 4) (hsize : (zpCodeT b.1 pstar).size = 2 * n)
    {CR : ℝ} (hCR : P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
      layerCost Bh (zpObjT b.1 pstar) < CR) :
    ∃ sf : SepFam P 0 (timeBoxGt (zpBranchQ b.1 pstar).1 (zpBranchQ b.1 pstar).2)
        ![((zpBranchQ b.1 pstar).1 : ℝ), (zpBranchQ b.1 pstar).2] (2 * (P.C₁ * P.C₁ ^ n))
        (P.C₁ * P.C₁ ^ n * layerCost Bh (zpObjT b.1 pstar)) (srcT κ b),
      sf.m ≤ 2 ^ n ∧ (∀ i, (sf.term i).c = P.δ ^ n) ∧
      ∃ R : RemT P 0 (timeBoxGt (zpBranchQ b.1 pstar).1 (zpBranchQ b.1 pstar).2)
        ![((zpBranchQ b.1 pstar).1 : ℝ), (zpBranchQ b.1 pstar).2] CR,
        (R.f = fun ts k => KTstar κ.L κ.γ κ.δ κ.F (zpObjT b.1 pstar) (ts 0) (ts 1) k - srcT κ b (ts 0) (ts 1) k) ∧
        ∀ (t s : ℝ), ((zpBranchQ b.1 pstar).1 : ℝ) ≤ t → t ≤ (zpBranchQ b.1 pstar).1 + 1 →
          ((zpLt b : ℝ) < t ∨ ¬ zpTrT b) → ∀ k, remT κ (zpTfam κ A) b t s k = R.f ![t, s] k := by
  obtain ⟨-, hle⟩ := hL.branch b hb
  have hc := (hZ.coherent b hb).2
  obtain ⟨κL, κγ, κδ, κF, κbase, κt0, κt1, κt2⟩ := κ
  simp only at hκδ hκL hκγ
  subst hκδ hκL hκγ
  obtain ⟨sf, hm, hcc, R, hR⟩ := tree_gate_data hg hB hd hL1 hC1 hδ hη hθ hp hn hle hqp hsize hc hCR
  refine ⟨sf, hm, hcc, R, hR, ?_⟩
  intro t s h1 h2 hne k
  rw [zp_remT_eq A sp0 hA hZ hL _ hb h1 h2 hne s k, hR]
  rfl

end

end WaveTurbulence.VineEstS5C.P2
