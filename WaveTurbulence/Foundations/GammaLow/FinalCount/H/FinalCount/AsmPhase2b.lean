/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase2b
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase3c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase3d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmRun3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3URun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3UStep
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Vine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAdm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCoords
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCDict
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCFlow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCGain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCInj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCLadProd
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCScale
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmPhase2b`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY, phase 2: per-node facts** (invariant of the post class, dart count decrease, deviation in `stepRHS` form).
Ghost-free triangles use G3 `tri_excess` and `stepRHS_tri`; triangles with a ghost use the named input `GhostTriangleStep`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem runInv_of_reach {M₀ : Molecule V D₀} {Rn : ℕ} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} (hS : SubHyp Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Relation.ReflTransGen (HAny L γ η w κ) (HSt.init M₀) h) : RunInv Rn L γ η w κ h :=
  rtgH (S := HAny L γ η w κ) (P := RunInv Rn L γ η w κ)
    (fun _ _ hs hI => by rcases hs with hs | hs | hs | hs; exacts [hI.step1L hs, hI.step2 hs, hI.step3 hs, hI.step4 hs]) hr
    (RunInv.init hS h0)

theorem node2_facts [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 A : Set (D₀ → (Fin d → ℤ))} (H : TriReal d L γ η δ C₁) (hS : SubHyp Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hRA : ∀ κ h, Rch κ h → Relation.ReflTransGen (HAny L γ η w κ) (HSt.init M₀) h)
    (h8 : 8 * η ≤ 2 * γ - 1)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    {h : HSt V D₀} (hA : Inv3 M₀ Rn Rch L w A0 A h) {n : T2 h} (hn : Node2 L γ η h n)
    (hext : ∀ k ∈ cls2 L γ η w h A n, Rch k h → Rch k (post2 L γ η h n)) :
    Inv3 M₀ Rn Rch L w A0 (cls2 L γ η w h A n) (post2 L γ η h n) ∧
    Fintype.card (post2 L γ η h n).s.D < Fintype.card h.s.D ∧
    QS L γ δ C₁ w P h (cls2 L γ η w h A n) ≤
      ENNReal.ofReal (ghostConst d c η δ * stepRHS L γ η h (post2 L γ η h n)) *
        QS L γ δ C₁ w P (post2 L γ η h n) (cls2 L γ η w h A n) := by
  have hsub : cls2 L γ η w h A n ⊆ A := fun k hk => hk.1
  have hlt := card_dart_post2 hn
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hQpos : ∀ j, 0 < Q2 n j := fun j => zpow_pos (by norm_num) _
  by_cases hAe : cls2 L γ η w h A n = ∅
  · refine ⟨⟨hsub.trans hA.1, Or.inl hAe⟩, hlt, ?_⟩
    rw [hAe, QS_empty]; exact bot_le
  rcases hA.2 with he | ⟨hc, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hsub)) hAe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAe
  have hcc := uctx_mono hc (fun k (hk : k ∈ cls2 L γ η w h A n) => hk.1)
  have hpp := pinned_mono hp0 (fun k (hk : k ∈ cls2 L γ η w h A n) => hA.1 hk.1)
  have hst := uStep2_node (L := L) (γ := γ) (η := η) (w := w) (A := A) hn
  have hc' : UCtx M₀ Rn (fun k => k ∈ cls2 L γ η w h A n) L w (post2 L γ η h n) := UCtx.step2 hκ hst hpp hcc
  have hap' : ApPos (post2 L γ η h n).s := by
    rw [post2_eq hn]; exact apPos_triSt hap _ _ _ hQpos _
  have hr' : ∀ k ∈ cls2 L γ η w h A n, Rch k (post2 L γ η h n) := fun k hk => hext k hk (hr k hk.1)
  refine ⟨⟨hsub.trans hA.1, Or.inr ⟨hc', hap', hr'⟩⟩, hlt, ?_⟩
  have hI : Inv Rn h.s := hc.good.1
  have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
  have hcard : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c := by
    have := UCtx.card_atoms_le hS hcc
    exact le_trans (by exact_mod_cast this) hnc
  have hX : 0 ≤ stepRHS L γ η h (post2 L γ η h n) := by
    unfold stepRHS
    have h1 := apProd_pos (L := L) (γ := γ) (η := η) hL hap
    have h2 := apProd_pos (L := L) (γ := γ) (η := η) hL hap'
    positivity
  have hCB : CompBeta h.s := (invE_of_reach hS (h0 κ (hA.1 hκ.1)) (hRA κ h (hr κ hκ.1))).comp
  have hRI : ∀ k0, k0 ∈ cls2 L γ η w h A n → HInv L γ η w k0 h ∧ HGap L w k0 h := fun k0 hk0 => by
    have := runInv_of_reach hS (h0 k0 (hA.1 hk0.1)) (hRA k0 h (hr k0 hk0.1))
    exact ⟨this.hrec, this.gap⟩
  obtain ⟨T', Q', kp', hcl', hEq, hdev⟩ := UStep2.excess H hst hLC hc.good.2 hCB hcc.atom P hP0 hP hcard ⟨κ, hκ⟩ hRI h8
  rw [hEq] at hX hdev ⊢
  rw [stepRHS_tri' hL hap T' Q' kp' hcl'] at hX ⊢
  exact hdev

end WaveTurbulence.GammaLow.FinalCount.H
