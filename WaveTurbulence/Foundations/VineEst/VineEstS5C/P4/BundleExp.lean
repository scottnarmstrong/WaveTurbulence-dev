/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Index
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Win
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Unroll

/-! # P4: `BundleExp` per level from `bundle_decomp` / `bundle_decomp_mirror` (V5 Step 4d part C)

`SepFam`: the separated expansions of the approximant families `zpQfam`, `zpTfam` at the two time points of the bundle (to be delivered by P2 from the
gates; `PtOK` is the point domain of the expansions, `dom` says it holds on the frame domain).  `bundleExpOf`: the `BundleExp` of a level, with the
static case split (`CaseA` -> `bundle_decomp`, otherwise the mirror `bundle_decomp_mirror`).  The window `Win` is `bundleFrame = 0 ∨ (window ∧ PtOK)`:
outside the frame domain both `psiSB` and every summand vanish.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.ConjCoh TTree
  WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1
open scoped ComplexConjugate

set_option linter.unusedSectionVars false
section
variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} {d : ℕ} [Fintype ι] [DecidableEq ι]

variable (p kind J) in
/-- The separated expansions of the approximants of a level (input from P2/the gates). -/
structure SepFam (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) where
  S : SepTerms (ST w ι pstar J) d
  PtOK : ℝ → ℝ → ℝ → Prop
  hQ : ∀ t0 s1 t1, PtOK t0 s1 t1 → ∀ b, (b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) →
    (∀ k, zpQfam κ A b s1 t0 k = ∑ i, S.sQ b i s1 t0 k) ∧ ∀ k, zpQfam κ A b t1 t0 k = ∑ i, S.sQ b i t1 t0 k
  hT : ∀ t0 s1 t1, PtOK t0 s1 t1 → ∀ b, (b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) →
    (∀ k, zpTfam κ A b s1 t0 k = ∑ j, S.sT b j s1 t0 k) ∧ ∀ k, zpTfam κ A b t1 t0 k = ∑ j, S.sT b j t1 t0 k
  dom : ∀ (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ),
    DomF (layOf A) sp0.sb.U sp0.sb.a sp0.sb.b u →
    (layOf A sp0.sb.a : ℝ) < u sp0.sb.a → u sp0.sb.a < layOf A sp0.sb.a + 1 →
    PtOK (bundleVars κ A sp0 x u).1 (bundleVars κ A sp0 x u).2.1 (bundleVars κ A sp0 x u).2.2.1

theorem psiSB_eq_zero_of_frame (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ)
    (h : bundleFrame κ A sp0 x u = 0) : psiSB (p := p) (kind := kind) κ A sp0 hA x u = 0 := by
  classical
  have h' : spartFrame A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base sp0.sb.U sp0.sb.a
      sp0.sb.b (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) x u = 0 := h
  unfold psiSB bundleKernel
  simp [h']

variable (p kind J) in
open Classical in
/-- The window of the bundle (see the module docstring). -/
def BundleWin (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (SF : SepFam p kind J κ A sp0 hA)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ) : Prop :=
  bundleFrame κ A sp0 x u = 0 ∨
    ((if CaseA (pstar := pstar) A then
        (zpQ4 A pstar : ℝ) < (bundleVars κ A sp0 x u).2.2.1 ∧ (bundleVars κ A sp0 x u).2.2.1 ≤ zpQ4 A pstar + 1
      else
        (zpQ4 A pstar : ℝ) < (bundleVars κ A sp0 x u).2.1 ∧ (bundleVars κ A sp0 x u).2.1 ≤ zpQ4 A pstar + 1) ∧
      (zpQ2 A pstar : ℝ) ≤ (bundleVars κ A sp0 x u).1 ∧ (bundleVars κ A sp0 x u).1 ≤ zpQ2 A pstar + 1 ∧
      SF.PtOK (bundleVars κ A sp0 x u).1 (bundleVars κ A sp0 x u).2.1 (bundleVars κ A sp0 x u).2.2.1)

/-- **`BundleWin` holds** wherever the exterior clock is in its window. -/
theorem bundleWin_holds (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (SF : SepFam p kind J κ A sp0 hA) (hr : RetParent (pstar := pstar) A)
    (hq2 : zpQ2 A pstar ≤ layOf A (qrOf (A.family.placement pstar)))
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ)
    (hext : (layOf A sp0.sb.a : ℝ) < u sp0.sb.a ∧ u sp0.sb.a < layOf A sp0.sb.a + 1) :
    BundleWin p kind J κ A sp0 hA SF x u := by
  classical
  by_cases hf : bundleFrame κ A sp0 x u = 0
  · exact Or.inl hf
  · right
    have hD := domF_of_frame_ne κ A sp0 x u hf
    have hP := SF.dom x u hD hext.1 hext.2
    by_cases hca : CaseA (pstar := pstar) A
    · obtain ⟨a1, a2, a3, a4⟩ := window_caseA κ A sp0 hr hq2 hca x u hD hext
      exact ⟨by rw [if_pos hca]; exact ⟨a1, a2⟩, a3, a4, hP⟩
    · have hM : CaseM (pstar := pstar) A := (caseA_or_caseM A).resolve_left hca
      obtain ⟨a1, a2, a3, a4⟩ := window_caseM κ A sp0 hr hq2 hM x u hD hext
      exact ⟨by rw [if_neg hca]; exact ⟨a1, a2⟩, a3, a4, hP⟩

variable (p kind J) in
open Classical in
/-- The summand `c` of the bundle at the point `(t₀, s₁, t₁, x, y)`: the pieces (mirrored and conjugated in case M) and the remainder rows. -/
noncomputable def bundlePt (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (SF : SepFam p kind J κ A sp0 hA) (bs₁ bs₂ : Finset (ST w ι pstar J))
    (t0 s1 t1 : ℝ) (x y : Mom d) : Ch SF.S bs₁ bs₂ (bsA p kind J A sp0 hA) (bsB p kind J A sp0 hA) → ℂ :=
  Sum.elim (fun c => if CaseA (pstar := pstar) A then ptP SF.S bs₁ bs₂ t0 s1 t1 x y c
      else -(starRingEnd ℂ) (ptP SF.S bs₁ bs₂ t0 t1 s1 y x c))
    (fun c => ptR SF.S (remQ κ (zpQfam κ A)) (remT κ (zpTfam κ A)) (bsA p kind J A sp0 hA) (bsB p kind J A sp0 hA) t0 s1 t1 x y c)

variable (p kind J) in
/-- The summand `c` of the bundle as a function of the decoration and the clock. -/
noncomputable def bundleTerm (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (SF : SepFam p kind J κ A sp0 hA) (bs₁ bs₂ : Finset (ST w ι pstar J))
    (c : Ch SF.S bs₁ bs₂ (bsA p kind J A sp0 hA) (bsB p kind J A sp0 hA))
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ) : ℂ :=
  bundleFrame κ A sp0 x u * ((nuOf A pstar : ℤˣ) : ℂ) *
    bundlePt p kind J κ A sp0 hA SF bs₁ bs₂ (bundleVars κ A sp0 x u).1 (bundleVars κ A sp0 x u).2.1 (bundleVars κ A sp0 x u).2.2.1
      (bundleVars κ A sp0 x u).2.2.2.1 (bundleVars κ A sp0 x u).2.2.2.2 c

open Classical in
/-- **The bundle is the sum of its summands** on the window. -/
theorem psiSB_eq_sum_terms (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (hR : RealityAll) (hZ : ZpSurj p kind pstar J A sp0 hA) (hL : ZpLayers p kind J A sp0 hA) (κ : KPar d)
    (SF : SepFam p kind J κ A sp0 hA) (hr : RetParent (pstar := pstar) A)
    (bs₁ bs₂ : Finset (ST w ι pstar J))
    (hc : (CaseA (pstar := pstar) A → bs₁ = bsA p kind J A sp0 hA ∧ bs₂ = bsB p kind J A sp0 hA) ∧
      (¬ CaseA (pstar := pstar) A → bs₁ = bsB p kind J A sp0 hA ∧ bs₂ = bsA p kind J A sp0 hA))
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ)
    (hW : BundleWin p kind J κ A sp0 hA SF x u) :
    psiSB (p := p) (kind := kind) κ A sp0 hA x u = ∑ c, bundleTerm p kind J κ A sp0 hA SF bs₁ bs₂ c x u := by
  classical
  have hsum : ∑ c, bundleTerm p kind J κ A sp0 hA SF bs₁ bs₂ c x u = bundleFrame κ A sp0 x u * (((nuOf A pstar : ℤˣ) : ℂ) *
      ∑ c, bundlePt p kind J κ A sp0 hA SF bs₁ bs₂ (bundleVars κ A sp0 x u).1 (bundleVars κ A sp0 x u).2.1
        (bundleVars κ A sp0 x u).2.2.1 (bundleVars κ A sp0 x u).2.2.2.1 (bundleVars κ A sp0 x u).2.2.2.2 c) := by
    unfold bundleTerm
    rw [← Finset.mul_sum]; ring
  rcases hW with hf | ⟨hwin, h0, h0', hP⟩
  · rw [psiSB_eq_zero_of_frame κ A sp0 hA x u hf, hsum, hf, zero_mul]
  · generalize hv : bundleVars κ A sp0 x u = v at hP hwin h0 h0'
    have hq := SF.hQ _ _ _ hP
    have hT := SF.hT _ _ _ hP
    by_cases hca : CaseA (pstar := pstar) A
    · obtain ⟨e1, e2⟩ := hc.1 hca
      subst e1 e2
      rw [if_pos hca] at hwin
      rw [← hv] at hwin h0 h0'
      rw [bundle_decomp A sp0 hA hR hZ hL κ x u hwin.1 hwin.2 h0 h0', hsum, hv]
      congr 2
      rw [Fintype.sum_sum_type]
      simp only [bundlePt, Sum.elim_inl, Sum.elim_inr, if_pos hca]
      rw [sum_ptP_eq SF.S (zpQfam κ A) (zpTfam κ A) (bsA p kind J A sp0 hA) (bsB p kind J A sp0 hA) v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2
          (fun b hb => hq b hb) (fun b hb => hT b hb),
        sum_ptR_eq SF.S (zpQfam κ A) (zpTfam κ A) (remQ κ (zpQfam κ A)) (remT κ (zpTfam κ A)) (bsA p kind J A sp0 hA) (bsB p kind J A sp0 hA)
          v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 (fun b hb => hq b hb) (fun b hb => hT b hb)]
      rfl
    · obtain ⟨e1, e2⟩ := hc.2 hca
      subst e1 e2
      rw [if_neg hca] at hwin
      rw [← hv] at hwin h0 h0'
      rw [bundle_decomp_mirror A sp0 hA hR hZ hL κ x u hwin.1 hwin.2 h0 h0', hsum, hv]
      congr 2
      rw [Fintype.sum_sum_type]
      simp only [bundlePt, Sum.elim_inl, Sum.elim_inr, if_neg hca, Finset.sum_neg_distrib, ← map_sum]
      rw [sum_ptP_eq SF.S (zpQfam κ A) (zpTfam κ A) (bsB p kind J A sp0 hA) (bsA p kind J A sp0 hA) v.1 v.2.2.1 v.2.1 v.2.2.2.2 v.2.2.2.1
          (fun b hb => ⟨(hq b hb.symm).2, (hq b hb.symm).1⟩) (fun b hb => ⟨(hT b hb.symm).2, (hT b hb.symm).1⟩),
        sum_ptR_eq SF.S (zpQfam κ A) (zpTfam κ A) (remQ κ (zpQfam κ A)) (remT κ (zpTfam κ A)) (bsA p kind J A sp0 hA) (bsB p kind J A sp0 hA)
          v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 (fun b hb => hq b hb) (fun b hb => hT b hb)]
      rfl

end

section Level
open WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS5B MeasureTheory
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable {kind : Bool}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}

open Classical in
/-- **`BundleExp` of a level** from the separated expansions `SF`, the typing inputs `hZ`, `hL`, `hr` and `hR` (PL234 `reality_all`). -/
noncomputable def bundleExpOf (hR : RealityAll) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hZ : ZpSurj p kind pstar {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime)
    (hL : ZpLayers p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime)
    (hr : RetParent (pstar := pstar) (lv.state B RD hG layer hLayer))
    (SF : SepFam p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} κ0 (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime) :
    BundleExp (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime lv pstar hk where
  Ch := Ch SF.S
    (if CaseA (pstar := pstar) (lv.state B RD hG layer hLayer) then
      bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
      else bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
    (if CaseA (pstar := pstar) (lv.state B RD hG layer hLayer) then
      bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
      else bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
    (bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
    (bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime)
  term := fun c x u => bundleTerm p kind _ κ0 _ _ hprime SF _ _ c x u
  Win := BundleWin p kind _ κ0 _ _ hprime SF
  eq := fun x u hW => psiSB_eq_sum_terms _ _ hprime hR hZ hL κ0 SF hr _ _
    ⟨fun h => by simp [if_pos h], fun h => by simp [if_neg h]⟩ x u hW

/-- **The number of summands of a level's bundle** (independent of the static case split):
`3 (∑_{bsA} mQ mT + ∑_{bsB} mQ mT) + ∑_{bsA} (mQ + mT + 1) + ∑_{bsB} (mQ + mT + 1)`. -/
theorem card_bundleExpCh (hR : RealityAll) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hZ : ZpSurj p kind pstar {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime)
    (hL : ZpLayers p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime)
    (hr : RetParent (pstar := pstar) (lv.state B RD hG layer hLayer))
    (SF : SepFam p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} κ0 (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime) :
    Fintype.card (bundleExpOf B RD hG layer hLayer hR lv pstar hk hZ hL hr SF).Ch =
      3 * ((∑ b ∈ bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
              (lv.split B RD hG layer hLayer pstar hk) hprime, SF.S.mQ b * SF.S.mT b) +
            ∑ b ∈ bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
              (lv.split B RD hG layer hLayer pstar hk) hprime, SF.S.mQ b * SF.S.mT b) +
        ((∑ b ∈ bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
              (lv.split B RD hG layer hLayer pstar hk) hprime, (SF.S.mQ b + SF.S.mT b + 1)) +
          ∑ b ∈ bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
              (lv.split B RD hG layer hLayer pstar hk) hprime, (SF.S.mQ b + SF.S.mT b + 1)) := by
  classical
  unfold bundleExpOf
  show Fintype.card (Ch _ _ _ _ _) = _
  rw [card_ch]
  split_ifs <;> ring

end Level
end WaveTurbulence.VineEstS5C.P4
