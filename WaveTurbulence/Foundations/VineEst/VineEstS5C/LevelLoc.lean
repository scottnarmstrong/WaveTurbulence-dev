/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelBundle
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelStep

/-! # Clock locality of the S-side bundle (V5 Step 4d part C, WP-I)

`DomF_congr`, `qRow_congr`, `tRow_congr`, `spartFrame_congr`: the frame of the S-part reads the clock only on `S`;
`qbOf_mem`, `qrOf_mem`: the parents of the lower joint and of the partner of the retained leaf lie in the upper block;
`bundleKernel_congr`, `psiSB_congr`: the bundle `psiSB` reads the clock only on the upper block (hypothesis `hlocS` of `flat_merge`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem DomF_congr (hS : G.molecule.IsBlock S a b) (RS : CLRegionData G S a b) (lay : GBranch G.tree → ℕ)
    {u u' : GBranch G.tree → ℝ} (h : ∀ v ∈ S, u v = u' v) : DomF lay S a b u ↔ DomF lay S a b u' := by
  have ha : u a = u' a := h a hS.2.1
  have key : ∀ v ∈ S.erase a, parentClock (u a) u v.toNode = parentClock (u' a) u' v.toNode := by
    intro v hv
    obtain ⟨hva, hvS⟩ := Finset.mem_erase.mp hv
    rw [ha]
    exact parentClock_congr_S hS RS h ((branch_mem_clRealizationNodes v).mpr hvS)
      (fun e => hva (Mole.branch_toNode_injective e))
  unfold DomF
  constructor
  · intro H v hv
    have hvS := (Finset.mem_erase.mp hv).2
    obtain ⟨h1, h2, h3, h4⟩ := H v hv
    have e := h v hvS
    refine ⟨by rw [← e]; exact h1, by rw [← e]; exact h2, by rw [← e]; exact h3, fun hvb => ?_⟩
    rw [← key v hv, ← e]
    exact h4 hvb
  · intro H v hv
    have hvS := (Finset.mem_erase.mp hv).2
    obtain ⟨h1, h2, h3, h4⟩ := H v hv
    have e := h v hvS
    refine ⟨by rw [e]; exact h1, by rw [e]; exact h2, by rw [e]; exact h3, fun hvb => ?_⟩
    rw [key v hv, e]
    exact h4 hvb

section Rows
variable (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)

theorem qRow_congr (hS : G.molecule.IsBlock S a b) (RS : CLRegionData G S a b) {top : ℝ}
    (x : GNode G.tree → (Fin d → ℤ)) {u u' : GBranch G.tree → ℝ} (h : ∀ v ∈ S, u v = u' v) (q : SourcePair G)
    (hq : q ∈ clRegionalPairs hG S) :
    qRow D hG L γ δ F layer hLayer base top x u q = qRow D hG L γ δ F layer hLayer base top x u' q := by
  unfold qRow
  have hr := clRegionalPair_realization hG q hq
  rw [parentClock_congr_S hS RS h hr.1 (Mole.branch_toNode_ne_leaf a _).symm,
    parentClock_congr_S hS RS h hr.2 (Mole.branch_toNode_ne_leaf a _).symm]

theorem tRow_congr (hS : G.molecule.IsBlock S a b) (RS : CLRegionData G S a b) {top : ℝ}
    (x : GNode G.tree → (Fin d → ℤ)) {u u' : GBranch G.tree → ℝ} (h : ∀ v ∈ S, u v = u' v) (v : GBranch G.tree)
    (hv : v ∈ S.erase a) :
    tRow D hG L γ δ F layer hLayer base top x u v = tRow D hG L γ δ F layer hLayer base top x u' v := by
  unfold tRow
  obtain ⟨hva, hvS⟩ := Finset.mem_erase.mp hv
  rw [parentClock_congr_S hS RS h ((branch_mem_clRealizationNodes v).mpr hvS)
    (fun e => hva (Mole.branch_toNode_injective e)), h v hvS]

theorem spartFrame_congr (hS : G.molecule.IsBlock S a b) (RS : CLRegionData G S a b) (p0 : SourcePair G)
    (x : GNode G.tree → (Fin d → ℤ)) {u u' : GBranch G.tree → ℝ} (h : ∀ v ∈ S, u v = u' v) :
    spartFrame D hG L γ δ F layer hLayer base S a b p0 x u = spartFrame D hG L γ δ F layer hLayer base S a b p0 x u' := by
  classical
  have ha : u a = u' a := h a hS.2.1
  unfold spartFrame
  have h1 := DomF_congr hS RS (fun v => layer (D.coreBranch hG v).toNode) h
  have h3 : ∏ q ∈ (clRegionalPairs hG S).erase p0, qRow D hG L γ δ F layer hLayer base (u a) x u q =
      ∏ q ∈ (clRegionalPairs hG S).erase p0, qRow D hG L γ δ F layer hLayer base (u' a) x u' q := by
    refine Finset.prod_congr rfl fun q hq => ?_
    rw [ha]
    exact qRow_congr D hG L γ δ F layer hLayer base hS RS x h q (Finset.mem_of_mem_erase hq)
  have h4 : ∏ v ∈ (S.erase a).erase b, tRow D hG L γ δ F layer hLayer base (u a) x u v =
      ∏ v ∈ (S.erase a).erase b, tRow D hG L γ δ F layer hLayer base (u' a) x u' v := by
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [ha]
    exact tRow_congr D hG L γ δ F layer hLayer base hS RS x h v (Finset.mem_of_mem_erase hv)
  rw [h3, h4, clRegionalPhase_congr (S.erase b) L γ δ (k := cosetDecoration G L base x) (u := u) (u' := u')
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun v hv => h v (Finset.mem_of_mem_erase hv))]
  by_cases hd : DomF (fun v => layer (D.coreBranch hG v).toNode) S a b u
  · simp [hd, h1.mp hd]
  · have hd' : ¬ DomF (fun v => layer (D.coreBranch hG v).toNode) S a b u' := fun h' => hd (h1.mpr h')
    simp [hd, hd']

end Rows


section Bundle
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {pstar : ι} {J : Set ι} {p : ℕ}

theorem qbOf_mem (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) :
    qbOf (A.family.placement pstar) ∈ sp.sb.U := by
  have hSlow := SplitAt.slow sp
  have hx : (A.family.placement pstar).lower.toNode ∈ clRealizationNodes A.skeleton sp.sb.U :=
    (branch_mem_clRealizationNodes _).mpr hSlow.lower_mem
  have hne : (A.family.placement pstar).lower.toNode ≠ sp.sb.a.toNode := fun he =>
    sp.sb.block.2.2.2.1 ((Mole.branch_toNode_injective he).symm.trans hSlow.lower.symm)
  exact (cl_realization_parent sp.sb.block sp.RS _ hx hne).choose_spec

theorem qrOf_mem (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) :
    qrOf (A.family.placement pstar) ∈ sp.sb.U := by
  have hSlow := SplitAt.slow sp
  have hx : (A.skeleton.pair (A.family.placement pstar).retained).toNode ∈ clRealizationNodes A.skeleton sp.sb.U :=
    (leaf_mem_clRealizationNodes _).mpr hSlow.partner_internal
  have hne : (A.skeleton.pair (A.family.placement pstar).retained).toNode ≠ sp.sb.a.toNode :=
    (Mole.branch_toNode_ne_leaf sp.sb.a _).symm
  exact (cl_realization_parent sp.sb.block sp.RS _ hx hne).choose_spec

theorem bundleKernel_congr (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
    (tw : Bool) (ν : ℤˣ) (rq rt : ℝ → ℝ → Mom d → ℂ) (x : GNode A.skeleton.tree → (Fin d → ℤ))
    {u u' : GBranch A.skeleton.tree → ℝ} (h : ∀ v ∈ sp.sb.U, u v = u' v) :
    bundleKernel κ A sp tw ν rq rt x u = bundleKernel κ A sp tw ν rq rt x u' := by
  have hb : u sp.sb.b = u' sp.sb.b := h _ sp.sb.block.2.2.1
  have hqb := h _ (qbOf_mem A sp)
  have hqr := h _ (qrOf_mem A sp)
  unfold bundleKernel
  rw [spartFrame_congr A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base sp.sb.block sp.RS _ x h]
  simp only [hb, hqb, hqr]

theorem psiSB_congr (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (x : GNode A.skeleton.tree → (Fin d → ℤ))
    {u u' : GBranch A.skeleton.tree → ℝ} (h : ∀ v ∈ sp.sb.U, u v = u' v) :
    psiSB (p := p) (kind := kind) κ A sp hA x u = psiSB (p := p) (kind := kind) κ A sp hA x u' := by
  unfold psiSB
  refine Finset.sum_congr rfl fun G _ => ?_
  rw [bundleKernel_congr κ A sp _ _ _ _ x h]

end Bundle

end WaveTurbulence.VineEstS5C
