/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot16

/-! # V5 Step 4d-B2: the bottom vine, part 17 (clock locality of the bundle)

`psiBot_congr`: the bundle `psiBot` reads the clock only on the atoms of the chain region (hypothesis of the locality of the summands in
the induction over the core vines, TARGET Step 4).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem DomF_clock_congr (hS : G.molecule.IsBlock S a b) (RS : CLRegionData G S a b) (lay : GBranch G.tree → ℕ)
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

theorem qRow_clock_congr (hS : G.molecule.IsBlock S a b) (RS : CLRegionData G S a b) {top : ℝ}
    (x : GNode G.tree → (Fin d → ℤ)) {u u' : GBranch G.tree → ℝ} (h : ∀ v ∈ S, u v = u' v) (q : SourcePair G)
    (hq : q ∈ clRegionalPairs hG S) :
    qRow D hG L γ δ F layer hLayer base top x u q = qRow D hG L γ δ F layer hLayer base top x u' q := by
  unfold qRow
  have hr := clRegionalPair_realization hG q hq
  rw [parentClock_congr_S hS RS h hr.1 (Mole.branch_toNode_ne_leaf a _).symm,
    parentClock_congr_S hS RS h hr.2 (Mole.branch_toNode_ne_leaf a _).symm]

theorem tRow_clock_congr (hS : G.molecule.IsBlock S a b) (RS : CLRegionData G S a b) {top : ℝ}
    (x : GNode G.tree → (Fin d → ℤ)) {u u' : GBranch G.tree → ℝ} (h : ∀ v ∈ S, u v = u' v) (v : GBranch G.tree)
    (hv : v ∈ S.erase a) :
    tRow D hG L γ δ F layer hLayer base top x u v = tRow D hG L γ δ F layer hLayer base top x u' v := by
  unfold tRow
  obtain ⟨hva, hvS⟩ := Finset.mem_erase.mp hv
  rw [parentClock_congr_S hS RS h ((branch_mem_clRealizationNodes v).mpr hvS)
    (fun e => hva (Mole.branch_toNode_injective e)), h v hvS]

theorem spartFrame_clock_congr (hS : G.molecule.IsBlock S a b) (RS : CLRegionData G S a b) (p0 : SourcePair G)
    (x : GNode G.tree → (Fin d → ℤ)) {u u' : GBranch G.tree → ℝ} (h : ∀ v ∈ S, u v = u' v) :
    spartFrame D hG L γ δ F layer hLayer base S a b p0 x u = spartFrame D hG L γ δ F layer hLayer base S a b p0 x u' := by
  classical
  have ha : u a = u' a := h a hS.2.1
  unfold spartFrame
  have h1 := DomF_clock_congr hS RS (fun v => layer (D.coreBranch hG v).toNode) h
  have h3 : ∏ q ∈ (clRegionalPairs hG S).erase p0, qRow D hG L γ δ F layer hLayer base (u a) x u q =
      ∏ q ∈ (clRegionalPairs hG S).erase p0, qRow D hG L γ δ F layer hLayer base (u' a) x u' q := by
    refine Finset.prod_congr rfl fun q hq => ?_
    rw [ha]
    exact qRow_clock_congr D hG L γ δ F layer hLayer base hS RS x h q (Finset.mem_of_mem_erase hq)
  have h4 : ∏ v ∈ (S.erase a).erase b, tRow D hG L γ δ F layer hLayer base (u a) x u v =
      ∏ v ∈ (S.erase a).erase b, tRow D hG L γ δ F layer hLayer base (u' a) x u' v := by
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [ha]
    exact tRow_clock_congr D hG L γ δ F layer hLayer base hS RS x h v (Finset.mem_of_mem_erase hv)
  rw [h3, h4, clRegionalPhase_congr (S.erase b) L γ δ (k := cosetDecoration G L base x) (u := u) (u' := u')
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun v hv => h v (Finset.mem_of_mem_erase hv))]
  by_cases hd : DomF (fun v => layer (D.coreBranch hG v).toNode) S a b u
  · simp [hd, h1.mp hd]
  · have hd' : ¬ DomF (fun v => layer (D.coreBranch hG v).toNode) S a b u' := fun h' => hd (h1.mpr h')
    simp [hd, hd']

end Rows

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {pstar : ι} {p : ℕ}

theorem botKernel_congr (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hb0 : c0.b = (A.family.placement pstar).lower) (tw : Bool) (ν : ℤˣ) (rq rt : ℝ → ℝ → Mom d → ℂ)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    {u u' : GBranch A.skeleton.tree → ℝ} (h : ∀ v ∈ c0.U, u v = u' v) :
    botKernel κ A c0 pstar tw ν rq rt x t u = botKernel κ A c0 pstar tw ν rq rt x t u' := by
  have hS := chain_slow c0 pstar hb0
  have hb : u c0.b = u' c0.b := h _ c0.block.2.2.1
  have hqb := h _ hS.qb_mem
  have hqr := h _ hS.qr_mem
  unfold botKernel
  rw [spartFrame_clock_congr A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base c0.block
    (botR A c0) _ x h]
  have hbf : bFac (botR A c0) κ.L κ.γ κ.δ κ.base x t u = bFac (botR A c0) κ.L κ.γ κ.δ κ.base x t u' := by
    unfold bFac bTimeOK
    rw [hb]
  rw [hbf]
  simp only [hb, hqb, hqr]

theorem psiBot_congr (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hb0 : c0.b = (A.family.placement pstar).lower) (x : GNode A.skeleton.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    {u u' : GBranch A.skeleton.tree → ℝ} (h : ∀ v ∈ c0.U, u v = u' v) :
    psiBot p kind κ A c0 pstar x t u = psiBot p kind κ A c0 pstar x t u' := by
  unfold psiBot
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold stBot
  rw [botKernel_congr κ A c0 hb0 _ _ _ _ x t h]

end WaveTurbulence.VineEstS5B2
