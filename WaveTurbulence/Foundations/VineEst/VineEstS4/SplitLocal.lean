/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitTime
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLStarConsumption

/-! # Locality of the S-part `spart` in the clock (V5 Step 4b, P2.3 Fubini form) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory
variable {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem parentClock_congr_S (hS : G.molecule.IsBlock S a b) (RS : CLRegionData G S a b) {top : ℝ}
    {u u' : GBranch G.tree → ℝ} (h : ∀ v ∈ S, u v = u' v) {x : GNode G.tree}
    (hx : x ∈ clRealizationNodes G S) (hne : x ≠ a.toNode) : parentClock top u x = parentClock top u' x := by
  obtain ⟨hn, hp⟩ := cl_realization_parent hS RS x hx hne
  rw [parentClock_nonroot _ _ x hn, parentClock_nonroot _ _ x hn]
  exact h _ hp

theorem DomS_congr (hS : G.molecule.IsBlock S a b) (RS : CLRegionData G S a b) (lay : GBranch G.tree → ℕ)
    {u u' : GBranch G.tree → ℝ} (h : ∀ v ∈ S, u v = u' v) : DomS lay S a u ↔ DomS lay S a u' := by
  have ha : u a = u' a := h a hS.2.1
  have key : ∀ v ∈ S.erase a, parentClock (u a) u v.toNode = parentClock (u' a) u' v.toNode := by
    intro v hv
    obtain ⟨hva, hvS⟩ := Finset.mem_erase.mp hv
    rw [ha]
    exact parentClock_congr_S hS RS h ((branch_mem_clRealizationNodes v).mpr hvS)
      (fun e => hva (Mole.branch_toNode_injective e))
  unfold DomS
  constructor
  · intro H v hv
    have hvS := (Finset.mem_erase.mp hv).2
    rw [← h v hvS, ← key v hv]
    exact H v hv
  · intro H v hv
    have hvS := (Finset.mem_erase.mp hv).2
    rw [h v hvS, key v hv]
    exact H v hv

section Part
variable (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)

theorem starProd_congr_S (hS : G.molecule.IsBlock S a b) (RS : CLRegionData G S a b) {top : ℝ}
    (x : GNode G.tree → (Fin d → ℤ)) {u u' : GBranch G.tree → ℝ} (h : ∀ v ∈ S, u v = u' v) :
    starProd D hG L γ δ F layer hLayer base S a top x u = starProd D hG L γ δ F layer hLayer base S a top x u' := by
  unfold starProd
  refine congrArg₂ (· * ·) ?_ ?_
  · refine Finset.prod_congr rfl (fun p hp => ?_)
    have hr := clRegionalPair_realization hG p hp
    rw [parentClock_congr_S hS RS h hr.1 (Mole.branch_toNode_ne_leaf a _).symm,
      parentClock_congr_S hS RS h hr.2 (Mole.branch_toNode_ne_leaf a _).symm]
  · refine Finset.prod_congr rfl (fun v hv => ?_)
    obtain ⟨hva, hvS⟩ := Finset.mem_erase.mp hv
    rw [parentClock_congr_S hS RS h ((branch_mem_clRealizationNodes v).mpr hvS)
      (fun e => hva (Mole.branch_toNode_injective e)), h v hvS]

/-- `spart` reads the clock only on `S`. -/
theorem spart_congr (hS : G.molecule.IsBlock S a b) (RS : CLRegionData G S a b)
    (x : GNode G.tree → (Fin d → ℤ)) {u u' : GBranch G.tree → ℝ} (h : ∀ v ∈ S, u v = u' v) :
    spart D hG L γ δ F layer hLayer base S a b x u = spart D hG L γ δ F layer hLayer base S a b x u' := by
  have ha : u a = u' a := h a hS.2.1
  unfold spart
  have h1 := DomS_congr hS RS (fun v => layer (D.coreBranch hG v).toNode) h
  have h2 := starProd_congr_S D hG L γ δ F layer hLayer base hS RS (top := u' a) x h
  have h3 : starProd D hG L γ δ F layer hLayer base S a (u a) x u =
      starProd D hG L γ δ F layer hLayer base S a (u' a) x u' := by
    rw [ha]; exact h2
  rw [h3, clRegionalPhase_congr (S.erase b) L γ δ (k := cosetDecoration G L base x) (u := u) (u' := u')
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun v hv => h v (Finset.mem_of_mem_erase hv))]
  by_cases hd : DomS (fun v => layer (D.coreBranch hG v).toNode) S a u
  · simp [hd, h1.mp hd]
  · have hd' : ¬ DomS (fun v => layer (D.coreBranch hG v).toNode) S a u' := fun h' => hd (h1.mpr h')
    simp [hd, hd']

end Part

end WaveTurbulence.VineEstS4
