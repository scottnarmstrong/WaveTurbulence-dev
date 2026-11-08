/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.TreeCoh

/-! # RT-GATE: the eligibility facts for D2c's root cut (`RootData`) and the one-pair cut (`PairOnly`)

From the canonical ambient `ProtAmbient p X LG` and `∀ a, LG.layer a ≤ p` (any root sign, chain in any layers):
`rtc_root_rest`, `rtc_root_inner`, `rtc_root_red`, `rtc_root_green` (`X = pair m Qr Qg inner rest`, `rest ≠ nil`) and
`rtc_pair_inner`, `rtc_pair_red`, `rtc_pair_green` (`X = cpair m Qr Qg inner`). Windows: `ℓ₀ = layerAt LG (0, [])`
(the root `𝔫_a`), `ℓb = layerAt LG (0, bPath m inner)` (`𝔫_b`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-! ### The root cut -/

section RootCut

variable {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner rest : RegChain} (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg)
include D

theorem rtc_root_mI : ∀ z : GNode LGi.garden.tree, m.c :: z.1.2 ∈ (LG.garden.tree 0).nodes := fun z => (D.ιI z).2

theorem rtc_root_mR : ∀ z : GNode LGr.garden.tree,
    rBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2 ∈ (LG.garden.tree 0).nodes := fun z => by
  have h := (D.ιR z).2
  rw [← D.sigZ]
  exact h

theorem rtc_root_mG : ∀ z : GNode LGg.garden.tree,
    gBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2 ∈ (LG.garden.tree 0).nodes := fun z => by
  have h := (D.ιG z).2
  rw [← D.sigZ]
  exact h

theorem rtc_root_mS : ∀ z : GNode LGs.garden.tree, lonePos m inner ++ z.1.2 ∈ (LG.garden.tree 0).nodes := fun z => by
  have hm : (((0 : Fin 1), lonePos m inner ++ z.1.2) : Fin 1 × TTree.Path) = (D.gd.ι₂ z).1 := by
    have hj : z.1.1 = 0 := Subsingleton.elim _ _
    simp [GlueData.ι₂, botAddr, hj, cpair_lonePath]
  have h2 := (D.gd.ι₂ z).2
  rw [← hm] at h2
  exact h2

theorem rtc_root_mb : bPath m inner ∈ (LG.garden.tree 0).nodes := TTree.branching_subset_nodes _ D.bR.2

theorem rtc_root_ml : (RegChain.pair m Qr Qg inner rest).lonePath ∈ (LG.garden.tree 0).nodes :=
  TTree.leaves_subset_nodes _ (lone_mem_leaves D.dec)

/-- **The suffix of the root cut.** -/
theorem rtc_root_rest {p : ℕ} (hA : ProtAmbient p (RegChain.pair m Qr Qg inner rest) LG)
    (hle : ∀ a, LG.layer a ≤ p) (hwf : (RegChain.pair m Qr Qg inner rest).wf = true) {q' : ℕ}
    (hq' : ∀ z : GNode LG.garden.tree, z.1.2 = (RegChain.pair m Qr Qg inner rest).lonePath → LG.layer z = q') :
    (∀ a, LGs.layer a ≤ p) ∧
    LGs.layer (GNode.root LGs.garden.tree 0) ≤ layerAt LG ((0 : Fin 1), bPath m inner) ∧
    (∀ a : GNode LGs.garden.tree, a.1.2 = rest.lonePath → LGs.layer a = q') ∧
    (LGs.incoherency (rest.treeLinks (LGs.garden.sig 0)) = 0 →
      IsCoherentTreeAt p (layerAt LG ((0 : Fin 1), bPath m inner)) q' rest LGs) := by
  obtain ⟨w', H, a, h, hcan, hC, hsa, hlay⟩ := hA
  refine ⟨fun z => (D.layS z).trans_le (layerAt_le_of_forall_layer_le hle _),
    rtc_rest_root hle D.layS (rtc_root_mS D), rtc_rest_lone D.layS (rtc_root_mS D) hq', fun h0 => ?_⟩
  exact rtc_rest_coh hcan hC hsa hlay (root_wf hwf).1 D.decS D.sigS D.layS (rtc_root_mS D) (rtc_root_mb D)
    (rtc_root_ml D) hq' h0

/-- **The interior of the root cut.** -/
theorem rtc_root_inner {p : ℕ} (hA : ProtAmbient p (RegChain.pair m Qr Qg inner rest) LG)
    (hle : ∀ a, LG.layer a ≤ p) (hwf : (RegChain.pair m Qr Qg inner rest).wf = true) :
    (∀ a, LGi.layer a ≤ p) ∧ LGi.layer (GNode.root LGi.garden.tree 0) ≤ layerAt LG ((0 : Fin 1), []) ∧
    (∀ a : GNode LGi.garden.tree, a.1.2 = inner.lonePath → LGi.layer a = layerAt LG ((0 : Fin 1), bPath m inner)) ∧
    (LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) = 0 →
      IsCoherentTreeAt p (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) inner LGi) := by
  obtain ⟨w', H, a, h, hcan, hC, hsa, hlay⟩ := hA
  refine ⟨fun z => (D.layI z).trans_le (layerAt_le_of_forall_layer_le hle _),
    rtc_inner_root hle D.layI (rtc_root_mI D), rtc_inner_lone D.layI, fun h0 => ?_⟩
  exact rtc_inner_coh hcan hC hsa hlay (root_wf hwf).2.1 D.decI D.sigI D.layI (rtc_root_mI D) (rtc_root_mb D) h0

/-- **The red side couple of the root cut.** -/
theorem rtc_root_red {p : ℕ} (hA : ProtAmbient p (RegChain.pair m Qr Qg inner rest) LG)
    (hle : ∀ a, LG.layer a ≤ p) (hwf : (RegChain.pair m Qr Qg inner rest).wf = true) :
    (∀ a, LGr.layer a ≤ p) ∧
    (∀ t : Fin 2, LGr.layer (GNode.root LGr.garden.tree t) ≤
      tc2aQR m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) t) ∧
    (LGr.incoherency Qr.links = 0 → IsCoherentCoupleAt p
      (tc2aQR m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) 0)
      (tc2aQR m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) 1)
      Qr LGr) := by
  obtain ⟨w', H, a, h, hcan, hC, hsa, hlay⟩ := hA
  refine ⟨fun z => (D.layR z).trans_le (layerAt_le_of_forall_layer_le hle _),
    rtc_red_root hle D.layR (rtc_root_mR D), fun h0 => ?_⟩
  exact rtc_red_coh hcan hC hsa hlay (root_wf hwf).2.2.1 D.decR D.layR (rtc_root_mR D) (rtc_root_mb D) h0

/-- **The green side couple of the root cut.** -/
theorem rtc_root_green {p : ℕ} (hA : ProtAmbient p (RegChain.pair m Qr Qg inner rest) LG)
    (hle : ∀ a, LG.layer a ≤ p) (hwf : (RegChain.pair m Qr Qg inner rest).wf = true) :
    (∀ a, LGg.layer a ≤ p) ∧
    (∀ t : Fin 2, LGg.layer (GNode.root LGg.garden.tree t) ≤
      tc2aQG m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) t) ∧
    (LGg.incoherency Qg.links = 0 → IsCoherentCoupleAt p
      (tc2aQG m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) 0)
      (tc2aQG m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) 1)
      Qg LGg) := by
  obtain ⟨w', H, a, h, hcan, hC, hsa, hlay⟩ := hA
  refine ⟨fun z => (D.layG z).trans_le (layerAt_le_of_forall_layer_le hle _),
    rtc_green_root hle D.layG (rtc_root_mG D), fun h0 => ?_⟩
  exact rtc_green_coh hcan hC hsa hlay (root_wf hwf).2.2.2 D.decG D.layG (rtc_root_mG D) (rtc_root_mb D) h0

end RootCut

/-! ### The one-pair cut -/

section PairCut

variable {LG LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner : RegChain} (D : PairOnly LG m Qr Qg inner LGi LGr LGg)
include D

theorem rtc_pair_mI : ∀ z : GNode LGi.garden.tree, m.c :: z.1.2 ∈ (LG.garden.tree 0).nodes :=
  fun z => (D.hp.ιi z).2

theorem rtc_pair_mR : ∀ z : GNode LGr.garden.tree,
    rBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2 ∈ (LG.garden.tree 0).nodes := fun z => (D.hp.ιr z).2

theorem rtc_pair_mG : ∀ z : GNode LGg.garden.tree,
    gBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2 ∈ (LG.garden.tree 0).nodes := fun z => (D.hp.ιg z).2

theorem rtc_pair_mb : bPath m inner ∈ (LG.garden.tree 0).nodes := TTree.branching_subset_nodes _ D.hp.bB.2

/-- **The interior of the one-pair cut.** -/
theorem rtc_pair_inner {p : ℕ} (hA : ProtAmbient p (cpair m Qr Qg inner) LG)
    (hle : ∀ a, LG.layer a ≤ p) (hwf : (cpair m Qr Qg inner).wf = true) :
    (∀ a, LGi.layer a ≤ p) ∧ LGi.layer (GNode.root LGi.garden.tree 0) ≤ layerAt LG ((0 : Fin 1), []) ∧
    (∀ a : GNode LGi.garden.tree, a.1.2 = inner.lonePath → LGi.layer a = layerAt LG ((0 : Fin 1), bPath m inner)) ∧
    (LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) = 0 →
      IsCoherentTreeAt p (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) inner LGi) := by
  obtain ⟨w', H, a, h, hcan, hC, hsa, hlay⟩ := hA
  refine ⟨fun z => (D.layI z).trans_le (layerAt_le_of_forall_layer_le hle _),
    rtc_inner_root hle D.layI (rtc_pair_mI D), rtc_inner_lone D.layI, fun h0 => ?_⟩
  exact rtc_inner_coh hcan hC hsa hlay (root_wf hwf).2.1 D.decI D.sigI D.layI (rtc_pair_mI D) (rtc_pair_mb D) h0

/-- **The red side couple of the one-pair cut.** -/
theorem rtc_pair_red {p : ℕ} (hA : ProtAmbient p (cpair m Qr Qg inner) LG)
    (hle : ∀ a, LG.layer a ≤ p) (hwf : (cpair m Qr Qg inner).wf = true) :
    (∀ a, LGr.layer a ≤ p) ∧
    (∀ t : Fin 2, LGr.layer (GNode.root LGr.garden.tree t) ≤
      tc2aQR m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) t) ∧
    (LGr.incoherency Qr.links = 0 → IsCoherentCoupleAt p
      (tc2aQR m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) 0)
      (tc2aQR m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) 1)
      Qr LGr) := by
  obtain ⟨w', H, a, h, hcan, hC, hsa, hlay⟩ := hA
  refine ⟨fun z => (D.layR z).trans_le (layerAt_le_of_forall_layer_le hle _),
    rtc_red_root hle D.layR (rtc_pair_mR D), fun h0 => ?_⟩
  exact rtc_red_coh hcan hC hsa hlay (root_wf hwf).2.2.1 D.decR D.layR (rtc_pair_mR D) (rtc_pair_mb D) h0

/-- **The green side couple of the one-pair cut.** -/
theorem rtc_pair_green {p : ℕ} (hA : ProtAmbient p (cpair m Qr Qg inner) LG)
    (hle : ∀ a, LG.layer a ≤ p) (hwf : (cpair m Qr Qg inner).wf = true) :
    (∀ a, LGg.layer a ≤ p) ∧
    (∀ t : Fin 2, LGg.layer (GNode.root LGg.garden.tree t) ≤
      tc2aQG m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) t) ∧
    (LGg.incoherency Qg.links = 0 → IsCoherentCoupleAt p
      (tc2aQG m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) 0)
      (tc2aQG m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) 1)
      Qg LGg) := by
  obtain ⟨w', H, a, h, hcan, hC, hsa, hlay⟩ := hA
  refine ⟨fun z => (D.layG z).trans_le (layerAt_le_of_forall_layer_le hle _),
    rtc_green_root hle D.layG (rtc_pair_mG D), fun h0 => ?_⟩
  exact rtc_green_coh hcan hC hsa hlay (root_wf hwf).2.2.2 D.decG D.layG (rtc_pair_mG D) (rtc_pair_mb D) h0

end PairCut

end WaveTurbulence.Flower.ProtRT
