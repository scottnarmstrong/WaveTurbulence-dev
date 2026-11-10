/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.CoupleTop

/-!
# Prop 6.1, `q > q'`, couples: the error estimate

**`couple_err_gt`**: for a coherent embedded couple code with parent layers `q > q'`, on `ℬ = [q,q+1]×[q',q'+1]`,
`‖⟨k⟩^{30d} (K*_𝒬 − 𝒜_𝒬)‖_{𝔛^{η,0,0}(ℬ)} ≤ C_f (C_f δ)^n L^{-(γ₁-√η)} ∏ B_leaf`, `C_f = 6 K_tr² C⁴`, from the
single-layer estimates (`Oracle`):

* trivial and type-1 codes lie in layer `q'` (LAYERREG): the bottom estimate (`couple_bottom_bounds`);
* type-2 codes whose top block is below `q`: the lower bounds (`lower_bounds`) with `π = []`;
* type-2 codes with a top block in layer `q`: the top factor (`tree_top_bounds`, product estimate `restr_top`)
  times the lower bounds of the rest.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-- The nodes of a coherent couple carrier, in the ambient garden. -/
theorem layer_of_coherent {p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2}
    (h : IsCoherentCoupleAt p q q' Q LG) :
    ∃ (w : ℕ) (HH : LayeredGarden w) (a b : Fin w × Path), IsCanonGC (p + 1) HH ∧ Embeds HH.garden Q a b ∧
      CohOn HH (Q.linksAt a b) ∧ parAt HH p a = q ∧ parAt HH p b = q' ∧
      ∀ z : GNode LG.garden.tree, rootEmb a b z.1 ∈ cplNodes Q a b ∧ LG.layer z = layerAt HH (rootEmb a b z.1) := by
  obtain ⟨hwf, hQ, w, HH, a, b, hcan, hE, -, -, hcoh, hpa, hpb, hlay⟩ := h
  refine ⟨w, HH, a, b, hcan, hE, hcoh, hpa, hpb, fun z => ⟨?_, ?_⟩⟩
  · have ha := addrExt_mem_cplNodes hQ ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) z
    have hae : addrExt (if z.1.1 = 0 then ((0 : Fin 2), ([] : Path)) else ((1 : Fin 2), ([] : Path))) z.1.2 =
        z.1 := by
      obtain ⟨⟨j, q⟩, _⟩ := z
      fin_cases j <;> simp [addrExt]
    rw [hae] at ha
    have hm := cplNodes_map Q (rootEmb a b) (rootEmb_hom a b) ((0 : Fin 2), []) ((1 : Fin 2), [])
    rw [rootEmb_zero, rootEmb_one] at hm
    rw [hm]
    exact Finset.mem_image_of_mem _ ha
  · rw [← layerAt_node, layerAt_rootEmb hQ hE hlay]

/-- **Trivial and type-1 coherent couples lie in layer `q'`** when `q' ≤ q`. -/
theorem layers_type1 {p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2} (hqq : q' ≤ q)
    (h : IsCoherentCoupleAt p q q' Q LG) (ht : Q.isType2 = false) : ∀ z : GNode LG.garden.tree, LG.layer z = q' := by
  have hwf := h.1
  obtain ⟨w, HH, a, b, hcan, hE, hcoh, hpa, hpb, hz⟩ := layer_of_coherent h
  have hL := layerreg1_type1 hcan.2.2 hcan.1 hwf hE hcoh ht
  intro z
  rw [(hz z).2, hL _ (hz z).1, hpa, hpb, min_eq_right hqq]

/-- The root of the `+` tree of a coherent type-2 couple is in a layer `≤ q`. -/
theorem root_le_type2 {p q q' : ℕ} {Xp Xm : RegChain} {Qlp : RegCpl} {LG : LayeredGarden 2} (hqq : q' ≤ q)
    (h : IsCoherentCoupleAt p q q' (.type2 Xp Xm Qlp) LG) : layerAt LG ((0 : Fin 2), []) ≤ q := by
  have hwf := h.1
  have hQ := h.2.1
  obtain ⟨w, HH, a, b, hcan, hE, hcoh, hpa, hpb, hz⟩ := layer_of_coherent h
  have hnode : ([] : Path) ∈ (LG.garden.tree 0).nodes := TTree.nil_mem_nodes _
  have h0 := (hz ⟨((0 : Fin 2), []), hnode⟩).2
  rw [layerAt_node LG ⟨((0 : Fin 2), []), hnode⟩, h0, rootEmb_zero]
  rw [← hpa]
  exact layerAt_le_parAt HH p hcan.2.2.1 hE.nodeA

/-- **The facts of the top block** of a nonempty suffix of the `+` chain whose top layer `u` exceeds `q'`. -/
theorem block_facts {LG : LayeredGarden 2} {Xp Xm : RegChain} {Qlp : RegCpl} {q' p : ℕ}
    (F : CohFacts LG Xp Xm Qlp q' p) {R X : RegChain} (hXp : Xp = appendChain R X) (hXn : X ≠ .nil)
    {u : ℕ} (hu : layerAt LG ((0 : Fin 2), R.lonePath) = u) (hqu : q' < u) :
    (∀ z ∈ chainNodesSet (takeLayer LG ((0 : Fin 2), R.lonePath) u X) 1 ((0 : Fin 2), R.lonePath),
        layerAt LG z = u) ∧
      layerAt LG ((0 : Fin 2), R.lonePath ++ (takeLayer LG ((0 : Fin 2), R.lonePath) u X).lonePath) < u ∧
      q' ≤ layerAt LG ((0 : Fin 2), R.lonePath ++ (takeLayer LG ((0 : Fin 2), R.lonePath) u X).lonePath) ∧
      (RegCpl.type2 X Xm Qlp).wf = true ∧
      SpineMono LG ((0 : Fin 2), R.lonePath ++ (takeLayer LG ((0 : Fin 2), R.lonePath) u X).lonePath)
        (dropLayer LG ((0 : Fin 2), R.lonePath) u X) := by
  set π := R.lonePath with hπ
  obtain ⟨hXwf, hmwf, hlwf, hlt2⟩ := F.wf_suffix hXp
  have hEmb := F.emb_suffix hXp
  have hPL := F.pl_suffix hXp
  have hSM := F.sm_suffix hXp
  set B := takeLayer LG ((0 : Fin 2), π) u X with hBdef
  set D := dropLayer LG ((0 : Fin 2), π) u X with hDdef
  have hXe : appendChain B D = X := appendChain_take_drop LG _ u X
  have hTA : TopAll LG u ((0 : Fin 2), π) B := topAll_takeLayer LG u _ X
  have hEmbBD : ChainEmb LG.garden (appendChain B D) 1 ((0 : Fin 2), π) Qlp.trees.1 := by
    rw [hXe]; exact hEmb
  have hPLBD : ChainPairLayers LG (appendChain B D) 1 ((0 : Fin 2), π) := by rw [hXe]; exact hPL
  have hSMBD : SpineMono LG ((0 : Fin 2), π) (appendChain B D) := by rw [hXe]; exact hSM
  have hBlay : ∀ z ∈ chainNodesSet B 1 ((0 : Fin 2), π), layerAt LG z = u :=
    chainNodes_layer_of_topAll (chainEmb_append_left hEmbBD)
      (chainPairLayers_append_left LG B D 1 _ hPLBD) hTA
  have hnode : (addrExt ((0 : Fin 2), π) B.lonePath).2 ∈
      (LG.garden.tree (addrExt ((0 : Fin 2), π) B.lonePath).1).nodes := by
    have ht : (LG.garden.tree ((0 : Fin 2), π).1).subtreeAt ((0 : Fin 2), π).2 =
        B.plug 1 (D.plug 1 Qlp.trees.1) := by
      rw [hEmbBD.tree, appendChain_plug]
    exact (node_iff_of_subtree hEmb.node ht B.lonePath).1.mpr (lonePath_mem_plug B 1 _)
  have hle : layerAt LG ((0 : Fin 2), π ++ B.lonePath) ≤ u := by
    rw [← hu]
    exact layerAt_le_of_under LG hEmb.node hnode (under_ext _ _)
  have hlone := F.lone_suffix hXp
  have hloneB : D = .nil → layerAt LG ((0 : Fin 2), π ++ B.lonePath) = q' := fun hDn => by
    have e : ((0 : Fin 2), π ++ B.lonePath) = addrExt ((0 : Fin 2), π) X.lonePath := by
      rw [← hXe, appendChain_lonePath, hDn]
      simp [RegChain.lonePath, addrExt]
    rw [e]
    exact hlone
  refine ⟨hBlay, ?_, ?_, ?_, spineMono_append_right LG B D _ hSMBD⟩
  · by_cases hDn : D = .nil
    · rw [hloneB hDn]; exact hqu
    · exact lt_of_le_of_ne hle (layer_drop_ne LG u X _ hDn)
  · by_cases hDn : D = .nil
    · rw [hloneB hDn]
    · obtain ⟨m', Qr', Qg', inner', rest', hD'⟩ :
          ∃ m' Qr' Qg' inner' rest', D = .pair m' Qr' Qg' inner' rest' := by
        cases hDc : D with
        | nil => exact absurd hDc hDn
        | pair m' Qr' Qg' inner' rest' => exact ⟨m', Qr', Qg', inner', rest', rfl⟩
      apply F.low
      apply CohFacts.sub_suffix hXp
      rw [← hXe]
      apply chainNodesSet_append_right B D 1 ((0 : Fin 2), π)
      rw [hD']
      exact root_mem_chainNodesSet _ _ _ _ _ _ _
  · have hXnil : X.isNil = false := by cases X <;> simp_all [RegChain.isNil]
    simp [RegCpl.wf, hXwf, hmwf, hlwf, hlt2, hXnil]

theorem continuous_coupleLeaves_snd {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 2) (H : LeafProfiles 2 d)
    (hplain : LG.garden.IsPlain) (c : ℝ) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|) :
    Continuous fun ts : Fin 2 → ℝ => coupleLeaves L γ δ LG H c (ts 1) k := by
  have hc := continuous_coupleLeaves_time L γ δ H LG hplain k hF
  have hg : Continuous (fun ts : Fin 2 → ℝ => (![c, ts 1] : Fin 2 → ℝ)) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_const
    · exact continuous_apply 1
  exact (hc.comp hg).congr fun _ => rfl

theorem continuous_lowApp_snd {d : ℕ} (δ : ℝ) (LG : LayeredGarden 2) (H : LeafProfiles 2 d) (Xm : RegChain)
    (Qlp : RegCpl) (q' : ℕ) (π : Path) (X : RegChain) (k : Mom d) :
    Continuous fun ts : Fin 2 → ℝ => lowApp δ LG H Xm Qlp q' π X (ts 1) k := by
  unfold lowApp lowBot
  exact continuous_const.mul (continuous_LeafApp_couple_comp _ _ _ _ _ _ _ continuous_const
    (continuous_apply 1))

section Err

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1) (hη2 : P.η ≤ 1 - P.η) (hδ : 0 ≤ P.δ)
  (hΛ0 : 0 ≤ gainΛ P) (hΛ1 : gainΛ P ≤ 1)

theorem timeBox_shift_unit (q q' : ℕ) :
    ∀ ts ∈ timeBox (q : ℝ) q', ts + ![-(q : ℝ), -(q' : ℝ)] ∈ (Layered.unitBox : Set (Fin 2 → ℝ)) := by
  intro ts hts i
  obtain ⟨h0, h1⟩ := hts
  have e0 : (ts + ![-(q : ℝ), -(q' : ℝ)]) 0 = ts 0 - q := by simp; ring
  have e1 : (ts + ![-(q : ℝ), -(q' : ℝ)]) 1 = ts 1 - q' := by simp; ring
  fin_cases i
  · show (ts + ![-(q : ℝ), -(q' : ℝ)]) 0 ∈ Icc (0 : ℝ) 1
    rw [e0]
    constructor <;> linarith [h0.1, h0.2]
  · show (ts + ![-(q : ℝ), -(q' : ℝ)]) 1 ∈ Icc (0 : ℝ) 1
    rw [e1]
    constructor <;> linarith [h1.1, h1.2]

include O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1

end Err

end WaveTurbulence.PL234
