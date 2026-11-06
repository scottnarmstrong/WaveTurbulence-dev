/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.InductionAux

/-!
# Prop 6.1, `q > q'`, couples: the induction over the blocks of the `+` chain

* `gainΛ`: the single-layer gain `L^{-(γ₁ - √η)}` of B2.1;
* `Oracle`: the single-layer estimates of B2.1 (leafwise) at fixed parameters with one constant `C`;
* `CohFacts`: the coherence facts of a coherent type-2 couple whose `-` side is in layer `q'` (LAYERREG,
  transported to the decoded carrier);
* **`lower_bounds`**: for every lower state (a suffix `X` of the `+` chain, below `(0, π)`), on any target box
  mapped into the unit box by `t ↦ t − (·, q')`, the weighted error and leading term of the lower couple satisfy
  `≤ 3^{m+1} M₀ D₀^m δ^m Λ β` and `≤ M₀ D₀^m δ^m β`, with `M₀ = K_tr C²`, `D₀ = 2C⁴`, `β = ∏ B_leaf`.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-- The single-layer gain `L^{-(γ₁ - √η)}`. -/
noncomputable def gainΛ (P : WTParams) : ℝ := P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ))

/-- **The single-layer estimates of B2.1**, leafwise, at fixed parameters, with one constant `C`. -/
structure Oracle (P : WTParams) (p : ℕ) (C : ℝ) : Prop where
  tree : ∀ (r q'' n : ℕ), r ≤ p → q'' ≤ r → n ≤ P.N (p + 1) ^ 4 → ∀ X : RegChain, X.wf = true →
    X.size = 2 * n → ∀ LG : LayeredGarden 1, X.DecodesTree LG.garden →
    (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r) →
    ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × Path) → NNReal), LeafwiseControlled LG H B →
    XNormRestr P.η (30 * P.d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (C * (C * P.δ) ^ n * gainΛ P * leafSizeProduct LG B) ∧
    (X.dominant = true → XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt r q'') Set.univ
      (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (C * C ^ n)) ∧
    (X.dominant = true → ∀ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)),
      SNormR (30 * P.d) 0 (LeafApp.chainNstar H Z X (LG.garden.sig 0) (0, [])) ≤
        ENNReal.ofReal (C * C ^ n * leafSizeProduct LG B))
  couple : ∀ (r n : ℕ), r ≤ p → n ≤ P.N (p + 1) ^ 4 → ∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n →
    ∀ LG : LayeredGarden 2, Q.Decodes LG.garden → (∀ a, LG.layer a = r) →
    ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × Path) → NNReal), LeafwiseControlled LG H B →
    XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox r r) Set.univ
      (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        LeafApp.couple P.δ r H Q (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (C * (C * P.δ) ^ n * gainΛ P * leafSizeProduct LG B) ∧
    (Q.dominant = true → XNorm00Restr (V := Unit) (1 - P.η) (timeBox r r) Set.univ
      (fun ts _ => (Q.JB r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (C * C ^ n)) ∧
    (Q.dominant = true → ∀ Z ∈ specialSets Q.links,
      SNormR (30 * P.d) (30 * P.d) (LeafApp.cplMstar H Z Q (0, []) (1, [])) ≤
        ENNReal.ofReal (C * C ^ n * leafSizeProduct LG B))

/-- **Coherence facts** of a coherent type-2 couple whose `-` side lies in layer `q'`, on the decoded carrier. -/
structure CohFacts (LG : LayeredGarden 2) (Xp Xm : RegChain) (Qlp : RegCpl) (q' p : ℕ) : Prop where
  wf : (RegCpl.type2 Xp Xm Qlp).wf = true
  emb : ChainEmb LG.garden Xp 1 ((0 : Fin 2), []) Qlp.trees.1
  pl : ChainPairLayers LG Xp 1 ((0 : Fin 2), [])
  sm : SpineMono LG ((0 : Fin 2), []) Xp
  low : ∀ z ∈ chainNodesSet Xp 1 ((0 : Fin 2), []), q' ≤ layerAt LG z
  high : ∀ z ∈ chainNodesSet Xp 1 ((0 : Fin 2), []), layerAt LG z ≤ p
  minus : ∀ z ∈ chainNodesSet Xm (-1) ((1 : Fin 2), []), layerAt LG z = q'
  lp : ∀ z ∈ cplNodes Qlp ((0 : Fin 2), Xp.lonePath) ((1 : Fin 2), Xm.lonePath), layerAt LG z = q'
  qp : q' ≤ p

theorem root_mem_chainNodesSet {w : ℕ} (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (ζ : ℤˣ)
    (a : Fin w × Path) : a ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a := by
  unfold chainNodesSet pairEndpoints
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [List.mem_toFinset]
  simp [RegChain.linksAt]

section Suffix

variable {LG : LayeredGarden 2} {Xp Xm : RegChain} {Qlp : RegCpl} {q' p : ℕ}
  (F : CohFacts LG Xp Xm Qlp q' p) {R X : RegChain} (hXp : Xp = appendChain R X)
include F hXp

theorem CohFacts.emb_suffix : ChainEmb LG.garden X 1 ((0 : Fin 2), R.lonePath) Qlp.trees.1 := by
  have h := F.emb
  rw [hXp] at h
  exact chainEmb_append_right h

theorem CohFacts.pl_suffix : ChainPairLayers LG X 1 ((0 : Fin 2), R.lonePath) := by
  have h := F.pl
  rw [hXp] at h
  exact chainPairLayers_append_right LG R X 1 _ h

theorem CohFacts.sm_suffix : SpineMono LG ((0 : Fin 2), R.lonePath) X := by
  have h := F.sm
  rw [hXp] at h
  exact spineMono_append_right LG R X _ h

omit F in
theorem CohFacts.sub_suffix {z : Fin 2 × Path} (hz : z ∈ chainNodesSet X 1 ((0 : Fin 2), R.lonePath)) :
    z ∈ chainNodesSet Xp 1 ((0 : Fin 2), []) := by
  rw [hXp]
  exact chainNodesSet_append_right R X 1 _ hz

theorem CohFacts.lone_suffix :
    layerAt LG (addrExt ((0 : Fin 2), R.lonePath) X.lonePath) = q' := by
  have he : addrExt ((0 : Fin 2), R.lonePath) X.lonePath = ((0 : Fin 2), Xp.lonePath) := by
    rw [hXp, appendChain_lonePath]
    rfl
  rw [he]
  exact F.lp _ (left_mem_cplNodes _ _ _)

theorem CohFacts.wf_suffix : X.wf = true ∧ Xm.wf = true ∧ Qlp.wf = true ∧ Qlp.isType2 = false := by
  have h := F.wf
  rw [hXp] at h
  simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true', appendChain_wf] at h
  exact ⟨h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2⟩

end Suffix

section Base

variable (P : WTParams) {p : ℕ} {C : ℝ} {LG : LayeredGarden 2} {H : LeafProfiles 2 P.d}
  {Bd : (Fin 2 × Path) → NNReal} {Xp Xm : RegChain} {Qlp : RegCpl} {q' : ℕ}

/-- In the base case every node of the lower couple lies in layer `q'`. -/
theorem base_layers (F : CohFacts LG Xp Xm Qlp q' p) {R X : RegChain} (hXp : Xp = appendChain R X)
    {LG' : LayeredGarden 2} (S : LowState LG H Bd Xm Qlp R.lonePath X LG')
    (hbase : X = .nil ∨ layerAt LG ((0 : Fin 2), R.lonePath) ≤ q') :
    layerAt LG ((0 : Fin 2), R.lonePath) = q' ∧ TopAll LG q' ((0 : Fin 2), R.lonePath) X ∧
      ∀ a : GNode LG'.garden.tree, LG'.layer a = q' := by
  set π := R.lonePath
  have hEmb := F.emb_suffix hXp
  have hlone := F.lone_suffix hXp
  -- the layer at the root of the suffix
  have hu : layerAt LG ((0 : Fin 2), π) = q' := by
    rcases hbase with hn | hle
    · subst hn
      simpa [RegChain.lonePath, addrExt] using hlone
    · cases X with
      | nil => simpa [RegChain.lonePath, addrExt] using hlone
      | pair m Qr Qg inner rest =>
        exact le_antisymm hle (F.low _ (CohFacts.sub_suffix hXp (root_mem_chainNodesSet _ _ _ _ _ _ _)))
  -- all chain nodes of the suffix in layer `q'`
  have hX : ∀ z ∈ chainNodesSet X 1 ((0 : Fin 2), π), layerAt LG z = q' := by
    intro z hz
    refine le_antisymm ?_ (F.low z (CohFacts.sub_suffix hXp hz))
    rw [← hu]
    exact layerAt_le_of_under LG hEmb.node (hEmb.mem_nodes hz)
      ((chain_endpoints_region X 1 _ z hz).1)
  have hTA : TopAll LG q' ((0 : Fin 2), π) X := topAll_of_chainNodes LG q' X 1 _ hX
  refine ⟨hu, hTA, fun a => ?_⟩
  rw [← layerAt_node, S.lay]
  have ha := addrExt_mem_cplNodes S.dec ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) a
  have hae : addrExt (if a.1.1 = 0 then ((0 : Fin 2), ([] : Path)) else ((1 : Fin 2), ([] : Path))) a.1.2 =
      a.1 := by
    obtain ⟨⟨j, q⟩, _⟩ := a
    fin_cases j <;> simp [addrExt]
  rw [hae] at ha
  have hm := cplNodes_map (SourceApp.closeCouple X Xm Qlp) (botAddr π) (botAddr_hom π)
    ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path))
  have h0 : botAddr π ((0 : Fin 2), ([] : Path)) = ((0 : Fin 2), π) := by simp [botAddr]
  have h1 : botAddr π ((1 : Fin 2), ([] : Path)) = ((1 : Fin 2), ([] : Path)) := by simp [botAddr]
  rw [h0, h1] at hm
  have hb : botAddr π a.1 ∈ cplNodes (SourceApp.closeCouple X Xm Qlp) ((0 : Fin 2), π) ((1 : Fin 2), []) := by
    rw [hm]
    exact Finset.mem_image_of_mem _ ha
  unfold SourceApp.closeCouple at hb
  split_ifs at hb with hnil
  · simp only [Bool.and_eq_true] at hnil
    have hXn : X = .nil := by cases X <;> simp_all [RegChain.isNil]
    have hmn : Xm = .nil := by cases Xm <;> simp_all [RegChain.isNil]
    apply F.lp
    have e1 : ((0 : Fin 2), π) = ((0 : Fin 2), Xp.lonePath) := by
      rw [hXp, hXn, appendChain_lonePath]
      simp [RegChain.lonePath, π]
    have e2 : ((1 : Fin 2), ([] : Path)) = ((1 : Fin 2), Xm.lonePath) := by
      rw [hmn]
      rfl
    rw [← e1, ← e2]
    exact hb
  · rcases mem_cplNodes_type2.mp hb with hz | hz | hz
    · exact hX _ hz
    · exact F.minus _ hz
    · apply F.lp
      have e1 : addrExt ((0 : Fin 2), π) X.lonePath = ((0 : Fin 2), Xp.lonePath) := by
        rw [hXp, appendChain_lonePath]
        rfl
      rw [e1] at hz
      exact hz

end Base

section Induction

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1) (hη2 : P.η ≤ 1 - P.η) (hδ : 0 ≤ P.δ)
  (hΛ0 : 0 ≤ gainΛ P) (hΛ1 : gainΛ P ≤ 1)
  {LG : LayeredGarden 2} (H : LeafProfiles 2 P.d) (Bd : (Fin 2 × Path) → NNReal)
  {Xp Xm : RegChain} {Qlp : RegCpl} {q' : ℕ} (F : CohFacts LG Xp Xm Qlp q' p)
  (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox)

/-- The base identification: a single-layer lower couple. -/
theorem lowApp_base {R X : RegChain} (hu : layerAt LG ((0 : Fin 2), R.lonePath) = q')
    (hTA : TopAll LG q' ((0 : Fin 2), R.lonePath) X) (s : ℝ) (k : Mom P.d) :
    lowApp P.δ LG H Xm Qlp q' R.lonePath X s k =
      LeafApp.couple P.δ q' (fun z => H (botAddr R.lonePath z)) (SourceApp.closeCouple X Xm Qlp)
        (q' + 1) s k := by
  unfold lowApp lowSlices lowBot
  rw [hu, chainSlice_of_topAll LG q' X _ hTA]
  have h0 : Finset.Ioo q' (q' + 1) = ∅ := by
    ext x
    simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
    omega
  rw [h0, Finset.prod_empty, one_mul]
  congr 1
  funext z
  unfold botProf
  split_ifs with hz
  · rw [sliceAddress_of_topAll LG q' X _ _ hTA]
    obtain ⟨j, q⟩ := z
    simp only at hz
    subst hz
    simp [botAddr, addrExt]
  · obtain ⟨j, q⟩ := z
    simp only at hz
    simp [botAddr, hz]

include O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 F hT'

/-- **The lower bounds**, by induction over the blocks of the `+` chain. -/
theorem lower_bounds : ∀ (m : ℕ) (R X : RegChain) (LG' : LayeredGarden 2), Xp = appendChain R X →
    (SourceApp.closeCouple X Xm Qlp).size = 2 * m → m ≤ P.N (p + 1) ^ 4 →
    LowState LG H Bd Xm Qlp R.lonePath X LG' →
    R00 P.η T' Set.univ (fun ts k => wt k *
        (coupleLeaves P.L P.γ P.δ LG' (fun z => H (botAddr R.lonePath z))
          ((layerAt LG ((0 : Fin 2), R.lonePath) : ℝ) + 1) (ts 1) k -
          lowApp P.δ LG H Xm Qlp q' R.lonePath X (ts 1) k)) ≤
        ENNReal.ofReal (3 ^ (m + 1) * (Ktr P.η * C ^ 2) * (2 * C ^ 4) ^ m * P.δ ^ m * gainΛ P *
          leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z))) ∧
      R00 P.η T' Set.univ (fun ts k => wt k * lowApp P.δ LG H Xm Qlp q' R.lonePath X (ts 1) k) ≤
        ENNReal.ofReal ((Ktr P.η * C ^ 2) * (2 * C ^ 4) ^ m * P.δ ^ m *
          leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z))) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro R X LG' hXp hsize hmN S
  have hC0 : 0 ≤ C := by linarith
  have hK0 : 0 ≤ Ktr P.η := Ktr_nonneg _
  have hβ0 : 0 ≤ leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) :=
    Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  obtain ⟨hXwf, hmwf, hlwf, hlt2⟩ := F.wf_suffix hXp
  by_cases hbase : X = .nil ∨ layerAt LG ((0 : Fin 2), R.lonePath) ≤ q'
  · -- the base: a single-layer couple in layer `q'`
    obtain ⟨hu, hTA, hlayq⟩ := base_layers P F hXp S hbase
    have hwfc : (SourceApp.closeCouple X Xm Qlp).wf = true := closeCouple_wf hXwf hmwf hlwf hlt2
    obtain ⟨hE, hJ, hM⟩ := O.couple q' m F.qp hmN _ hwfc hsize LG' S.dec hlayq _ _ S.ctrl
    obtain ⟨hEb, hAb⟩ := couple_bottom_bounds P (SourceApp.closeCouple X Xm Qlp) LG'
      (fun z => H (botAddr R.lonePath z)) hd hL hη0 hη2 hδ hsize S.dec _ S.ctrl
      (by positivity : 0 ≤ C * C ^ m * leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)))
      hE hJ hM T' b₀ hT'
    have heq : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)), wt k *
        (coupleLeaves P.L P.γ P.δ LG' (fun z => H (botAddr R.lonePath z))
          ((layerAt LG ((0 : Fin 2), R.lonePath) : ℝ) + 1) (ts 1) k -
          lowApp P.δ LG H Xm Qlp q' R.lonePath X (ts 1) k) =
        wt k * (coupleLeaves P.L P.γ P.δ LG' (fun z => H (botAddr R.lonePath z)) (q' + 1) (ts 1) k -
          LeafApp.couple P.δ q' (fun z => H (botAddr R.lonePath z)) (SourceApp.closeCouple X Xm Qlp)
            (q' + 1) (ts 1) k) := fun ts _ k _ => by
      rw [lowApp_base P H hu hTA, hu]
    have heqA : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        wt k * lowApp P.δ LG H Xm Qlp q' R.lonePath X (ts 1) k =
        wt k * LeafApp.couple P.δ q' (fun z => H (botAddr R.lonePath z)) (SourceApp.closeCouple X Xm Qlp)
            (q' + 1) (ts 1) k := fun ts _ k _ => by
      rw [lowApp_base P H hu hTA]
    constructor
    · refine (Layered.restr_congr P.η T' Set.univ heq).trans_le (hEb.trans ?_)
      exact ENNReal.ofReal_le_ofReal (absorb_base_err hC hδ hΛ0 hβ0 hK0 m)
    · refine (Layered.restr_congr P.η T' Set.univ heqA).trans_le (hAb.trans ?_)
      apply ENNReal.ofReal_le_ofReal
      calc P.δ ^ m * 2 ^ m * (C * C ^ m * leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z))) *
            (Ktr P.η * (C * C ^ m))
          ≤ (Ktr P.η * C ^ 2) * (2 * C ^ 4) ^ m * P.δ ^ m *
            leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) :=
            absorb_base_app hC hδ hβ0 hK0 m
        _ = _ := rfl
  · push_neg at hbase
    obtain ⟨hXn, hqu⟩ := hbase
    set π := R.lonePath with hπ
    set u := layerAt LG ((0 : Fin 2), π) with hu
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
    -- the next layer
    have hnode : (addrExt ((0 : Fin 2), π) B.lonePath).2 ∈
        (LG.garden.tree (addrExt ((0 : Fin 2), π) B.lonePath).1).nodes := by
      have ht : (LG.garden.tree ((0 : Fin 2), π).1).subtreeAt ((0 : Fin 2), π).2 =
          B.plug 1 (D.plug 1 Qlp.trees.1) := by
        rw [hEmbBD.tree, appendChain_plug]
      exact (node_iff_of_subtree hEmb.node ht B.lonePath).1.mpr (lonePath_mem_plug B 1 _)
    have hle : layerAt LG ((0 : Fin 2), π ++ B.lonePath) ≤ u :=
      layerAt_le_of_under LG hEmb.node hnode (under_ext _ _)
    have hlone := F.lone_suffix hXp
    have hloneB : D = .nil → layerAt LG ((0 : Fin 2), π ++ B.lonePath) = q' := fun hDn => by
      have e : ((0 : Fin 2), π ++ B.lonePath) = addrExt ((0 : Fin 2), π) X.lonePath := by
        rw [← hXe, appendChain_lonePath, hDn]
        simp [RegChain.lonePath, addrExt]
      rw [e]
      exact hlone
    have hlt : layerAt LG ((0 : Fin 2), π ++ B.lonePath) < u := by
      by_cases hDn : D = .nil
      · rw [hloneB hDn]; exact hqu
      · exact lt_of_le_of_ne hle (layer_drop_ne LG u X _ hDn)
    have hlow'' : q' ≤ layerAt LG ((0 : Fin 2), π ++ B.lonePath) := by
      by_cases hDn : D = .nil
      · rw [hloneB hDn]
      · obtain ⟨m', Qr', Qg', inner', rest', hD'⟩ : ∃ m' Qr' Qg' inner' rest', D = .pair m' Qr' Qg' inner' rest' := by
          cases hDc : D with
          | nil => exact absurd hDc hDn
          | pair m' Qr' Qg' inner' rest' => exact ⟨m', Qr', Qg', inner', rest', rfl⟩
        apply F.low
        apply CohFacts.sub_suffix hXp
        rw [← hXe]
        apply chainNodesSet_append_right B D 1 ((0 : Fin 2), π)
        rw [hD']
        exact root_mem_chainNodesSet _ _ _ _ _ _ _
    have hwf2 : (RegCpl.type2 X Xm Qlp).wf = true := by
      have hXnil : X.isNil = false := by cases X <;> simp_all [RegChain.isNil]
      simp [RegCpl.wf, hXwf, hmwf, hlwf, hlt2, hXnil]
    obtain ⟨G₁, LG'', hdec₁, hsig₁, hlay₁, hctrl₁, S'', hβ, hK⟩ :=
      couple_block_step S P.L P.γ P.δ hd hL hXn hwf2 hu.symm hlt hBlay
    -- sizes
    have hsz : (SourceApp.closeCouple X Xm Qlp).size = B.size + (SourceApp.closeCouple D Xm Qlp).size := by
      rw [← hXe, closeCouple_size, closeCouple_size, appendChain_size]
      ring
    obtain ⟨nB, hnB⟩ := size_even_chain B
    obtain ⟨m₂, hm₂⟩ := size_even_cpl (SourceApp.closeCouple D Xm Qlp)
    have hB2 := two_le_size_of_ne_nil B (takeLayer_ne_nil LG X _ hXn)
    have hBsize : B.size = 2 * nB := by omega
    have hsz₂ : (SourceApp.closeCouple D Xm Qlp).size = 2 * m₂ := by omega
    have hmm : m = nB + m₂ := by omega
    have hnB1 : 1 ≤ nB := by omega
    -- the tree slice
    have hup : u ≤ p := by
      apply F.high
      apply CohFacts.sub_suffix hXp
      cases hXc : X with
      | nil => exact absurd hXc hXn
      | pair m' Qr' Qg' inner' rest' => exact root_mem_chainNodesSet _ _ _ _ _ _ _
    have hBwf : B.wf = true := (wf_split (hXe ▸ hwf2 : (RegCpl.type2 (appendChain B D) Xm Qlp).wf = true)).1
    set HT := LeafApp.sliceProfiles LG H ((0 : Fin 2), π) u X with hHT
    set BT : (Fin 1 × Path) → NNReal := fun z => Bd (LeafApp.sliceAddress LG ((0 : Fin 2), π) u X z.2) with hBT
    have hβT0 : 0 ≤ leafSizeProduct G₁ BT := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    obtain ⟨hET, hJT, hMT⟩ := O.tree u _ nB hup hlt.le (by omega) B hBwf hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
    have hmid := fun k => tree_middle_bounds P B G₁ HT hd hL hη0 hη1 hδ hlt hBsize hdec₁ hlay₁ BT hctrl₁
      (by positivity) (by positivity) (by positivity) hET hJT hMT k
    rw [hsig₁] at hmid
    have hsl : SourceApp.chainSlice LG ((0 : Fin 2), π) u X = B :=
      chainSlice_eq_take LG _ X hSM fun _ => le_refl _
    have ha_eq : ∀ k, sliceFactor P.δ LG H π X u k = LeafApp.tree P.δ u HT B 1 ((u : ℝ) + 1) u k := by
      intro k
      unfold sliceFactor
      rw [hsl]
    -- the induction hypothesis on the rest
    have hXp' : Xp = appendChain (appendChain R B) D := by rw [appendChain_assoc, hXe]; exact hXp
    have hlp : (appendChain R B).lonePath = π ++ B.lonePath := appendChain_lonePath R B
    have S''' : LowState LG H Bd Xm Qlp (appendChain R B).lonePath D LG'' := by rw [hlp]; exact S''
    obtain ⟨hE₂, hA₂⟩ := ih m₂ (by omega) (appendChain R B) D LG'' hXp' hsz₂ (by omega) S'''
    rw [hlp] at hE₂ hA₂
    have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ B.lonePath) z)) :=
      Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hstep := Layered.restr_step P.η T' (Set.univ : Set (Mom P.d)) wt
      (fun k => treeLeaves P.L P.γ P.δ G₁ HT ((u : ℝ) + 1) u k)
      (fun k => LeafApp.tree P.δ u HT B 1 ((u : ℝ) + 1) u k)
      (fun ts k => coupleLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr (π ++ B.lonePath) z))
        ((layerAt LG ((0 : Fin 2), π ++ B.lonePath) : ℝ) + 1) (ts 1) k)
      (fun ts k => lowApp P.δ LG H Xm Qlp q' (π ++ B.lonePath) D (ts 1) k)
      (by positivity) (by positivity) (by positivity) (by positivity)
      (fun k _ => (hmid k).1) (fun k _ => (hmid k).2) hE₂ hA₂
    have hsplit := lowApp_split P.δ LG H Xm Qlp π X hu.symm hqu hXn hSM
      (spineMono_append_right LG B D _ hSMBD) hlow'' hlt
    have heq : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)), wt k *
        (coupleLeaves P.L P.γ P.δ LG' (fun z => H (botAddr π z)) ((u : ℝ) + 1) (ts 1) k -
          lowApp P.δ LG H Xm Qlp q' π X (ts 1) k) =
        wt k * ((fun k => treeLeaves P.L P.γ P.δ G₁ HT ((u : ℝ) + 1) u k) k *
          (fun ts k => coupleLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr (π ++ B.lonePath) z))
            ((layerAt LG ((0 : Fin 2), π ++ B.lonePath) : ℝ) + 1) (ts 1) k) ts k -
          (fun k => LeafApp.tree P.δ u HT B 1 ((u : ℝ) + 1) u k) k *
          (fun ts k => lowApp P.δ LG H Xm Qlp q' (π ++ B.lonePath) D (ts 1) k) ts k) := fun ts _ k _ => by
      rw [hK ((u : ℝ) + 1) (ts 1) k (by exact_mod_cast Nat.succ_le_succ hlt.le), hsplit (ts 1) k, ha_eq k]
    have heqA : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        wt k * lowApp P.δ LG H Xm Qlp q' π X (ts 1) k =
        wt k * ((fun k => LeafApp.tree P.δ u HT B 1 ((u : ℝ) + 1) u k) k *
          (fun ts k => lowApp P.δ LG H Xm Qlp q' (π ++ B.lonePath) D (ts 1) k) ts k) := fun ts _ k _ => by
      rw [hsplit (ts 1) k, ha_eq k]
    have habs := absorb_step (D₀ := 2 * C ^ 4) (M₀ := Ktr P.η * C ^ 2) (m₂ := m₂) (by positivity) (by positivity) hδ
      hΛ0 hΛ1 hβT0 hβ₂0 (by positivity) (by positivity)
      (absorb_tree_err hC hδ hΛ0 hβT0 hnB1) (absorb_tree_app hC hδ hβT0 hnB1) le_rfl le_rfl
      (by positivity) (by positivity) hnB1
    rw [← hmm, ← hβ] at habs
    constructor
    · exact (Layered.restr_congr P.η T' Set.univ heq).trans_le
        (hstep.1.trans (ENNReal.ofReal_le_ofReal habs.1))
    · exact (Layered.restr_congr P.η T' Set.univ heqA).trans_le
        (hstep.2.trans (ENNReal.ofReal_le_ofReal habs.2))

end Induction

end WaveTurbulence.PL234
