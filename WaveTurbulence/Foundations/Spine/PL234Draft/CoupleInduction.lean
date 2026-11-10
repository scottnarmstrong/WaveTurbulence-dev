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

end Induction

end WaveTurbulence.PL234
