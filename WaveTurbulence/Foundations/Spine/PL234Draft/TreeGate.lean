/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.TreeInduction

/-!
# Prop 6.1, `q > q'`, trees: the error estimate and the non-dominant codes

**`tree_err_gt`**: for a coherent embedded tree code with parent layer `q > q'` (lone layer `q'`), on
`ℬ = {(t, s) ∈ [q,q+1]×[q',q'+1], s < t}`,
`‖K*_𝒯 − 𝒜_𝒯‖_{𝔛^{η,0,0}(ℬ)} ≤ C_f (C_f δ)^n L^{-(γ₁-√η)} ∏ B_leaf`, from the single-layer estimates (`Oracle`):

* root in layer `q`, a single block: the single-layer estimate itself (TARGET prooflayer1-2 has one factor);
* root in layer `q`, further blocks: the top factor (`tree_top_bounds`, `restr_top`) times the lower bounds of the
  rest (`tree_lower_bounds`);
* root below `q`: the kernel does not depend on `t ≥ q`, and the lower bounds with `π = []`.

**`coherentTree_eq_zero`**: a non-dominant tree code has a non-dominant slice, hence vanishing leading term.
-/

@[expose] public section

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

theorem continuous_treeLeaves_snd {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d)
    {X : RegChain} (hX : X.DecodesTree LG.garden) (c : ℝ) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|) :
    Continuous fun ts : Fin 2 → ℝ => treeLeaves L γ δ LG H c (ts 1) k := by
  have hc := continuous_treeLeaves_time L γ δ LG H
    (noFlowerParent_of_noFlower (not_flower_of_decodesTree hX)) (card_lone_le_of_decodesTree hX) k hF
  have hg : Continuous (fun ts : Fin 2 → ℝ => (![c, ts 1] : Fin 2 → ℝ)) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_const
    · exact continuous_apply 1
  exact (hc.comp hg).congr fun _ => rfl

theorem continuous_lowAppT_snd {d : ℕ} (δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d) (q' : ℕ)
    (π : Path) (X : RegChain) (k : Mom d) :
    Continuous fun ts : Fin 2 → ℝ => lowAppT δ LG H q' π X (ts 1) k := by
  unfold lowAppT lowBotT
  exact continuous_const.mul (continuous_LeafApp_tree_comp _ _ _ _ _ _ _ _ continuous_const
    (continuous_apply 1))

theorem timeBoxGt_shift_unit (q q' : ℕ) :
    ∀ ts ∈ timeBoxGt (q : ℝ) q', ts + ![-(q : ℝ), -(q' : ℝ)] ∈ (Layered.unitBox : Set (Fin 2 → ℝ)) :=
  fun ts hts => timeBox_shift_unit q q' ts hts.1

/-- The layers of a single-block tree: the lone leaf in layer `q'`, every other node in layer `u`. -/
theorem layer_single_block {LG : LayeredGarden 1} {X : RegChain} {q' u : ℕ} (hX : X.DecodesTree LG.garden)
    (hlone : layerAt LG ((0 : Fin 1), X.lonePath) = q')
    (hXlay : ∀ z ∈ chainNodesSet X (LG.garden.sig 0) ((0 : Fin 1), []), layerAt LG z = u) :
    ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else u := by
  intro a
  rw [← layerAt_node]
  have ha : a.1 = ((0 : Fin 1), a.1.2) := by
    obtain ⟨⟨j, p⟩, _⟩ := a
    fin_cases j
    rfl
  split_ifs with hl
  · rw [ha, hl]
    exact hlone
  · rcases addrExt_mem_chainNodes hX ((0 : Fin 1), []) a with h | h
    · have e : addrExt ((0 : Fin 1), ([] : Path)) a.1.2 = a.1 := by rw [ha]; simp [addrExt]
      rw [e] at h
      exact hXlay _ h
    · exact absurd h hl

section Err

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1) (hη2 : P.η ≤ 1 - P.η) (hδ : 0 ≤ P.δ)
  (hΛ0 : 0 ≤ gainΛ P) (hΛ1 : gainΛ P ≤ 1)

include O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1

omit hd hL hη1 hη2 hΛ1 in
/-- **A single block in layer `q`**: the single-layer estimate itself. -/
theorem tree_err_single {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (F : TreeCohFacts LG X q' q)
    (hTAX : TopAll LG q ((0 : Fin 1), []) X)
    (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    R00 P.η (timeBoxGt q q') Set.univ (fun ts k =>
        treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (Cf P.η C * (Cf P.η C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) := by
  set ζ := LG.garden.sig 0 with hζ
  have hC0 : 0 ≤ C := by linarith
  have hK0 : 0 ≤ Ktr P.η := Ktr_nonneg _
  have hK1 : 1 ≤ Ktr P.η := one_le_Ktr hη0
  have hβ0 : 0 ≤ leafSizeProduct LG Bd := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hts1 : ∀ ts ∈ timeBoxGt (q : ℝ) q', ts 1 ≤ (q' : ℝ) + 1 := fun ts hts => hts.1.2.2
  have hq1 : (q' : ℝ) + 1 ≤ q := by exact_mod_cast hqq
  have hEmb := ChainEmb.of_decodesTree F.dec
  have hXlay : ∀ z ∈ chainNodesSet X ζ ((0 : Fin 1), []), layerAt LG z = q :=
    chainNodes_layer_of_topAll hEmb F.pl hTAX
  have hlay := layer_single_block F.dec F.lone hXlay
  obtain ⟨hE, -, -⟩ := O.tree q q' n hqp hqq.le hnN X F.wf hsize LG F.dec hlay H Bd hH
  have hprof : LeafApp.sliceProfiles LG H ((0 : Fin 1), []) q X = H := by
    funext z
    unfold LeafApp.sliceProfiles
    rw [sliceAddress_of_topAll LG q X _ _ hTAX]
    obtain ⟨j, p⟩ := z
    fin_cases j
    simp [addrExt]
  have heq : ∀ ts ∈ timeBoxGt (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)),
      treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k =
      treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.tree P.δ q H X ζ (ts 0) (ts 1) k := by
    intro ts hts k _
    have hsq : ts 1 ≤ (q : ℝ) := (hts1 ts hts).trans hq1
    rw [coherentTree_gt_eq P.δ LG H X hqq]
    rw [Finset.prod_eq_one fun r hr => by
      unfold sliceFactorT
      rw [chainSlice_of_topNe LG r X _ (TopAll.topNe LG (by simp only [Finset.mem_Ioo] at hr; omega) _ _ hTAX)]
      exact LeafApp.tree_nil _ _ _ _ _ _ _, one_mul]
    unfold lowBotT
    rw [chainSlice_of_topNe LG q' X _ (TopAll.topNe LG (by omega) _ _ hTAX), LeafApp.tree_nil, mul_one,
      chainSlice_of_topAll LG q X _ hTAX, hprof, ← LeafApp.tree_lower_eq P.δ q H X ζ (ts 0) hsq k]
  refine (Layered.restr_congr P.η (timeBoxGt (q : ℝ) q') Set.univ heq).trans_le ?_
  refine (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 P.η (timeBoxGt (q : ℝ) q') Set.univ
    (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
      LeafApp.tree P.δ q H X ζ (ts 0) (ts 1) k)).symm.le.trans ?_
  refine (XNorm00Restr_le_XNormRestr _ _ _ _ _ _).trans (hE.trans (ENNReal.ofReal_le_ofReal ?_))
  have h0 : 0 ≤ C * (C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd := by positivity
  calc C * (C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd
      ≤ Ktr P.η * (C * (C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) := le_mul_of_one_le_left h0 hK1
    _ ≤ _ := (absorb_base_err hC hδ hΛ0 hβ0 hK0 n).trans (absorb_final' hη0 hC hδ hΛ0 hβ0 n)

/-- **The top block in layer `q`, and the rest.** -/
theorem tree_err_top {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (F : TreeCohFacts LG X q' q)
    (htop : layerAt LG ((0 : Fin 1), []) = q) (hXn : X ≠ .nil)
    (hDn : dropLayer LG ((0 : Fin 1), []) q X ≠ .nil)
    (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    R00 P.η (timeBoxGt q q') Set.univ (fun ts k =>
        treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (Cf P.η C * (Cf P.η C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) := by
  set ζ := LG.garden.sig 0 with hζ
  have hC0 : 0 ≤ C := by linarith
  have hK0 : 0 ≤ Ktr P.η := Ktr_nonneg _
  have hβ0 : 0 ≤ leafSizeProduct LG Bd := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hHe : (fun z => H (botAddr [] z)) = H := funext fun z => by rw [botAddr_nil_tree]
  have hBe : (fun z => Bd (botAddr [] z)) = Bd := funext fun z => by rw [botAddr_nil_tree]
  have S₀ : TreeLowState LG H Bd [] X LG := TreeLowState.root F.dec hH
  have hT := timeBoxGt_shift_unit q q'
  have hEmb := ChainEmb.of_decodesTree F.dec
  set B := takeLayer LG ((0 : Fin 1), []) q X with hBdef
  set D := dropLayer LG ((0 : Fin 1), []) q X with hDdef
  have hXe : appendChain B D = X := appendChain_take_drop LG _ q X
  have hTA : TopAll LG q ((0 : Fin 1), []) B := topAll_takeLayer LG q _ X
  have hEmbBD : ChainEmb LG.garden (appendChain B D) ζ ((0 : Fin 1), []) .leaf := by rw [hXe]; exact hEmb
  have hPLBD : ChainPairLayers LG (appendChain B D) ζ ((0 : Fin 1), []) := by rw [hXe]; exact F.pl
  have hSMBD : SpineMono LG ((0 : Fin 1), []) (appendChain B D) := by rw [hXe]; exact F.sm
  have hBlay : ∀ z ∈ chainNodesSet B ζ ((0 : Fin 1), []), layerAt LG z = q :=
    chainNodes_layer_of_topAll (chainEmb_append_left hEmbBD) (chainPairLayers_append_left LG B D ζ _ hPLBD) hTA
  have hsl : SourceApp.chainSlice LG ((0 : Fin 1), []) q X = B :=
    chainSlice_eq_take LG _ X F.sm fun _ => by rw [htop]
  set r'' := layerAt LG ((0 : Fin 1), B.lonePath) with hr''
  have hnode : (addrExt ((0 : Fin 1), ([] : Path)) B.lonePath).2 ∈
      (LG.garden.tree (addrExt ((0 : Fin 1), ([] : Path)) B.lonePath).1).nodes := by
    have ht : (LG.garden.tree ((0 : Fin 1), ([] : Path)).1).subtreeAt ((0 : Fin 1), ([] : Path)).2 =
        B.plug ζ (D.plug ζ .leaf) := by
      rw [hEmbBD.tree, appendChain_plug]
    exact (node_iff_of_subtree hEmb.node ht B.lonePath).1.mpr (lonePath_mem_plug B ζ _)
  have hle : r'' ≤ q := by
    rw [← htop]
    exact layerAt_le_of_under LG hEmb.node hnode (under_ext _ _)
  have hlt : r'' < q := by
    refine lt_of_le_of_ne hle ?_
    have := layer_drop_ne LG q X ((0 : Fin 1), []) hDn
    simpa [addrExt] using this
  have hlow'' : q' ≤ r'' := by
    obtain ⟨m', Qr', Qg', inner', rest', hD'⟩ :
        ∃ m' Qr' Qg' inner' rest', D = .pair m' Qr' Qg' inner' rest' := by
      cases hDc : D with
      | nil => exact absurd hDc hDn
      | pair m' Qr' Qg' inner' rest' => exact ⟨m', Qr', Qg', inner', rest', rfl⟩
    apply F.low
    rw [← hXe]
    apply chainNodesSet_append_right B D ζ ((0 : Fin 1), [])
    rw [hD']
    exact root_mem_chainNodesSet _ _ _ _ _ _ _
  have hSMD : SpineMono LG ((0 : Fin 1), B.lonePath) D := spineMono_append_right LG B D _ hSMBD
  have hBlay' : ∀ z ∈ chainNodesSet (takeLayer LG ((0 : Fin 1), []) q X) (LG.garden.sig 0) (0, []),
      layerAt LG z = q := hBlay
  obtain ⟨G₁, LG'', hdec₁, hsig₁, hlay₁, hctrl₁, S'', hβ, hK⟩ :=
    tree_block_step S₀ P.L P.γ P.δ hd hL F.wf hDn hlt hBlay'
  simp only [List.nil_append] at hlay₁ S'' hβ hK
  rw [hHe] at hK
  have hβe : leafSizeProduct LG Bd =
      leafSizeProduct G₁ (fun z => Bd (LeafApp.sliceAddress LG (0, []) q X z.2)) *
        leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) := by
    have h' := hβ
    rw [hBe] at h'
    exact h'
  -- sizes
  have hwfBD : (appendChain B D).wf = true := by rw [hXe]; exact F.wf
  rw [appendChain_wf, Bool.and_eq_true] at hwfBD
  have hsz : X.size = B.size + D.size := by rw [← hXe, appendChain_size]
  obtain ⟨nB, hnB⟩ := size_even_chain B
  obtain ⟨m₂, hm₂⟩ := size_even_chain D
  have hBne : B ≠ .nil := by
    have := takeLayer_ne_nil LG X ((0 : Fin 1), []) hXn
    rw [htop] at this
    exact this
  have hB2 := two_le_size_of_ne_nil B hBne
  have hBsize : B.size = 2 * nB := by omega
  have hsz₂ : D.size = 2 * m₂ := by omega
  have hnn' : n = nB + m₂ := by omega
  have hnB1 : 1 ≤ nB := by omega
  set HT := LeafApp.sliceProfiles LG H ((0 : Fin 1), []) q X with hHT
  set BT : (Fin 1 × Path) → NNReal := fun z => Bd (LeafApp.sliceAddress LG ((0 : Fin 1), []) q X z.2)
    with hBT
  have hβT0 : 0 ≤ leafSizeProduct G₁ BT := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  obtain ⟨hET, hJT, hMT⟩ :=
    O.tree q r'' nB hqp hlt.le (by omega) B hwfBD.1 hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
  have hT₁ : ∀ ts ∈ timeBoxGt (q : ℝ) q', ts + ![-(q : ℝ), -(q' : ℝ)] ∈ (Layered.unitBox : Set (Fin 2 → ℝ)) := hT
  obtain ⟨hX, hY⟩ := tree_top_bounds P B G₁ HT hd hL hη0 hη2 hδ hlt hBsize hdec₁ hlay₁ BT hctrl₁
    (by positivity) (by positivity) (by positivity) hET hJT hMT (timeBoxGt (q : ℝ) q') (-(q' : ℝ)) hT₁
  rw [hsig₁] at hX hY
  -- the lower bounds of the rest
  obtain ⟨hE₂, hA₂⟩ := tree_lower_bounds P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 H Bd F hqq.le hqp
    (timeBoxGt (q : ℝ) q') (-(q : ℝ)) hT m₂ B D LG'' hXe.symm hsz₂ (by omega) S''
  have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) :=
    Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hE₂' : R00 P.η (timeBoxGt (q : ℝ) q') Set.univ (fun ts k => (1 : ℂ) *
      (treeLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) ((r'' : ℝ) + 1) (ts 1) k -
        lowAppT P.δ LG H q' B.lonePath D (ts 1) k)) ≤
      ENNReal.ofReal (3 ^ (m₂ + 1) * (Ktr P.η * C ^ 2) * (2 * C ^ 4) ^ m₂ * P.δ ^ m₂ * gainΛ P *
        leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z))) :=
    (restr_one_mul_eq P.η (timeBoxGt (q : ℝ) q') Set.univ (fun ts k =>
      treeLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) ((r'' : ℝ) + 1) (ts 1) k -
        lowAppT P.δ LG H q' B.lonePath D (ts 1) k)).trans_le hE₂
  have hA₂' : R00 P.η (timeBoxGt (q : ℝ) q') Set.univ (fun ts k => (1 : ℂ) *
      lowAppT P.δ LG H q' B.lonePath D (ts 1) k) ≤
      ENNReal.ofReal ((Ktr P.η * C ^ 2) * (2 * C ^ 4) ^ m₂ * P.δ ^ m₂ *
        leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z))) :=
    (restr_one_mul_eq P.η (timeBoxGt (q : ℝ) q') Set.univ (fun ts k =>
      lowAppT P.δ LG H q' B.lonePath D (ts 1) k)).trans_le hA₂
  have hcK : ∀ k : Mom P.d, Continuous fun ts : Fin 2 → ℝ =>
      treeLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) ((r'' : ℝ) + 1) (ts 1) k :=
    fun k => continuous_treeLeaves_snd P.L P.γ P.δ LG'' _ S''.dec _ k (S''.ctrl.summable_coset hd hL k)
  have hcA : ∀ k : Mom P.d, Continuous fun ts : Fin 2 → ℝ =>
      lowAppT P.δ LG H q' B.lonePath D (ts 1) k := fun k =>
    continuous_lowAppT_snd P.δ LG H q' B.lonePath D k
  have hc₁ : ∀ k ∈ (Set.univ : Set (Mom P.d)), Continuous fun ts : Fin 2 → ℝ => (fun _ => (1 : ℂ)) k *
      (treeLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) ((r'' : ℝ) + 1) (ts 1) k -
        lowAppT P.δ LG H q' B.lonePath D (ts 1) k) := fun k _ =>
    continuous_const.mul ((hcK k).sub (hcA k))
  have hc₂ : ∀ k ∈ (Set.univ : Set (Mom P.d)), Continuous fun ts : Fin 2 → ℝ => (fun _ => (1 : ℂ)) k *
      lowAppT P.δ LG H q' B.lonePath D (ts 1) k := fun k _ => continuous_const.mul (hcA k)
  have htopb := Layered.restr_top hη0 (timeBoxGt (q : ℝ) q') (fun ts hts => mem_closure_interior_timeBoxGt hts)
    (Set.univ : Set (Mom P.d)) (fun _ => (1 : ℂ))
    (fun ts k => treeLeaves P.L P.γ P.δ G₁ HT (ts 0) q k)
    (fun ts k => LeafApp.tree P.δ q HT B ζ (ts 0) q k)
    (fun ts k => treeLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) ((r'' : ℝ) + 1) (ts 1) k)
    (fun ts k => lowAppT P.δ LG H q' B.lonePath D (ts 1) k) hc₁ hc₂
    (by positivity) (by positivity) (by positivity) (by positivity) hX hY hE₂' hA₂'
  have heq : ∀ ts ∈ timeBoxGt (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)),
      treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k =
      (fun _ => (1 : ℂ)) k * ((fun ts k => treeLeaves P.L P.γ P.δ G₁ HT (ts 0) q k) ts k *
        (fun ts k => treeLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z))
          ((r'' : ℝ) + 1) (ts 1) k) ts k -
        (fun ts k => LeafApp.tree P.δ q HT B ζ (ts 0) q k) ts k *
        (fun ts k => lowAppT P.δ LG H q' B.lonePath D (ts 1) k) ts k) := by
    intro ts hts k _
    have ht0 : (q : ℝ) ≤ ts 0 := hts.1.1.1
    have hr1 : (r'' : ℝ) + 1 ≤ ts 0 := by
      have : (r'' : ℝ) + 1 ≤ q := by exact_mod_cast hlt
      linarith
    have hrest := lowRestT_eq P.δ LG H [] X (u := q) hSMD hqq hlow'' hlt (ts 1) k
    simp only [List.nil_append] at hrest
    have hA : LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k =
        LeafApp.tree P.δ q HT B ζ (ts 0) q k * lowAppT P.δ LG H q' B.lonePath D (ts 1) k := by
      rw [coherentTree_gt_eq P.δ LG H X hqq, hsl, ← hrest]
      ring
    rw [hK (ts 0) (ts 1) k hr1, hA, one_mul]
  refine (Layered.restr_congr P.η (timeBoxGt (q : ℝ) q') Set.univ heq).trans_le
    (htopb.1.trans (ENNReal.ofReal_le_ofReal ?_))
  -- constants
  have h2η : (2 : ℝ) ^ P.η ≤ 2 := by
    calc (2 : ℝ) ^ P.η ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hη1
      _ = 2 := Real.rpow_one 2
  have habs := absorb_step (δ := P.δ) (Λ := gainΛ P) (D₀ := 2 * C ^ 4) (M₀ := Ktr P.η * C ^ 2) (m₂ := m₂)
    (n := nB) (β₁ := Ktr P.η * leafSizeProduct G₁ BT) (by positivity) (by positivity) hδ hΛ0 hΛ1
    (by positivity) hβ₂0 (by positivity) (by positivity)
    (ε := Ktr P.η * (C * (C * P.δ) ^ nB * gainΛ P * leafSizeProduct G₁ BT))
    (α := P.δ ^ nB * 2 ^ nB * (C * C ^ nB * leafSizeProduct G₁ BT) * (Ktr P.η * (C * C ^ nB)))
    (by nlinarith [absorb_tree_err hC hδ hΛ0 hβT0 hnB1]) (by
      have : P.δ ^ nB * 2 ^ nB * (C * C ^ nB * leafSizeProduct G₁ BT) * (Ktr P.η * (C * C ^ nB)) =
          Ktr P.η * (P.δ ^ nB * 2 ^ nB * (C * C ^ nB) * (C * C ^ nB * leafSizeProduct G₁ BT)) := by ring
      rw [this]
      nlinarith [absorb_tree_app hC hδ hβT0 hnB1]) le_rfl le_rfl (by positivity) (by positivity) hnB1
  rw [← hnn'] at habs
  set W := 3 ^ (n + 1) * (Ktr P.η * C ^ 2) * (2 * C ^ 4) ^ n * P.δ ^ n * gainΛ P * leafSizeProduct LG Bd
    with hW
  have hW0 : 0 ≤ W := by positivity
  calc 2 ^ P.η * (Ktr P.η * (C * (C * P.δ) ^ nB * gainΛ P * leafSizeProduct G₁ BT) *
        (3 ^ (m₂ + 1) * (Ktr P.η * C ^ 2) * (2 * C ^ 4) ^ m₂ * P.δ ^ m₂ * gainΛ P *
            leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) +
          Ktr P.η * C ^ 2 * (2 * C ^ 4) ^ m₂ * P.δ ^ m₂ *
            leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z))) +
        P.δ ^ nB * 2 ^ nB * (C * C ^ nB * leafSizeProduct G₁ BT) * (Ktr P.η * (C * C ^ nB)) *
          (3 ^ (m₂ + 1) * (Ktr P.η * C ^ 2) * (2 * C ^ 4) ^ m₂ * P.δ ^ m₂ * gainΛ P *
            leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z))))
      ≤ 2 * (Ktr P.η * W) := by
        apply mul_le_mul h2η _ (by positivity) (by norm_num)
        refine habs.1.trans_eq ?_
        rw [hW, hβe]
        ring
    _ ≤ Cf P.η C * (Cf P.η C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd := by
        have := absorb_final hη0 hC hδ hΛ0 hβ0 n
        rw [hW]
        linarith

/-- **The root below `q`**: the kernel does not depend on `t ≥ q`; the lower bounds with `π = []`. -/
theorem tree_err_low {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (F : TreeCohFacts LG X q' q)
    (hr₁lt : layerAt LG ((0 : Fin 1), []) < q)
    (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    R00 P.η (timeBoxGt q q') Set.univ (fun ts k =>
        treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (Cf P.η C * (Cf P.η C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) := by
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b :=
    noFlowerParent_of_noFlower (not_flower_of_decodesTree F.dec)
  have hβ0 : 0 ≤ leafSizeProduct LG Bd := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hHe : (fun z => H (botAddr [] z)) = H := funext fun z => by rw [botAddr_nil_tree]
  have hBe : (fun z => Bd (botAddr [] z)) = Bd := funext fun z => by rw [botAddr_nil_tree]
  have S₀ : TreeLowState LG H Bd [] X LG := TreeLowState.root F.dec hH
  have hT := timeBoxGt_shift_unit q q'
  set r₁ := layerAt LG ((0 : Fin 1), []) with hr₁
  have hroot : X ≠ .nil → ((0 : Fin 1), ([] : Path)) ∈ chainNodesSet X (LG.garden.sig 0) ((0 : Fin 1), []) :=
    fun hXn => by
      cases X with
      | nil => exact absurd rfl hXn
      | pair m' Qr' Qg' inner' rest' => exact root_mem_chainNodesSet _ _ _ _ _ _ _
  have hlowr₁ : q' ≤ r₁ := by
    by_cases hXn : X = .nil
    · have h := F.lone
      rw [hXn] at h
      have : r₁ = q' := by simpa [RegChain.lonePath] using h
      rw [this]
    · exact F.low _ (hroot hXn)
  obtain ⟨hE, -⟩ := tree_lower_bounds P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 H Bd F hqq.le hqp
    (timeBoxGt (q : ℝ) q') (-(q : ℝ)) hT n .nil X LG rfl hsize hnN S₀
  have heq : ∀ ts ∈ timeBoxGt (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)),
      treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k =
      treeLeaves P.L P.γ P.δ LG (fun z => H (botAddr RegChain.nil.lonePath z))
        ((layerAt LG ((0 : Fin 1), RegChain.nil.lonePath) : ℝ) + 1) (ts 1) k -
        lowAppT P.δ LG H q' RegChain.nil.lonePath X (ts 1) k := by
    intro ts hts k _
    have ht0 : (q : ℝ) ≤ ts 0 := hts.1.1.1
    have hq1' : (r₁ : ℝ) + 1 ≤ q := by exact_mod_cast hr₁lt
    have hK : treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k =
        treeLeaves P.L P.γ P.δ LG H ((r₁ : ℝ) + 1) (ts 1) k :=
      treeLeaves_upper_eq P.L P.γ P.δ LG H hfl (ts 1) k fun b => by
        have hroot0 : ([] : Path) ∈ (LG.garden.tree 0).nodes := TTree.nil_mem_nodes _
        have hu : Under ((0 : Fin 1), ([] : Path)) b.toNode.1 :=
          ⟨Subsingleton.elim _ _, List.nil_prefix⟩
        have hl := layerAt_le_of_under LG hroot0 b.toNode.2 hu
        rw [layerAt_node] at hl
        have : (LG.layer b.toNode : ℝ) ≤ r₁ := by exact_mod_cast hl
        exact ⟨by linarith, by linarith⟩
    have hslq : SourceApp.chainSlice LG ((0 : Fin 1), []) q X = .nil :=
      chainSlice_eq_nil LG _ X F.sm fun _ => hr₁lt
    have hA : LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k =
        lowAppT P.δ LG H q' [] X (ts 1) k := by
      rw [coherentTree_gt_eq P.δ LG H X hqq, hslq, LeafApp.tree_nil, mul_one]
      unfold lowAppT
      congr 1
      rw [← hr₁, Ioo_eq_Ico_succ, Ioo_eq_Ico_succ,
        ← prod_Ico_consecutive _ (show q' + 1 ≤ r₁ + 1 by omega) (show r₁ + 1 ≤ q by omega)]
      rw [Finset.prod_eq_one (s := Ico (r₁ + 1) q) fun r hr => by
        unfold sliceFactorT
        rw [chainSlice_eq_nil LG _ X F.sm fun _ => by simp only [Finset.mem_Ico] at hr; omega]
        exact LeafApp.tree_nil _ _ _ _ _ _ _, mul_one]
    simp only [RegChain.lonePath]
    rw [hK, hA, hHe]
  refine (Layered.restr_congr P.η (timeBoxGt (q : ℝ) q') Set.univ heq).trans_le (hE.trans ?_)
  simp only [RegChain.lonePath]
  rw [hBe]
  exact ENNReal.ofReal_le_ofReal (absorb_final' hη0 hC hδ hΛ0 hβ0 n)

/-- **Prop 6.1, trees, `q > q'`: the error estimate** (TARGET L1097–1111, prooflayer1-2). -/
theorem tree_err_gt {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (hcoh : IsCoherentTreeAt p q q' X LG)
    (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    R00 P.η (timeBoxGt q q') Set.univ (fun ts k =>
        treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (Cf P.η C * (Cf P.η C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) := by
  have F := treeCohFacts_of_coherent hcoh
  have hnil : X = .nil → layerAt LG ((0 : Fin 1), []) = q' := fun hXn => by
    have h := F.lone
    rw [hXn] at h
    simpa [RegChain.lonePath] using h
  have hr₁q : layerAt LG ((0 : Fin 1), []) ≤ q := by
    by_cases hXn : X = .nil
    · rw [hnil hXn]; exact hqq.le
    · apply F.high
      cases X with
      | nil => exact absurd rfl hXn
      | pair m' Qr' Qg' inner' rest' => exact root_mem_chainNodesSet _ _ _ _ _ _ _
  by_cases htop : layerAt LG ((0 : Fin 1), []) = q
  · have hXn : X ≠ .nil := fun h => by have := hnil h; omega
    by_cases hDn : dropLayer LG ((0 : Fin 1), []) q X = .nil
    · have hXe := appendChain_take_drop LG ((0 : Fin 1), []) q X
      rw [hDn, appendChain_nil_right] at hXe
      have hTAX : TopAll LG q ((0 : Fin 1), []) X := by
        have := topAll_takeLayer LG q ((0 : Fin 1), []) X
        rwa [hXe] at this
      exact tree_err_single P O hC hη0 hδ hΛ0 hqq hqp hnN X hsize LG F hTAX H Bd hH
    · exact tree_err_top P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 hqq hqp hnN X hsize LG F htop hXn hDn H Bd hH
  · exact tree_err_low P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 hqq hqp hnN X hsize LG F
      (lt_of_le_of_ne hr₁q htop) H Bd hH

end Err

/-- **Non-dominant coherent trees have vanishing explicit leading terms** (`q' ≤ q`). -/
theorem coherentTree_eq_zero {d : ℕ} (δ : ℝ) {p q q' : ℕ} (hqq : q' ≤ q) {X : RegChain}
    {LG : LayeredGarden 1} (hcoh : IsCoherentTreeAt p q q' X LG) (hdom : X.dominant = false)
    (H : LeafProfiles 1 d) (t s : ℝ) (k : Mom d) : LeafApp.coherentTree δ LG H X q q' t s k = 0 := by
  by_cases heq : q = q'
  · simp only [LeafApp.coherentTree, heq, ↓reduceIte]
    exact LeafApp.tree_not_dominant _ _ _ _ _ hdom _ _ _
  have hlt : q' < q := lt_of_le_of_ne hqq (Ne.symm heq)
  have F := treeCohFacts_of_coherent hcoh
  rw [coherentTree_gt_eq δ LG H X hlt]
  obtain ⟨z, hz, hzd⟩ := chainSlice_not_dominant LG X (LG.garden.sig 0) ((0 : Fin 1), []) hdom
  have hlow := F.low z hz
  have hup := F.high z hz
  rcases eq_or_lt_of_le hlow with hr | hr
  · -- the bottom slice
    unfold lowBotT
    rw [← hr] at hzd
    rw [LeafApp.tree_not_dominant _ _ _ _ _ hzd, mul_zero]
  rcases eq_or_lt_of_le hup with hr' | hr'
  · -- the top slice
    rw [hr'] at hzd
    rw [LeafApp.tree_not_dominant _ _ _ _ _ hzd, mul_zero, zero_mul]
  · -- a middle slice
    rw [Finset.prod_eq_zero (i := layerAt LG z) (Finset.mem_Ioo.mpr ⟨hr, hr'⟩) (by
      unfold sliceFactorT
      exact LeafApp.tree_not_dominant _ _ _ _ _ hzd _ _ _), zero_mul, zero_mul]

end WaveTurbulence.PL234
