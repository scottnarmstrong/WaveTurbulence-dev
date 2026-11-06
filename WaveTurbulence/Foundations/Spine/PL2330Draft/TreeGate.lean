/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.TreeInd

/-!
# Prop 6.1 at `Λ₁ = 30d`, `q > q'`, trees: the error estimate (PL23-30D)

**`tree_err_gt30`**: for a coherent embedded tree code with parent layers `q > q'`, on `ℬ = {(t,s) ∈ [q,q+1]×[q',q'+1] : s < t}`,
`‖K*_𝒯 − 𝒜_𝒯‖_{𝔛^{η,30d,0}(ℬ)} ≤ C_f (C_f δ)^n L^{-(γ₁-√η)} ∏ B_leaf`, from the single-layer estimates (`Oracle`):
single block in layer `q`, top block with a nonempty rest (`restr_top30`), root below `q` (`tree_lower_bounds30`).
-/

@[expose] public section

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL2330

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.Reg WaveTurbulence.Links

section Err

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1) (hη2 : P.η ≤ 1 - P.η) (hδ : 0 ≤ P.δ)
  (hΛ0 : 0 ≤ gainΛ P) (hΛ1 : gainΛ P ≤ 1)

include O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1

omit hL hη1 hη2 hΛ1 in
/-- **A single block in layer `q`**: the single-layer estimate itself. -/
theorem tree_err_single30 {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (F : TreeCohFacts LG X q' q)
    (hTAX : TopAll LG q ((0 : Fin 1), []) X)
    (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    rN P.η (30 * P.d) 0 (timeBoxGt q q') (fun ts k =>
        treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (Cf30 P.η C (Lsq P) * (Cf30 P.η C (Lsq P) * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hL2 : 1 ≤ Lsq P := one_le_Lsq P hd
  have hLle : cLeib P.d (30 * P.d) ≤ Lsq P := cLeib_le_Lsq P hd
  have hLc0 : 0 ≤ cLeib P.d (30 * P.d) := cLeib_nonneg _ _
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
  refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 0) (timeBoxGt (q : ℝ) q') Set.univ heq).trans_le ?_
  have hE' := hE
  rw [XNormRestr_eq_rN] at hE'
  refine hE'.trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 : 0 ≤ C * (C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd := by positivity
  calc C * (C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd
      ≤ Ktr P.η * (C * (C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) := le_mul_of_one_le_left h0 hK1
    _ ≤ _ := (absorb_base_err30 hC hδ hΛ0 hβ0 hL2 hK0 n).trans (absorb_final30' hη0 hC hδ hΛ0 hβ0 hL2 n)

/-- **The top block in layer `q`, and the rest.** -/
theorem tree_err_top30 {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (F : TreeCohFacts LG X q' q)
    (htop : layerAt LG ((0 : Fin 1), []) = q) (hXn : X ≠ .nil)
    (hDn : dropLayer LG ((0 : Fin 1), []) q X ≠ .nil)
    (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    rN P.η (30 * P.d) 0 (timeBoxGt q q') (fun ts k =>
        treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (Cf30 P.η C (Lsq P) * (Cf30 P.η C (Lsq P) * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hL2 : 1 ≤ Lsq P := one_le_Lsq P hd
  have hLle : cLeib P.d (30 * P.d) ≤ Lsq P := cLeib_le_Lsq P hd
  have hLc0 : 0 ≤ cLeib P.d (30 * P.d) := cLeib_nonneg _ _
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
    exact PL234.root_mem_chainNodesSet _ _ _ _ _ _ _
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
  obtain ⟨hX, hY⟩ := tree_top_bounds30 P B G₁ HT hd hL hη0 hη2 hδ hlt hBsize hdec₁ hlay₁ BT hctrl₁
    (by positivity) (by positivity) (by positivity) hET hJT hMT (timeBoxGt (q : ℝ) q') (-(q' : ℝ)) hT₁
  rw [hsig₁] at hX hY
  -- the lower bounds of the rest
  obtain ⟨hE₂, hA₂⟩ := tree_lower_bounds30 P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 H Bd F hqq.le hqp
    (timeBoxGt (q : ℝ) q') (-(q : ℝ)) hT m₂ B D LG'' hXe.symm hsz₂ (by omega) S''
  have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) :=
    Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hcK : ∀ k : Mom P.d, Continuous fun ts : Fin 2 → ℝ =>
      treeLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) ((r'' : ℝ) + 1) (ts 1) k :=
    fun k => continuous_treeLeaves_snd P.L P.γ P.δ LG'' _ S''.dec _ k (S''.ctrl.summable_coset hd hL k)
  have hcA : ∀ k : Mom P.d, Continuous fun ts : Fin 2 → ℝ =>
      lowAppT P.δ LG H q' B.lonePath D (ts 1) k := fun k =>
    continuous_lowAppT_snd P.δ LG H q' B.lonePath D k
  have hc₁ : ∀ k : Mom P.d, Continuous fun ts : Fin 2 → ℝ =>
      (treeLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) ((r'' : ℝ) + 1) (ts 1) k -
        lowAppT P.δ LG H q' B.lonePath D (ts 1) k) := fun k => (hcK k).sub (hcA k)
  have htopb := restr_top30 (θ := P.η) hΛ hd hη0 0 (timeBoxGt (q : ℝ) q')
    (fun ts hts => mem_closure_interior_timeBoxGt hts)
    (fun ts k => treeLeaves P.L P.γ P.δ G₁ HT (ts 0) q k)
    (fun ts k => LeafApp.tree P.δ q HT B ζ (ts 0) q k)
    (fun ts k => treeLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) ((r'' : ℝ) + 1) (ts 1) k)
    (fun ts k => lowAppT P.δ LG H q' B.lonePath D (ts 1) k) hc₁ hcA
    (by positivity) (by positivity) (by positivity) (by positivity) hX hY hE₂ hA₂
  have heq : ∀ ts ∈ timeBoxGt (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)),
      treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k =
      ((fun ts k => treeLeaves P.L P.γ P.δ G₁ HT (ts 0) q k) ts k *
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
    rw [hK (ts 0) (ts 1) k hr1, hA]
  refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 0) (timeBoxGt (q : ℝ) q') Set.univ heq).trans_le
    (htopb.1.trans (ENNReal.ofReal_le_ofReal ?_))
  -- constants
  have hε := absorb_tree_err30 hC hδ hΛ0 hβT0 hL2 hnB1
  have hα := absorb_tree_app30 hC hδ hβT0 hL2 hnB1
  have hK0 : 0 ≤ Ktr P.η := Ktr_nonneg _
  have hLc0 : 0 ≤ cLeib P.d (30 * P.d) := cLeib_nonneg _ _
  have hεK : cLeib P.d (30 * P.d) * (Ktr P.η * (C * (C * P.δ) ^ nB * gainΛ P * leafSizeProduct G₁ BT)) ≤
      (2 * C ^ 4 * Lsq P) ^ nB * P.δ ^ nB * gainΛ P * (Ktr P.η * leafSizeProduct G₁ BT) := by
    have h1 : cLeib P.d (30 * P.d) * (C * (C * P.δ) ^ nB * gainΛ P * leafSizeProduct G₁ BT) ≤
        Lsq P * (C * (C * P.δ) ^ nB * gainΛ P * leafSizeProduct G₁ BT) :=
      mul_le_mul_of_nonneg_right hLle (by positivity)
    calc cLeib P.d (30 * P.d) * (Ktr P.η * (C * (C * P.δ) ^ nB * gainΛ P * leafSizeProduct G₁ BT))
        = Ktr P.η * (cLeib P.d (30 * P.d) * (C * (C * P.δ) ^ nB * gainΛ P * leafSizeProduct G₁ BT)) := by ring
      _ ≤ Ktr P.η * ((2 * C ^ 4 * Lsq P) ^ nB * P.δ ^ nB * gainΛ P * leafSizeProduct G₁ BT) :=
          mul_le_mul_of_nonneg_left (h1.trans hε) hK0
      _ = _ := by ring
  have hαK : cLeib P.d (30 * P.d) * (2 ^ nB * (cLeib P.d (30 * P.d) * (P.δ ^ nB * (C * C ^ nB * leafSizeProduct G₁ BT)) *
      (Ktr P.η * (C * C ^ nB)))) ≤ (2 * C ^ 4 * Lsq P) ^ nB * P.δ ^ nB * (Ktr P.η * leafSizeProduct G₁ BT) := by
    have e : cLeib P.d (30 * P.d) * (2 ^ nB * (cLeib P.d (30 * P.d) * (P.δ ^ nB * (C * C ^ nB * leafSizeProduct G₁ BT)) *
        (Ktr P.η * (C * C ^ nB)))) = Lsq P *
        (Ktr P.η * (P.δ ^ nB * 2 ^ nB * (C * C ^ nB) * (C * C ^ nB * leafSizeProduct G₁ BT))) := by
      unfold Lsq; ring
    rw [e]
    calc Lsq P * (Ktr P.η * (P.δ ^ nB * 2 ^ nB * (C * C ^ nB) * (C * C ^ nB * leafSizeProduct G₁ BT)))
        = Ktr P.η * (Lsq P * (P.δ ^ nB * 2 ^ nB * (C * C ^ nB) * (C * C ^ nB * leafSizeProduct G₁ BT))) := by ring
      _ ≤ Ktr P.η * ((2 * C ^ 4 * Lsq P) ^ nB * P.δ ^ nB * leafSizeProduct G₁ BT) :=
          mul_le_mul_of_nonneg_left hα hK0
      _ = _ := by ring
  have habs := absorb_step (δ := P.δ) (Λ := gainΛ P) (D₀ := 2 * C ^ 4 * Lsq P) (M₀ := Ktr P.η * C ^ 2 * Lsq P)
    (m₂ := m₂) (n := nB) (β₁ := Ktr P.η * leafSizeProduct G₁ BT) (by positivity) (by positivity) hδ hΛ0 hΛ1
    (by positivity) hβ₂0 (by positivity) (by positivity)
    (ε := cLeib P.d (30 * P.d) * (Ktr P.η * (C * (C * P.δ) ^ nB * gainΛ P * leafSizeProduct G₁ BT)))
    (α := cLeib P.d (30 * P.d) * (2 ^ nB * (cLeib P.d (30 * P.d) * (P.δ ^ nB * (C * C ^ nB * leafSizeProduct G₁ BT)) *
      (Ktr P.η * (C * C ^ nB)))))
    hεK hαK le_rfl le_rfl (by positivity) (by positivity) hnB1
  rw [← hnn'] at habs
  have h2η : (2 : ℝ) ^ P.η ≤ 2 := by
    calc (2 : ℝ) ^ P.η ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hη1
      _ = 2 := Real.rpow_one 2
  set W := 3 ^ (n + 1) * (Ktr P.η * C ^ 2 * Lsq P) * (2 * C ^ 4 * Lsq P) ^ n * P.δ ^ n * gainΛ P *
    leafSizeProduct LG Bd with hW
  have hW0 : 0 ≤ W := by positivity
  refine le_trans ?_ ((absorb_final30 hη0 hC hδ hΛ0 hβ0 hL2 n))
  calc 2 ^ P.η * cLeib P.d (30 * P.d) * (Ktr P.η * (C * (C * P.δ) ^ nB * gainΛ P * leafSizeProduct G₁ BT) *
        (3 ^ (m₂ + 1) * (Ktr P.η * C ^ 2 * Lsq P) * (2 * C ^ 4 * Lsq P) ^ m₂ * P.δ ^ m₂ * gainΛ P *
            leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) +
          Ktr P.η * C ^ 2 * Lsq P * (2 * C ^ 4 * Lsq P) ^ m₂ * P.δ ^ m₂ *
            leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z))) +
        2 ^ nB * (cLeib P.d (30 * P.d) * (P.δ ^ nB * (C * C ^ nB * leafSizeProduct G₁ BT)) *
          (Ktr P.η * (C * C ^ nB))) *
          (3 ^ (m₂ + 1) * (Ktr P.η * C ^ 2 * Lsq P) * (2 * C ^ 4 * Lsq P) ^ m₂ * P.δ ^ m₂ * gainΛ P *
            leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z))))
      = 2 ^ P.η * (cLeib P.d (30 * P.d) * (Ktr P.η * (C * (C * P.δ) ^ nB * gainΛ P * leafSizeProduct G₁ BT)) *
        (3 ^ (m₂ + 1) * (Ktr P.η * C ^ 2 * Lsq P) * (2 * C ^ 4 * Lsq P) ^ m₂ * P.δ ^ m₂ * gainΛ P *
            leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) +
          Ktr P.η * C ^ 2 * Lsq P * (2 * C ^ 4 * Lsq P) ^ m₂ * P.δ ^ m₂ *
            leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z))) +
        cLeib P.d (30 * P.d) * (2 ^ nB * (cLeib P.d (30 * P.d) * (P.δ ^ nB * (C * C ^ nB * leafSizeProduct G₁ BT)) *
          (Ktr P.η * (C * C ^ nB)))) *
          (3 ^ (m₂ + 1) * (Ktr P.η * C ^ 2 * Lsq P) * (2 * C ^ 4 * Lsq P) ^ m₂ * P.δ ^ m₂ * gainΛ P *
            leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)))) := by ring
    _ ≤ 2 * (Ktr P.η * W) := by
        apply mul_le_mul h2η _ (by positivity) (by norm_num)
        refine habs.1.trans_eq ?_
        rw [hW, hβe]
        ring
    _ = _ := by rw [hW]; ring

/-- **The root below `q`**: the kernel does not depend on `t ≥ q`; the lower bounds with `π = []`. -/
theorem tree_err_low30 {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (F : TreeCohFacts LG X q' q)
    (hr₁lt : layerAt LG ((0 : Fin 1), []) < q)
    (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    rN P.η (30 * P.d) 0 (timeBoxGt q q') (fun ts k =>
        treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (Cf30 P.η C (Lsq P) * (Cf30 P.η C (Lsq P) * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hL2 : 1 ≤ Lsq P := one_le_Lsq P hd
  have hLle : cLeib P.d (30 * P.d) ≤ Lsq P := cLeib_le_Lsq P hd
  have hLc0 : 0 ≤ cLeib P.d (30 * P.d) := cLeib_nonneg _ _
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
      | pair m' Qr' Qg' inner' rest' => exact PL234.root_mem_chainNodesSet _ _ _ _ _ _ _
  have hlowr₁ : q' ≤ r₁ := by
    by_cases hXn : X = .nil
    · have h := F.lone
      rw [hXn] at h
      have : r₁ = q' := by simpa [RegChain.lonePath] using h
      rw [this]
    · exact F.low _ (hroot hXn)
  obtain ⟨hE, -⟩ := tree_lower_bounds30 P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 H Bd F hqq.le hqp
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
  refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 0) (timeBoxGt (q : ℝ) q') Set.univ heq).trans_le (hE.trans ?_)
  simp only [RegChain.lonePath]
  rw [hBe]
  exact ENNReal.ofReal_le_ofReal (absorb_final30' hη0 hC hδ hΛ0 hβ0 hL2 n)

/-- **Prop 6.1, trees, `q > q'`: the error estimate** (TARGET L1097–1111, prooflayer1-2). -/
theorem tree_err_gt30 {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (hcoh : IsCoherentTreeAt p q q' X LG)
    (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    rN P.η (30 * P.d) 0 (timeBoxGt q q') (fun ts k =>
        treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (Cf30 P.η C (Lsq P) * (Cf30 P.η C (Lsq P) * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hL2 : 1 ≤ Lsq P := one_le_Lsq P hd
  have hLle : cLeib P.d (30 * P.d) ≤ Lsq P := cLeib_le_Lsq P hd
  have hLc0 : 0 ≤ cLeib P.d (30 * P.d) := cLeib_nonneg _ _
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
      | pair m' Qr' Qg' inner' rest' => exact PL234.root_mem_chainNodesSet _ _ _ _ _ _ _
  by_cases htop : layerAt LG ((0 : Fin 1), []) = q
  · have hXn : X ≠ .nil := fun h => by have := hnil h; omega
    by_cases hDn : dropLayer LG ((0 : Fin 1), []) q X = .nil
    · have hXe := appendChain_take_drop LG ((0 : Fin 1), []) q X
      rw [hDn, appendChain_nil_right] at hXe
      have hTAX : TopAll LG q ((0 : Fin 1), []) X := by
        have := topAll_takeLayer LG q ((0 : Fin 1), []) X
        rwa [hXe] at this
      exact tree_err_single30 P O hC hd hη0 hδ hΛ0 hqq hqp hnN X hsize LG F hTAX H Bd hH
    · exact tree_err_top30 P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 hqq hqp hnN X hsize LG F htop hXn hDn H Bd hH
  · exact tree_err_low30 P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 hqq hqp hnN X hsize LG F
      (lt_of_le_of_ne hr₁q htop) H Bd hH

end Err

end WaveTurbulence.PL2330
