/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiTree
public import WaveTurbulence.Foundations.Spine.PL2330Draft.TreeGate

/-! # FILT-COH: coherent paired trees `(q, q')`, any weight `θ ∈ [0, 1]` (bound only)

The case split of main's `PL2330.tree_err_gt30` (single block / top block in layer `q` / root below `q`) and
`tree_same30`, for the kernel alone. The constant is `G' = 2 K_tr(θ) cLeib C²`. -/

public section
open WaveTurbulence.Induct
open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltCoh

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.PL2330 WaveTurbulence.Reg WaveTurbulence.Links

variable {d : ℕ}

/-- The constant of the coherent tree bound. -/
@[expose] noncomputable def treeG (d : ℕ) (θ C : ℝ) : ℝ := 2 * (Ktr θ * cLeib d (30 * d) * C ^ 2)

theorem le_treeG {d : ℕ} (hd : 1 ≤ d) {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 1 ≤ C) :
    C ≤ treeG d θ C ∧ Ktr θ * cLeib d (30 * d) * C ^ 2 ≤ treeG d θ C ∧ 1 ≤ treeG d θ C := by
  have hK1 : 1 ≤ Ktr θ := one_le_Ktr hθ
  have hLc : 1 ≤ cLeib d (30 * d) := one_le_cLeib hd _
  have h1 : C ≤ Ktr θ * cLeib d (30 * d) * C ^ 2 := by
    have := mul_le_mul (mul_le_mul hK1 hLc zero_le_one (by linarith)) (pow_le_pow_right₀ hC
      (by norm_num : 1 ≤ 2)) (by positivity) (by positivity)
    simpa using this
  have h0 : 0 ≤ Ktr θ * cLeib d (30 * d) * C ^ 2 := by linarith
  unfold treeG
  refine ⟨by linarith, by linarith, by linarith⟩

theorem bound_mono_G {C G δ β : ℝ} (n : ℕ) (hC : 0 ≤ C) (hCG : C ≤ G) (hδ : 0 ≤ δ) (hβ : 0 ≤ β) :
    C * (C * δ) ^ n * β ≤ G * (G * δ) ^ n * β :=
  mul_le_mul_of_nonneg_right (mul_le_mul hCG (pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_right hCG hδ) n) (by positivity) (hC.trans hCG)) hβ


theorem ofReal_mul4 {a b c e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c * ENNReal.ofReal e =
      ENNReal.ofReal (a * b * c * e) := by
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg ha hb) hc)]

section Gate

variable {L γ δ θ : ℝ} {Nmax : ℕ} {C : ℝ} (O : TreeKOracle d L γ δ θ Nmax C) (hC : 1 ≤ C)
  (hd : 1 ≤ d) (hL : 1 ≤ L) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hδ : 0 ≤ δ)

include O hC hd hL hθ0 hθ1 hδ

/-- **Coherent paired trees, `q' < q`.** -/
theorem tree_gt_kernel {q q' n : ℕ} (hqq : q' < q) (hnN : n ≤ Nmax)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (F : TreeCohFacts LG X q' q)
    (H : LeafProfiles 1 d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    XNormRestr θ (30 * d) 0 (timeBoxGt q q') Set.univ
      (fun ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (treeG d θ C * (treeG d θ C * δ) ^ n * leafSizeProduct LG Bd) := by
  have hΛ : 30 * d ≠ 0 := by omega
  obtain ⟨hCG', hGG', hG1⟩ := le_treeG hd hθ0 hC
  set G' := treeG d θ C with hG'def
  set G := Ktr θ * cLeib d (30 * d) * C ^ 2 with hGdef
  have hC0 : 0 ≤ C := by linarith
  have hK1 : 1 ≤ Ktr θ := one_le_Ktr hθ0
  have hK0 : 0 ≤ Ktr θ := Ktr_nonneg _
  have hLc : 1 ≤ cLeib d (30 * d) := one_le_cLeib hd _
  have hβ0 : 0 ≤ leafSizeProduct LG Bd := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b :=
    noFlowerParent_of_noFlower (not_flower_of_decodesTree F.dec)
  have hHe : (fun z => H (botAddr [] z)) = H := funext fun z => by rw [botAddr_nil_tree]
  have hBe : (fun z => Bd (botAddr [] z)) = Bd := funext fun z => by rw [botAddr_nil_tree]
  have S₀ : TreeLowState LG H Bd [] X LG := TreeLowState.root F.dec hH
  have hT := timeBoxGt_shift_unit q q'
  set ζ := LG.garden.sig 0 with hζ
  have hnil : X = .nil → layerAt LG ((0 : Fin 1), []) = q' := fun hXn => by
    have h := F.lone
    rw [hXn] at h
    simpa [RegChain.lonePath] using h
  have hroot : X ≠ .nil → ((0 : Fin 1), ([] : Path)) ∈ chainNodesSet X ζ ((0 : Fin 1), []) := fun hXn => by
    cases X with
    | nil => exact absurd rfl hXn
    | pair m' Qr' Qg' inner' rest' => exact PL234.root_mem_chainNodesSet _ _ _ _ _ _ _
  have hr₁q : layerAt LG ((0 : Fin 1), []) ≤ q := by
    by_cases hXn : X = .nil
    · rw [hnil hXn]; exact hqq.le
    · exact F.high _ (hroot hXn)
  rw [XNormRestr_eq_rN]
  by_cases htop : layerAt LG ((0 : Fin 1), []) = q
  · have hXn : X ≠ .nil := fun h => by have := hnil h; omega
    have hEmb := ChainEmb.of_decodesTree F.dec
    by_cases hDn : dropLayer LG ((0 : Fin 1), []) q X = .nil
    · -- a single block in layer `q`
      have hXe := appendChain_take_drop LG ((0 : Fin 1), []) q X
      rw [hDn, appendChain_nil_right] at hXe
      have hTAX : TopAll LG q ((0 : Fin 1), []) X := by
        have := topAll_takeLayer LG q ((0 : Fin 1), []) X
        rwa [hXe] at this
      have hXlay : ∀ z ∈ chainNodesSet X ζ ((0 : Fin 1), []), layerAt LG z = q :=
        chainNodes_layer_of_topAll hEmb F.pl hTAX
      have hlay := layer_single_block F.dec F.lone hXlay
      have hE := O q q' n hqq.le hnN X F.wf hsize LG F.dec hlay H Bd hH
      rw [XNormRestr_eq_rN] at hE
      exact hE.trans (ENNReal.ofReal_le_ofReal (bound_mono_G n hC0 hCG' hδ hβ0))
    · -- the top block in layer `q`, then the lower blocks
      set B := takeLayer LG ((0 : Fin 1), []) q X with hBdef
      set D := dropLayer LG ((0 : Fin 1), []) q X with hDdef
      have hXe : appendChain B D = X := appendChain_take_drop LG _ q X
      have hTA : TopAll LG q ((0 : Fin 1), []) B := topAll_takeLayer LG q _ X
      have hEmbBD : ChainEmb LG.garden (appendChain B D) ζ ((0 : Fin 1), []) .leaf := by rw [hXe]; exact hEmb
      have hPLBD : ChainPairLayers LG (appendChain B D) ζ ((0 : Fin 1), []) := by rw [hXe]; exact F.pl
      have hBlay : ∀ z ∈ chainNodesSet B ζ ((0 : Fin 1), []), layerAt LG z = q :=
        chainNodes_layer_of_topAll (chainEmb_append_left hEmbBD) (chainPairLayers_append_left LG B D ζ _ hPLBD) hTA
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
      have hBlay' : ∀ z ∈ chainNodesSet (takeLayer LG ((0 : Fin 1), []) q X) (LG.garden.sig 0) (0, []),
          layerAt LG z = q := hBlay
      obtain ⟨G₁, LG'', hdec₁, hsig₁, hlay₁, hctrl₁, S'', hβ, hK⟩ :=
        tree_block_step S₀ L γ δ hd hL F.wf hDn hlt hBlay'
      simp only [List.nil_append] at hlay₁ S'' hβ hK
      rw [hHe] at hK
      have hβe : leafSizeProduct LG Bd =
          leafSizeProduct G₁ (fun z => Bd (LeafApp.sliceAddress LG (0, []) q X z.2)) *
            leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) := by
        have h' := hβ
        rw [hBe] at h'
        exact h'
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
      have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) :=
        Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
      -- the top factor
      have hET := O q r'' nB hlt.le (by omega) B hwfBD.1 hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
      have hX₁ := tree_top_kernel hd hL hθ0 hlt hdec₁ hlay₁ hctrl₁ hET (timeBoxGt (q : ℝ) q') (-(q' : ℝ))
        (fun ts hts => hT ts hts)
      -- the lower factor
      have hX₂ := tree_lower_kernel O hC hd hL hθ0 hδ H Bd F hqq.le (timeBoxGt (q : ℝ) q') (-(q : ℝ)) hT
        m₂ B D LG'' hXe.symm hsz₂ (by omega) S''
      -- the product
      have hcont : ∀ k, Continuous fun ts : Fin 2 → ℝ =>
          treeLeaves L γ δ LG'' (fun z => H (botAddr B.lonePath z))
            ((layerAt LG ((0 : Fin 1), B.lonePath) : ℝ) + 1) (ts 1) k := fun k =>
        continuous_treeLeaves_snd L γ δ LG'' _ S''.dec _ k (S''.ctrl.summable_coset hd hL k)
      have hprod := restr_mul_le hΛ hd hθ0 0 0 (B := timeBoxGt (q : ℝ) q')
        (fun ts hts => mem_closure_interior_timeBoxGt hts)
        (fun ts k => treeLeaves L γ δ G₁ HT (ts 0) q k)
        (fun ts k => treeLeaves L γ δ LG'' (fun z => H (botAddr B.lonePath z))
          ((layerAt LG ((0 : Fin 1), B.lonePath) : ℝ) + 1) (ts 1) k) hcont
        (hX₁.trans_lt ENNReal.ofReal_lt_top) (hX₂.trans_lt ENNReal.ofReal_lt_top)
      have heq : ∀ ts ∈ timeBoxGt (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom d)),
          treeLeaves L γ δ LG H (ts 0) (ts 1) k =
            treeLeaves L γ δ G₁ HT (ts 0) q k *
              treeLeaves L γ δ LG'' (fun z => H (botAddr B.lonePath z))
                ((layerAt LG ((0 : Fin 1), B.lonePath) : ℝ) + 1) (ts 1) k := by
        intro ts hts k _
        have ht0 : (q : ℝ) ≤ ts 0 := hts.1.1.1
        have hr1 : (r'' : ℝ) + 1 ≤ ts 0 := by
          have : (r'' : ℝ) + 1 ≤ q := by exact_mod_cast hlt
          linarith
        exact hK (ts 0) (ts 1) k hr1
      rw [zero_add] at hprod
      refine (restr_congr (θ := θ) (Λ := 30 * d) (Λ₂ := 0) (timeBoxGt (q : ℝ) q') Set.univ heq).trans_le
        (hprod.trans ((mul_le_mul' (mul_le_mul' le_rfl hX₁) hX₂).trans ?_))
      rw [ofReal_mul4 (Real.rpow_nonneg (by norm_num) θ) (cLeib_nonneg _ _)
        (mul_nonneg hK0 (by positivity))]
      apply ENNReal.ofReal_le_ofReal
      have h2θ : (2 : ℝ) ^ θ ≤ 2 := by
        calc (2 : ℝ) ^ θ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
          _ = 2 := Real.rpow_one 2
      have hlowG : G * (G * δ) ^ m₂ * leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) ≤
          G' * (G' * δ) ^ m₂ * leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) :=
        bound_mono_G m₂ (by positivity) hGG' hδ hβ₂0
      have hab := absorb_kernel_step (c := 2 * (cLeib d (30 * d) * Ktr θ)) (C := C) (G := G')
        (δ := δ) (βT := leafSizeProduct G₁ BT)
        (β₂ := leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z))) (nB := nB) (m₂ := m₂)
        (by nlinarith) hC (by rw [hG'def]; unfold treeG; nlinarith) hδ hβT0 hβ₂0 hnB1
      rw [← hnn', ← hβe] at hab
      calc 2 ^ θ * cLeib d (30 * d) * (Ktr θ * (C * (C * δ) ^ nB * leafSizeProduct G₁ BT)) *
            (G * (G * δ) ^ m₂ * leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)))
          ≤ 2 * cLeib d (30 * d) * (Ktr θ * (C * (C * δ) ^ nB * leafSizeProduct G₁ BT)) *
            (G' * (G' * δ) ^ m₂ * leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z))) := by
            gcongr
        _ = 2 * (cLeib d (30 * d) * Ktr θ) * (C * (C * δ) ^ nB * leafSizeProduct G₁ BT) *
            (G' * (G' * δ) ^ m₂ * leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z))) := by ring
        _ ≤ _ := hab
  · -- the root lies below `q`: the kernel does not depend on `t`
    have hr₁lt : layerAt LG ((0 : Fin 1), []) < q := lt_of_le_of_ne hr₁q htop
    set r₁ := layerAt LG ((0 : Fin 1), []) with hr₁
    have hE := tree_lower_kernel O hC hd hL hθ0 hδ H Bd F hqq.le (timeBoxGt (q : ℝ) q') (-(q : ℝ)) hT
      n .nil X LG rfl hsize hnN S₀
    have heq : ∀ ts ∈ timeBoxGt (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom d)),
        treeLeaves L γ δ LG H (ts 0) (ts 1) k =
          treeLeaves L γ δ LG (fun z => H (botAddr RegChain.nil.lonePath z))
            ((layerAt LG ((0 : Fin 1), RegChain.nil.lonePath) : ℝ) + 1) (ts 1) k := by
      intro ts hts k _
      have ht0 : (q : ℝ) ≤ ts 0 := hts.1.1.1
      have hq1' : (r₁ : ℝ) + 1 ≤ q := by exact_mod_cast hr₁lt
      have hK : treeLeaves L γ δ LG H (ts 0) (ts 1) k =
          treeLeaves L γ δ LG H ((r₁ : ℝ) + 1) (ts 1) k :=
        treeLeaves_upper_eq L γ δ LG H hfl (ts 1) k fun b => by
          have hroot0 : ([] : Path) ∈ (LG.garden.tree 0).nodes := TTree.nil_mem_nodes _
          have hu : Under ((0 : Fin 1), ([] : Path)) b.toNode.1 :=
            ⟨Subsingleton.elim _ _, List.nil_prefix⟩
          have hl := layerAt_le_of_under LG hroot0 b.toNode.2 hu
          rw [layerAt_node] at hl
          have : (LG.layer b.toNode : ℝ) ≤ r₁ := by exact_mod_cast hl
          exact ⟨by linarith, by linarith⟩
      simp only [RegChain.lonePath]
      rw [hK, hHe]
    refine (restr_congr (θ := θ) (Λ := 30 * d) (Λ₂ := 0) (timeBoxGt (q : ℝ) q') Set.univ heq).trans_le
      (hE.trans ?_)
    simp only [RegChain.lonePath]
    rw [hBe]
    exact ENNReal.ofReal_le_ofReal (bound_mono_G n (by positivity) hGG' hδ hβ0)

/-- **Coherent paired trees, all `q' ≤ q`.** -/
theorem tree_coherent_kernel {p q q' n : ℕ} (hqq : q' ≤ q) (hnN : n ≤ Nmax)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (hcoh : IsCoherentTreeAt p q q' X LG)
    (H : LeafProfiles 1 d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    XNormRestr θ (30 * d) 0 (timeBoxGt q q') Set.univ
      (fun ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (treeG d θ C * (treeG d θ C * δ) ^ n * leafSizeProduct LG Bd) := by
  rcases eq_or_lt_of_le hqq with heq | hlt
  · subst heq
    have hlay := coherentTree_layer_eq hcoh
    have hlay' : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else q' := fun a => by
      rw [hlay a]
      split_ifs <;> rfl
    have hβ0 : 0 ≤ leafSizeProduct LG Bd := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    exact (O q' q' n le_rfl hnN X hcoh.1 hsize LG hcoh.2.1 hlay' H Bd hH).trans
      (ENNReal.ofReal_le_ofReal (bound_mono_G n (by linarith) (le_treeG hd hθ0 hC).1 hδ hβ0))
  · exact tree_gt_kernel O hC hd hL hθ0 hθ1 hδ hlt hnN X hsize LG (treeCohFacts_of_coherent hcoh) H Bd hH

end Gate

end WaveTurbulence.Flower.FiltCoh
