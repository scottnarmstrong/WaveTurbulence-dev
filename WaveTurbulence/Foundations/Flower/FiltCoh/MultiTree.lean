/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiPieces
public import WaveTurbulence.Foundations.Spine.PL2330Draft.TreeInd

/-! # FILT-COH: coherent paired trees across layers (bound only)

The kernel of a coherent regular tree whose chain crosses layers is a product of single-layer tree kernels
(`PL234.tree_block_step`): a top factor in `t`, middle factors at fixed times (spatial profiles) and a bottom
factor in `s`. Main's induction over the blocks (`PL2330.tree_lower_bounds30`) is replayed for the kernel alone,
from the single-layer bounds (`TreeKOracle`) and the trace lemmas of `MultiPieces`, at any weight `θ ∈ [0, 1]`. -/

public section
open WaveTurbulence.Induct
open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltCoh

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.PL2330 WaveTurbulence.Reg WaveTurbulence.Links

variable {d : ℕ}

/-- The single-layer tree bound used by the induction (the tree clause of `single_layer_bounds`). -/
@[expose] def TreeKOracle (d : ℕ) (L γ δ θ : ℝ) (Nmax : ℕ) (C : ℝ) : Prop :=
  ∀ (r q'' n : ℕ), q'' ≤ r → n ≤ Nmax → ∀ X : RegChain, X.wf = true → X.size = 2 * n →
    ∀ LG : LayeredGarden 1, X.DecodesTree LG.garden →
    (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r) →
    ∀ (H : LeafProfiles 1 d) (B : (Fin 1 × Path) → NNReal), LeafwiseControlled LG H B →
    XNormRestr θ (30 * d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (C * (C * δ) ^ n * leafSizeProduct LG B)

/-- The absorption of one block: `c C^{nB+1} ≤ G^{nB}` when `c C² ≤ G` and `nB ≥ 1`. -/
theorem absorb_kernel_step {c C G δ βT β₂ : ℝ} {nB m₂ : ℕ} (hc1 : 1 ≤ c) (hC : 1 ≤ C) (hG : c * C ^ 2 ≤ G)
    (hδ : 0 ≤ δ) (hβT : 0 ≤ βT) (hβ₂ : 0 ≤ β₂) (hnB : 1 ≤ nB) :
    c * (C * (C * δ) ^ nB * βT) * (G * (G * δ) ^ m₂ * β₂) ≤ G * (G * δ) ^ (nB + m₂) * (βT * β₂) := by
  obtain ⟨k, rfl⟩ : ∃ k, nB = k + 1 := ⟨nB - 1, by omega⟩
  have hC0 : 0 ≤ C := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hCG : C ≤ G := by nlinarith [pow_le_pow_left₀ zero_le_one hC 2]
  have hG0 : 0 ≤ G := le_trans hC0 hCG
  have hkey : c * C ^ (k + 2) ≤ G ^ (k + 1) := by
    have h1 : C ^ k ≤ G ^ k := pow_le_pow_left₀ hC0 hCG k
    calc c * C ^ (k + 2) = C ^ k * (c * C ^ 2) := by ring
      _ ≤ G ^ k * G := mul_le_mul h1 hG (by positivity) (by positivity)
      _ = G ^ (k + 1) := by ring
  have hδp : 0 ≤ δ ^ (k + 1 + m₂) := by positivity
  calc c * (C * (C * δ) ^ (k + 1) * βT) * (G * (G * δ) ^ m₂ * β₂)
      = (c * C ^ (k + 2)) * (G * G ^ m₂ * δ ^ (k + 1 + m₂) * (βT * β₂)) := by ring
    _ ≤ G ^ (k + 1) * (G * G ^ m₂ * δ ^ (k + 1 + m₂) * (βT * β₂)) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = G * (G * δ) ^ (k + 1 + m₂) * (βT * β₂) := by ring

section Induction

variable {L γ δ θ : ℝ} {Nmax : ℕ} {C : ℝ} (O : TreeKOracle d L γ δ θ Nmax C) (hC : 1 ≤ C)
  (hd : 1 ≤ d) (hL : 1 ≤ L) (hθ0 : 0 ≤ θ) (hδ : 0 ≤ δ)
  {LG : LayeredGarden 1} (H : LeafProfiles 1 d) (Bd : (Fin 1 × Path) → NNReal)
  {X₀ : RegChain} {q' q : ℕ} (F : TreeCohFacts LG X₀ q' q) (hqq : q' ≤ q)
  (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox)

include O hC hd hL hθ0 hδ F hqq hT'

/-- **The lower kernels of a tree**, by induction over the blocks of its chain (bound-only
`PL2330.tree_lower_bounds30`), with `G = K_tr(θ) · cLeib · C²`. -/
theorem tree_lower_kernel : ∀ (m : ℕ) (R Y : RegChain) (LG' : LayeredGarden 1), X₀ = appendChain R Y →
    Y.size = 2 * m → m ≤ Nmax → TreeLowState LG H Bd R.lonePath Y LG' →
    rN θ (30 * d) 0 T' (fun ts k =>
        treeLeaves L γ δ LG' (fun z => H (botAddr R.lonePath z))
          ((layerAt LG ((0 : Fin 1), R.lonePath) : ℝ) + 1) (ts 1) k) ≤
        ENNReal.ofReal ((Ktr θ * cLeib d (30 * d) * C ^ 2) * ((Ktr θ * cLeib d (30 * d) * C ^ 2) * δ) ^ m *
          leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z))) := by
  have _hqq' := hqq
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro R Y LG' hXp hsize hmN S
  have hΛ : 30 * d ≠ 0 := by omega
  have hC0 : 0 ≤ C := by linarith
  have hK1 : 1 ≤ Ktr θ := one_le_Ktr hθ0
  have hK0 : 0 ≤ Ktr θ := Ktr_nonneg _
  have hLc : 1 ≤ cLeib d (30 * d) := one_le_cLeib hd _
  set G := Ktr θ * cLeib d (30 * d) * C ^ 2 with hGdef
  have hCG : C ≤ G := by
    have h1 : 1 * 1 * C ^ 1 ≤ Ktr θ * cLeib d (30 * d) * C ^ 2 :=
      mul_le_mul (mul_le_mul hK1 hLc zero_le_one (by linarith)) (pow_le_pow_right₀ hC (by norm_num))
        (by positivity) (by positivity)
    simpa using h1
  have hG0 : 0 ≤ G := hC0.trans hCG
  have hβ0 : 0 ≤ leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) :=
    Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  set π := R.lonePath with hπ
  set ζ := LG.garden.sig 0 with hζ
  set u := layerAt LG ((0 : Fin 1), π) with hu
  have hYwf := F.wf_suffix hXp
  have hEmb := F.emb_suffix hXp
  have hPL := F.pl_suffix hXp
  have hSM := F.sm_suffix hXp
  have hlone := F.lone_suffix hXp
  have hroot : Y ≠ .nil → ((0 : Fin 1), π) ∈ chainNodesSet Y ζ ((0 : Fin 1), π) := fun hYn => by
    cases Y with
    | nil => exact absurd rfl hYn
    | pair m' Qr' Qg' inner' rest' => exact PL234.root_mem_chainNodesSet _ _ _ _ _ _ _
  have hnil : Y = .nil → u = q' := fun hYn => by
    rw [hYn] at hlone
    simpa [RegChain.lonePath, addrExt] using hlone
  have hqu : q' ≤ u := by
    by_cases hYn : Y = .nil
    · rw [hnil hYn]
    · exact F.low _ (TreeCohFacts.sub_suffix hXp (hroot hYn))
  set B := takeLayer LG ((0 : Fin 1), π) u Y with hBdef
  set D := dropLayer LG ((0 : Fin 1), π) u Y with hDdef
  have hXe : appendChain B D = Y := appendChain_take_drop LG _ u Y
  have hTA : TopAll LG u ((0 : Fin 1), π) B := topAll_takeLayer LG u _ Y
  have hEmbBD : ChainEmb LG.garden (appendChain B D) ζ ((0 : Fin 1), π) .leaf := by rw [hXe]; exact hEmb
  have hPLBD : ChainPairLayers LG (appendChain B D) ζ ((0 : Fin 1), π) := by rw [hXe]; exact hPL
  have hBlay : ∀ z ∈ chainNodesSet B ζ ((0 : Fin 1), π), layerAt LG z = u :=
    chainNodes_layer_of_topAll (chainEmb_append_left hEmbBD) (chainPairLayers_append_left LG B D ζ _ hPLBD) hTA
  by_cases hDn : D = .nil
  · -- the base: a single block in layer `u`, with the lone leaf in layer `q'`
    have hYB : Y = B := by rw [← hXe, hDn]; exact appendChain_nil_right B
    have hTAY : TopAll LG u ((0 : Fin 1), π) Y := by rw [hYB]; exact hTA
    have hYlay : ∀ z ∈ chainNodesSet Y ζ ((0 : Fin 1), π), layerAt LG z = u :=
      chainNodes_layer_of_topAll hEmb hPL hTAY
    have hlay' : ∀ a : GNode LG'.garden.tree, LG'.layer a = if a.1.2 = Y.lonePath then q' else u := by
      intro a
      rw [← layerAt_node, S.lay]
      have hba : botAddr π a.1 = addrExt ((0 : Fin 1), π) a.1.2 := by
        obtain ⟨⟨j, p⟩, _⟩ := a
        fin_cases j
        simp [botAddr, addrExt]
      rw [hba]
      split_ifs with hl
      · rw [hl]
        exact hlone
      · rcases addrExt_mem_chainNodes S.dec ((0 : Fin 1), π) a with h | h
        · rw [S.sig] at h
          exact hYlay _ h
        · exact absurd h hl
    have hE := O u q' m hqu hmN Y hYwf hsize LG' S.dec hlay' _ _ S.ctrl
    have hEb := tree_bottom_kernel hd hL hθ0 hqu S.dec S.ctrl hE T' b₀ hT'
    refine hEb.trans (ENNReal.ofReal_le_ofReal ?_)
    calc Ktr θ * (C * (C * δ) ^ m * leafSizeProduct LG' (fun z => Bd (botAddr π z)))
        = (Ktr θ * C) * (C * δ) ^ m * leafSizeProduct LG' (fun z => Bd (botAddr π z)) := by ring
      _ ≤ G * (G * δ) ^ m * leafSizeProduct LG' (fun z => Bd (botAddr π z)) := by
          apply mul_le_mul_of_nonneg_right _ hβ0
          apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCG hδ) m)
            (by positivity) hG0
          calc Ktr θ * C = Ktr θ * 1 * C ^ 1 := by ring
            _ ≤ Ktr θ * cLeib d (30 * d) * C ^ 2 :=
                mul_le_mul (mul_le_mul_of_nonneg_left hLc hK0) (pow_le_pow_right₀ hC (by norm_num))
                  (by positivity) (by positivity)
  · -- the step: remove the top block
    have hYn : Y ≠ .nil := by
      intro h
      apply hDn
      rw [hDdef, h]
      rfl
    have hnode : (addrExt ((0 : Fin 1), π) B.lonePath).2 ∈
        (LG.garden.tree (addrExt ((0 : Fin 1), π) B.lonePath).1).nodes := by
      have ht : (LG.garden.tree ((0 : Fin 1), π).1).subtreeAt ((0 : Fin 1), π).2 =
          B.plug ζ (D.plug ζ .leaf) := by
        rw [hEmbBD.tree, appendChain_plug]
      exact (node_iff_of_subtree hEmb.node ht B.lonePath).1.mpr (lonePath_mem_plug B ζ _)
    have hle : layerAt LG ((0 : Fin 1), π ++ B.lonePath) ≤ u :=
      layerAt_le_of_under LG hEmb.node hnode (under_ext _ _)
    have hlt : layerAt LG ((0 : Fin 1), π ++ B.lonePath) < u :=
      lt_of_le_of_ne hle (layer_drop_ne LG u Y _ hDn)
    obtain ⟨G₁, LG'', hdec₁, hsig₁, hlay₁, hctrl₁, S'', hβ, hK⟩ :=
      tree_block_step S L γ δ hd hL hYwf hDn hlt hBlay
    -- sizes
    have hwfBD : (appendChain B D).wf = true := by rw [hXe]; exact hYwf
    rw [appendChain_wf, Bool.and_eq_true] at hwfBD
    have hsz : Y.size = B.size + D.size := by rw [← hXe, appendChain_size]
    obtain ⟨nB, hnB⟩ := size_even_chain B
    obtain ⟨m₂, hm₂⟩ := size_even_chain D
    have hB2 := two_le_size_of_ne_nil B (takeLayer_ne_nil LG Y _ hYn)
    have hBsize : B.size = 2 * nB := by omega
    have hsz₂ : D.size = 2 * m₂ := by omega
    have hmm : m = nB + m₂ := by omega
    have hnB1 : 1 ≤ nB := by omega
    -- the middle factor
    set HT := LeafApp.sliceProfiles LG H ((0 : Fin 1), π) u Y with hHT
    set BT : (Fin 1 × Path) → NNReal := fun z => Bd (LeafApp.sliceAddress LG ((0 : Fin 1), π) u Y z.2) with hBT
    have hβT0 : 0 ≤ leafSizeProduct G₁ BT := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hET := O u _ nB hlt.le (by omega) B hwfBD.1 hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
    have hmid := tree_middle_kernel hd hL hθ0 hlt hdec₁ hlay₁ hctrl₁ hET
    -- the induction hypothesis on the rest
    have hXp' : X₀ = appendChain (appendChain R B) D := by rw [appendChain_assoc, hXe]; exact hXp
    have hlp : (appendChain R B).lonePath = π ++ B.lonePath := appendChain_lonePath R B
    have S''' : TreeLowState LG H Bd (appendChain R B).lonePath D LG'' := by rw [hlp]; exact S''
    have hE₂ := ih m₂ (by omega) (appendChain R B) D LG'' hXp' hsz₂ (by omega) S'''
    rw [hlp] at hE₂
    have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ B.lonePath) z)) :=
      Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hstep := restr_mul_w_le hΛ hd (θ := θ) 0 T'
      (c := fun k => treeLeaves L γ δ G₁ HT ((u : ℝ) + 1) u k)
      (fun ts k => treeLeaves L γ δ LG'' (fun z => H (botAddr (π ++ B.lonePath) z))
        ((layerAt LG ((0 : Fin 1), π ++ B.lonePath) : ℝ) + 1) (ts 1) k)
      (by positivity) hmid hE₂
    have heq : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom d)),
        treeLeaves L γ δ LG' (fun z => H (botAddr π z)) ((u : ℝ) + 1) (ts 1) k =
        (fun k => treeLeaves L γ δ G₁ HT ((u : ℝ) + 1) u k) k *
          (fun ts k => treeLeaves L γ δ LG'' (fun z => H (botAddr (π ++ B.lonePath) z))
            ((layerAt LG ((0 : Fin 1), π ++ B.lonePath) : ℝ) + 1) (ts 1) k) ts k := fun ts _ k _ => by
      rw [hK ((u : ℝ) + 1) (ts 1) k (by exact_mod_cast Nat.succ_le_succ hlt.le)]
    refine (restr_congr (θ := θ) (Λ := 30 * d) (Λ₂ := 0) T' Set.univ heq).trans_le (hstep.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have hab := absorb_kernel_step (c := cLeib d (30 * d)) (C := C) (G := G) (δ := δ)
      (βT := leafSizeProduct G₁ BT) (β₂ := leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ B.lonePath) z)))
      (nB := nB) (m₂ := m₂) hLc hC (by
        calc cLeib d (30 * d) * C ^ 2 = 1 * cLeib d (30 * d) * C ^ 2 := by ring
          _ ≤ G := by
            rw [hGdef]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 (by positivity)) (by positivity))
      hδ hβT0 hβ₂0 hnB1
    rw [← hmm, ← hβ] at hab
    calc cLeib d (30 * d) * (C * (C * δ) ^ nB * leafSizeProduct G₁ BT) *
          (G * (G * δ) ^ m₂ * leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ B.lonePath) z)))
        ≤ _ := hab

end Induction

end WaveTurbulence.Flower.FiltCoh
