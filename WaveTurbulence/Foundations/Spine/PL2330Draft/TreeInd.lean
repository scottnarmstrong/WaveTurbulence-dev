/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.CoupleGate
public import WaveTurbulence.Foundations.Spine.PL234Draft.TreeGate

/-!
# Prop 6.1 at `Λ₁ = 30d`, `q > q'`, trees: the induction over the blocks of the chain (PL23-30D)

**`tree_lower_bounds30`** is `PL234.tree_lower_bounds` in the norm `𝔛^{η,30d,0}`, with `L = (2d)^{30d}`,
`M₀ = K_tr C² L²`, `D₀ = 2C⁴L²` (`Lsq`).
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL2330

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.Reg WaveTurbulence.Links

section Induction

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1) (hη2 : P.η ≤ 1 - P.η) (hδ : 0 ≤ P.δ)
  (hΛ0 : 0 ≤ gainΛ P) (hΛ1 : gainΛ P ≤ 1)
  {LG : LayeredGarden 1} (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal)
  {X₀ : RegChain} {q' q : ℕ} (F : TreeCohFacts LG X₀ q' q) (hqq : q' ≤ q) (hqp : q ≤ p)
  (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox)

include O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 F hqq hqp hT'

/-- **The lower bounds of a tree**, by induction over the blocks of its chain, at `Λ₁ = 30d`. -/
theorem tree_lower_bounds30 : ∀ (m : ℕ) (R Y : RegChain) (LG' : LayeredGarden 1), X₀ = appendChain R Y →
    Y.size = 2 * m → m ≤ P.N (p + 1) ^ 4 → TreeLowState LG H Bd R.lonePath Y LG' →
    rN P.η (30 * P.d) 0 T' (fun ts k =>
        treeLeaves P.L P.γ P.δ LG' (fun z => H (botAddr R.lonePath z))
          ((layerAt LG ((0 : Fin 1), R.lonePath) : ℝ) + 1) (ts 1) k -
          lowAppT P.δ LG H q' R.lonePath Y (ts 1) k) ≤
        ENNReal.ofReal (3 ^ (m + 1) * (Ktr P.η * C ^ 2 * Lsq P) * (2 * C ^ 4 * Lsq P) ^ m * P.δ ^ m * gainΛ P *
          leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z))) ∧
      rN P.η (30 * P.d) 0 T' (fun ts k => lowAppT P.δ LG H q' R.lonePath Y (ts 1) k) ≤
        ENNReal.ofReal ((Ktr P.η * C ^ 2 * Lsq P) * (2 * C ^ 4 * Lsq P) ^ m * P.δ ^ m *
          leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z))) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro R Y LG' hXp hsize hmN S
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hL2 : 1 ≤ Lsq P := one_le_Lsq P hd
  have hLle : cLeib P.d (30 * P.d) ≤ Lsq P := cLeib_le_Lsq P hd
  have hC0 : 0 ≤ C := by linarith
  have hK0 : 0 ≤ Ktr P.η := Ktr_nonneg _
  have hβ0 : 0 ≤ leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) :=
    Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hT1 : ∀ ts ∈ T', ts 1 ≤ (q' : ℝ) + 1 := fun ts hts => snd_le_of_unitBox (hT' ts hts)
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
  have hup : u ≤ q := by
    by_cases hYn : Y = .nil
    · rw [hnil hYn]; exact hqq
    · exact F.high _ (TreeCohFacts.sub_suffix hXp (hroot hYn))
  set B := takeLayer LG ((0 : Fin 1), π) u Y with hBdef
  set D := dropLayer LG ((0 : Fin 1), π) u Y with hDdef
  have hXe : appendChain B D = Y := appendChain_take_drop LG _ u Y
  have hTA : TopAll LG u ((0 : Fin 1), π) B := topAll_takeLayer LG u _ Y
  have hEmbBD : ChainEmb LG.garden (appendChain B D) ζ ((0 : Fin 1), π) .leaf := by rw [hXe]; exact hEmb
  have hPLBD : ChainPairLayers LG (appendChain B D) ζ ((0 : Fin 1), π) := by rw [hXe]; exact hPL
  have hSMBD : SpineMono LG ((0 : Fin 1), π) (appendChain B D) := by rw [hXe]; exact hSM
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
    obtain ⟨hE, hJ, hM⟩ := O.tree u q' m (hup.trans hqp) hqu hmN Y hYwf hsize LG' S.dec hlay' _ _ S.ctrl
    obtain ⟨hEb, hAb⟩ := tree_bottom_bounds30 P Y LG' (fun z => H (botAddr π z)) hd hL hη0 hη2 hδ hqu hsize S.dec _
      S.ctrl (by positivity : 0 ≤ C * C ^ m * leafSizeProduct LG' (fun z => Bd (botAddr π z)))
      (by positivity : 0 ≤ C * C ^ m) hE hJ hM T' b₀ hT'
    rw [S.sig] at hEb hAb
    have heq : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        treeLeaves P.L P.γ P.δ LG' (fun z => H (botAddr π z)) ((u : ℝ) + 1) (ts 1) k -
          lowAppT P.δ LG H q' π Y (ts 1) k =
        treeLeaves P.L P.γ P.δ LG' (fun z => H (botAddr π z)) ((u : ℝ) + 1) (ts 1) k -
          LeafApp.tree P.δ u (fun z => H (botAddr π z)) Y ζ ((u : ℝ) + 1) (ts 1) k := fun ts hts k _ => by
      rw [lowAppT_base P.δ LG H hu.symm hqu hTAY (hT1 ts hts) k]
    have heqA : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        lowAppT P.δ LG H q' π Y (ts 1) k =
          LeafApp.tree P.δ u (fun z => H (botAddr π z)) Y ζ ((u : ℝ) + 1) (ts 1) k := fun ts hts k _ => by
      rw [lowAppT_base P.δ LG H hu.symm hqu hTAY (hT1 ts hts) k]
    constructor
    · refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 0) T' Set.univ heq).trans_le (hEb.trans ?_)
      exact ENNReal.ofReal_le_ofReal (absorb_base_err30 hC hδ hΛ0 hβ0 hL2 hK0 m)
    · refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 0) T' Set.univ heqA).trans_le (hAb.trans ?_)
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ (absorb_base_app30 hC hδ hβ0 hL2 hK0 m))
      gcongr
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
    have hlow'' : q' ≤ layerAt LG ((0 : Fin 1), π ++ B.lonePath) := by
      obtain ⟨m', Qr', Qg', inner', rest', hD'⟩ :
          ∃ m' Qr' Qg' inner' rest', D = .pair m' Qr' Qg' inner' rest' := by
        cases hDc : D with
        | nil => exact absurd hDc hDn
        | pair m' Qr' Qg' inner' rest' => exact ⟨m', Qr', Qg', inner', rest', rfl⟩
      apply F.low
      apply TreeCohFacts.sub_suffix hXp
      rw [← hXe]
      apply chainNodesSet_append_right B D ζ ((0 : Fin 1), π)
      rw [hD']
      exact PL234.root_mem_chainNodesSet _ _ _ _ _ _ _
    have hqu' : q' < u := lt_of_le_of_lt hlow'' hlt
    obtain ⟨G₁, LG'', hdec₁, hsig₁, hlay₁, hctrl₁, S'', hβ, hK⟩ :=
      tree_block_step S P.L P.γ P.δ hd hL hYwf hDn hlt hBlay
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
    -- the tree slice
    set HT := LeafApp.sliceProfiles LG H ((0 : Fin 1), π) u Y with hHT
    set BT : (Fin 1 × Path) → NNReal := fun z => Bd (LeafApp.sliceAddress LG ((0 : Fin 1), π) u Y z.2) with hBT
    have hβT0 : 0 ≤ leafSizeProduct G₁ BT := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    obtain ⟨hET, hJT, hMT⟩ :=
      O.tree u _ nB (hup.trans hqp) hlt.le (by omega) B hwfBD.1 hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
    have hmid := tree_middle_bounds30 P B G₁ HT hd hL hη0 hη1 hδ hlt hBsize hdec₁ hlay₁ BT hctrl₁
      (by positivity) (by positivity) (by positivity) hET hJT hMT
    rw [hsig₁] at hmid
    have hsl : SourceApp.chainSlice LG ((0 : Fin 1), π) u Y = B :=
      chainSlice_eq_take LG _ Y hSM fun _ => le_refl _
    have ha_eq : ∀ k, sliceFactorT P.δ LG H π Y u k = LeafApp.tree P.δ u HT B ζ ((u : ℝ) + 1) u k := by
      intro k
      unfold sliceFactorT
      rw [hsl]
    -- the induction hypothesis on the rest
    have hXp' : X₀ = appendChain (appendChain R B) D := by rw [appendChain_assoc, hXe]; exact hXp
    have hlp : (appendChain R B).lonePath = π ++ B.lonePath := appendChain_lonePath R B
    have S''' : TreeLowState LG H Bd (appendChain R B).lonePath D LG'' := by rw [hlp]; exact S''
    obtain ⟨hE₂, hA₂⟩ := ih m₂ (by omega) (appendChain R B) D LG'' hXp' hsz₂ (by omega) S'''
    rw [hlp] at hE₂ hA₂
    have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ B.lonePath) z)) :=
      Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hstep := restr_step30 (θ := P.η) hΛ hd 0 T'
      (fun k => treeLeaves P.L P.γ P.δ G₁ HT ((u : ℝ) + 1) u k)
      (fun k => LeafApp.tree P.δ u HT B ζ ((u : ℝ) + 1) u k)
      (fun ts k => treeLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr (π ++ B.lonePath) z))
        ((layerAt LG ((0 : Fin 1), π ++ B.lonePath) : ℝ) + 1) (ts 1) k)
      (fun ts k => lowAppT P.δ LG H q' (π ++ B.lonePath) D (ts 1) k)
      (by positivity) (by positivity) (by positivity) (by positivity)
      hmid.1 hmid.2 hE₂ hA₂
    have hsplit := lowAppT_split P.δ LG H π Y hu.symm (spineMono_append_right LG B D _ hSMBD) hqu' hlow'' hlt
    have heq : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        treeLeaves P.L P.γ P.δ LG' (fun z => H (botAddr π z)) ((u : ℝ) + 1) (ts 1) k -
          lowAppT P.δ LG H q' π Y (ts 1) k =
        ((fun k => treeLeaves P.L P.γ P.δ G₁ HT ((u : ℝ) + 1) u k) k *
          (fun ts k => treeLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr (π ++ B.lonePath) z))
            ((layerAt LG ((0 : Fin 1), π ++ B.lonePath) : ℝ) + 1) (ts 1) k) ts k -
          (fun k => LeafApp.tree P.δ u HT B ζ ((u : ℝ) + 1) u k) k *
          (fun ts k => lowAppT P.δ LG H q' (π ++ B.lonePath) D (ts 1) k) ts k) := fun ts _ k _ => by
      rw [hK ((u : ℝ) + 1) (ts 1) k (by exact_mod_cast Nat.succ_le_succ hlt.le), hsplit (ts 1) k, ha_eq k]
    have heqA : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        lowAppT P.δ LG H q' π Y (ts 1) k =
        ((fun k => LeafApp.tree P.δ u HT B ζ ((u : ℝ) + 1) u k) k *
          (fun ts k => lowAppT P.δ LG H q' (π ++ B.lonePath) D (ts 1) k) ts k) := fun ts _ k _ => by
      rw [hsplit (ts 1) k, ha_eq k]
    have habs := absorb_step (D₀ := 2 * C ^ 4 * Lsq P) (M₀ := Ktr P.η * C ^ 2 * Lsq P) (m₂ := m₂)
      (ε := Lsq P * (C * (C * P.δ) ^ nB * gainΛ P * leafSizeProduct G₁ BT))
      (α := Lsq P * (P.δ ^ nB * 2 ^ nB * (C * C ^ nB) * (C * C ^ nB * leafSizeProduct G₁ BT)))
      (by positivity) (by positivity) hδ hΛ0 hΛ1 hβT0 hβ₂0 (by positivity) (by positivity)
      (absorb_tree_err30 hC hδ hΛ0 hβT0 hL2 hnB1) (absorb_tree_app30 hC hδ hβT0 hL2 hnB1) le_rfl le_rfl
      (by positivity) (by positivity) hnB1
    rw [← hmm, ← hβ] at habs
    constructor
    · exact (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 0) T' Set.univ heq).trans_le
        (hstep.1.trans (ENNReal.ofReal_le_ofReal
          (((mul_le_mul_of_nonneg_right hLle (by positivity)).trans_eq (by ring)).trans habs.1)))
    · exact (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 0) T' Set.univ heqA).trans_le
        (hstep.2.trans (ENNReal.ofReal_le_ofReal
          (((mul_le_mul_of_nonneg_right hLle (by positivity)).trans_eq (by ring)).trans habs.2)))

end Induction

end WaveTurbulence.PL2330
