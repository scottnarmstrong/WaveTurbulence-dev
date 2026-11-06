/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Absorb
public import WaveTurbulence.Foundations.Spine.PL234Draft.CoupleInduction

/-!
# Prop 6.1 at `Λ₁ = 30d`, `q > q'`, couples: the induction over the blocks of the `+` chain (PL23-30D)

**`lower_bounds30`** is `PL234.lower_bounds` in the norm `𝔛^{η,30d,30d}`: for every lower state (a suffix `X` of the
`+` chain below `(0, π)`), on any target box mapped into the unit box by `t ↦ t − (·, q')`, the error and the
leading term of the lower couple satisfy `≤ 3^{m+1} M₀ D₀^m δ^m Λ β` and `≤ M₀ D₀^m δ^m β`, with `L = (2d)^{30d}`,
`M₀ = K_tr C² L`, `D₀ = 2C⁴L`, `β = ∏ B_leaf`.
-/

@[expose] public section

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL2330

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.Reg WaveTurbulence.Links

section Induction

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1) (hη2 : P.η ≤ 1 - P.η) (hδ : 0 ≤ P.δ)
  (hΛ0 : 0 ≤ gainΛ P) (hΛ1 : gainΛ P ≤ 1)
  {LG : LayeredGarden 2} (H : LeafProfiles 2 P.d) (Bd : (Fin 2 × Path) → NNReal)
  {Xp Xm : RegChain} {Qlp : RegCpl} {q' : ℕ} (F : CohFacts LG Xp Xm Qlp q' p)
  (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox)

include O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 F hT'

/-- **The lower bounds**, by induction over the blocks of the `+` chain, at `Λ₁ = 30d`. -/
theorem lower_bounds30 : ∀ (m : ℕ) (R X : RegChain) (LG' : LayeredGarden 2), Xp = appendChain R X →
    (SourceApp.closeCouple X Xm Qlp).size = 2 * m → m ≤ P.N (p + 1) ^ 4 →
    LowState LG H Bd Xm Qlp R.lonePath X LG' →
    rN P.η (30 * P.d) (30 * P.d) T' (fun ts k =>
        coupleLeaves P.L P.γ P.δ LG' (fun z => H (botAddr R.lonePath z))
          ((layerAt LG ((0 : Fin 2), R.lonePath) : ℝ) + 1) (ts 1) k -
          lowApp P.δ LG H Xm Qlp q' R.lonePath X (ts 1) k) ≤
        ENNReal.ofReal (3 ^ (m + 1) * (Ktr P.η * C ^ 2 * Lsq P) *
          (2 * C ^ 4 * Lsq P) ^ m * P.δ ^ m * gainΛ P *
          leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z))) ∧
      rN P.η (30 * P.d) (30 * P.d) T' (fun ts k => lowApp P.δ LG H Xm Qlp q' R.lonePath X (ts 1) k) ≤
        ENNReal.ofReal ((Ktr P.η * C ^ 2 * Lsq P) *
          (2 * C ^ 4 * Lsq P) ^ m * P.δ ^ m *
          leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z))) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro R X LG' hXp hsize hmN S
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hLb : 1 ≤ Lsq P := one_le_Lsq P hd
  have hLle : cLeib P.d (30 * P.d) ≤ Lsq P := cLeib_le_Lsq P hd
  set Lb := Lsq P with hLbdef
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
    obtain ⟨hEb, hAb⟩ := couple_bottom_bounds30 P (SourceApp.closeCouple X Xm Qlp) LG'
      (fun z => H (botAddr R.lonePath z)) hd hL hη0 hη2 hδ hsize S.dec _ S.ctrl
      (by positivity : 0 ≤ C * C ^ m * leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)))
      (by positivity : 0 ≤ C * C ^ m) hE hJ hM T' b₀ hT'
    have heq : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        (coupleLeaves P.L P.γ P.δ LG' (fun z => H (botAddr R.lonePath z))
          ((layerAt LG ((0 : Fin 2), R.lonePath) : ℝ) + 1) (ts 1) k -
          lowApp P.δ LG H Xm Qlp q' R.lonePath X (ts 1) k) =
        (coupleLeaves P.L P.γ P.δ LG' (fun z => H (botAddr R.lonePath z)) (q' + 1) (ts 1) k -
          LeafApp.couple P.δ q' (fun z => H (botAddr R.lonePath z)) (SourceApp.closeCouple X Xm Qlp)
            (q' + 1) (ts 1) k) := fun ts _ k _ => by
      rw [lowApp_base P H hu hTA, hu]
    have heqA : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        lowApp P.δ LG H Xm Qlp q' R.lonePath X (ts 1) k =
        LeafApp.couple P.δ q' (fun z => H (botAddr R.lonePath z)) (SourceApp.closeCouple X Xm Qlp)
            (q' + 1) (ts 1) k := fun ts _ k _ => by
      rw [lowApp_base P H hu hTA]
    constructor
    · refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) T' Set.univ heq).trans_le (hEb.trans ?_)
      exact ENNReal.ofReal_le_ofReal (absorb_base_err30 hC hδ hΛ0 hβ0 hLb hK0 m)
    · refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) T' Set.univ heqA).trans_le (hAb.trans ?_)
      apply ENNReal.ofReal_le_ofReal
      calc 2 ^ m * (cLeib P.d (30 * P.d) * (P.δ ^ m * (C * C ^ m * leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)))) *
            (Ktr P.η * (C * C ^ m)))
          ≤ 2 ^ m * (Lb * (P.δ ^ m * (C * C ^ m * leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)))) *
            (Ktr P.η * (C * C ^ m))) := by gcongr
        _ ≤ (Ktr P.η * C ^ 2 * Lb) * (2 * C ^ 4 * Lb) ^ m * P.δ ^ m *
            leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) :=
            absorb_base_app30 hC hδ hβ0 hLb hK0 m
        _ = _ := rfl
  · push Not at hbase
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
        exact PL234.root_mem_chainNodesSet _ _ _ _ _ _ _
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
      | pair m' Qr' Qg' inner' rest' => exact PL234.root_mem_chainNodesSet _ _ _ _ _ _ _
    have hBwf : B.wf = true := (wf_split (hXe ▸ hwf2 : (RegCpl.type2 (appendChain B D) Xm Qlp).wf = true)).1
    set HT := LeafApp.sliceProfiles LG H ((0 : Fin 2), π) u X with hHT
    set BT : (Fin 1 × Path) → NNReal := fun z => Bd (LeafApp.sliceAddress LG ((0 : Fin 2), π) u X z.2) with hBT
    have hβT0 : 0 ≤ leafSizeProduct G₁ BT := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    obtain ⟨hET, hJT, hMT⟩ := O.tree u _ nB hup hlt.le (by omega) B hBwf hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
    have hmid := tree_middle_bounds30 P B G₁ HT hd hL hη0 hη1 hδ hlt hBsize hdec₁ hlay₁ BT hctrl₁
      (by positivity) (by positivity) (by positivity) hET hJT hMT
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
    have hstep := restr_step30 (θ := P.η) hΛ hd (30 * P.d) T'
      (fun k => treeLeaves P.L P.γ P.δ G₁ HT ((u : ℝ) + 1) u k)
      (fun k => LeafApp.tree P.δ u HT B 1 ((u : ℝ) + 1) u k)
      (fun ts k => coupleLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr (π ++ B.lonePath) z))
        ((layerAt LG ((0 : Fin 2), π ++ B.lonePath) : ℝ) + 1) (ts 1) k)
      (fun ts k => lowApp P.δ LG H Xm Qlp q' (π ++ B.lonePath) D (ts 1) k)
      (by positivity) (by positivity) (by positivity) (by positivity)
      hmid.1 hmid.2 hE₂ hA₂
    have hsplit := lowApp_split P.δ LG H Xm Qlp π X hu.symm hqu hXn hSM
      (spineMono_append_right LG B D _ hSMBD) hlow'' hlt
    have heq : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        (coupleLeaves P.L P.γ P.δ LG' (fun z => H (botAddr π z)) ((u : ℝ) + 1) (ts 1) k -
          lowApp P.δ LG H Xm Qlp q' π X (ts 1) k) =
        ((fun k => treeLeaves P.L P.γ P.δ G₁ HT ((u : ℝ) + 1) u k) k *
          (fun ts k => coupleLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr (π ++ B.lonePath) z))
            ((layerAt LG ((0 : Fin 2), π ++ B.lonePath) : ℝ) + 1) (ts 1) k) ts k -
          (fun k => LeafApp.tree P.δ u HT B 1 ((u : ℝ) + 1) u k) k *
          (fun ts k => lowApp P.δ LG H Xm Qlp q' (π ++ B.lonePath) D (ts 1) k) ts k) := fun ts _ k _ => by
      rw [hK ((u : ℝ) + 1) (ts 1) k (by exact_mod_cast Nat.succ_le_succ hlt.le), hsplit (ts 1) k, ha_eq k]
    have heqA : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        lowApp P.δ LG H Xm Qlp q' π X (ts 1) k =
        ((fun k => LeafApp.tree P.δ u HT B 1 ((u : ℝ) + 1) u k) k *
          (fun ts k => lowApp P.δ LG H Xm Qlp q' (π ++ B.lonePath) D (ts 1) k) ts k) := fun ts _ k _ => by
      rw [hsplit (ts 1) k, ha_eq k]
    have hε := absorb_tree_err30 hC hδ hΛ0 hβT0 hLb hnB1
    have hα := absorb_tree_app30 hC hδ hβT0 hLb hnB1
    have habs := absorb_step (D₀ := 2 * C ^ 4 * Lb) (M₀ := Ktr P.η * C ^ 2 * Lb) (m₂ := m₂)
      (ε := Lb * (C * (C * P.δ) ^ nB * gainΛ P * leafSizeProduct G₁ BT))
      (α := Lb * (P.δ ^ nB * 2 ^ nB * (C * C ^ nB) * (C * C ^ nB * leafSizeProduct G₁ BT)))
      (by positivity) (by positivity) hδ hΛ0 hΛ1 hβT0 hβ₂0 (by positivity) (by positivity)
      hε hα le_rfl le_rfl (by positivity) (by positivity) hnB1
    rw [← hmm, ← hβ] at habs
    constructor
    · refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) T' Set.univ heq).trans_le
        (hstep.1.trans (ENNReal.ofReal_le_ofReal (((mul_le_mul_of_nonneg_right hLle (by positivity)).trans_eq (by ring)).trans habs.1)))
    · refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) T' Set.univ heqA).trans_le
        (hstep.2.trans (ENNReal.ofReal_le_ofReal (((mul_le_mul_of_nonneg_right hLle (by positivity)).trans_eq (by ring)).trans habs.2)))

end Induction

end WaveTurbulence.PL2330
