/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.SepCouple

/-!
# Prop 6.1, `q > q'`, trees: the separated representation of the explicit leading term

* **`tree_lower_sep`**: the lower leading term of every lower state of a coherent tree has a separated
  representation with `(K_J^{m+1}, K_M^{m+1} β)`;
* **`tree_sep_gt`**: `LeafApp.coherentTree` on `{(t,s) ∈ [q,q+1]×[q',q'+1], s < t}` has one with
  `(K_J^{n+1}, K_M^{n+1} β)`.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

theorem timeBoxGt_closure_interior (q q' : ℕ) :
    ∀ t ∈ timeBoxGt (q : ℝ) q', t ∈ closure (interior (timeBoxGt (q : ℝ) q')) :=
  fun _ ht => mem_closure_interior_timeBoxGt ht

section Induction

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1)
  {LG : LayeredGarden 1} (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal)
  {X₀ : RegChain} {q' q : ℕ} (F : TreeCohFacts LG X₀ q' q) (hqq : q' ≤ q) (hqp : q ≤ p)
  (T' : Set (Fin 2 → ℝ)) (hTc : ∀ t ∈ T', t ∈ closure (interior T')) (b₀ : ℝ)
  (hT' : ∀ ts ∈ T', ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox)

include O hC hd hL hη0 hη1 F hqq hqp hTc hT'

/-- **The separated lower leading term of a tree**, by induction over the blocks of its chain. -/
theorem tree_lower_sep : ∀ (m : ℕ) (R Y : RegChain) (LG' : LayeredGarden 1), X₀ = appendChain R Y →
    Y.size = 2 * m → m ≤ P.N (p + 1) ^ 4 → TreeLowState LG H Bd R.lonePath Y LG' →
    SepRep (1 - P.η) P.δ (30 * P.d) 0 m T'
      (fun ts k => lowAppT P.δ LG H q' R.lonePath Y (ts 1) k)
      (KJ (1 - P.η) C ^ (m + 1))
      (KM (30 * P.d) P.d C ^ (m + 1) * leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z))) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro R Y LG' hXp hsize hmN S
  have hθ : 0 ≤ 1 - P.η := by linarith
  have hθ1 : 1 - P.η ≤ 1 := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hA : 30 * P.d ≠ 0 := by omega
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
    | pair m' Qr' Qg' inner' rest' => exact root_mem_chainNodesSet _ _ _ _ _ _ _
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
  · -- the base: a single block in layer `u`
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
    obtain ⟨-, hJ, hM⟩ := O.tree u q' m (hup.trans hqp) hqu hmN Y hYwf hsize LG' S.dec hlay' _ _ S.ctrl
    rw [S.sig] at hM
    have hsep := sep_bottom_tree P hη1 (fun z => H (botAddr π z)) Y ζ hqu hsize hJ hM T' b₀ hT'
    refine (hsep.congr fun ts hts k => lowAppT_base P.δ LG H hu.symm hqu hTAY (hT1 ts hts) k).mono
      (by simpa [mul_comm] using sep_base_J hθ hC m) (sep_base_M _ hd hC hβ0 m)
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
      exact root_mem_chainNodesSet _ _ _ _ _ _ _
    have hqu' : q' < u := lt_of_le_of_lt hlow'' hlt
    obtain ⟨G₁, LG'', hdec₁, hsig₁, hlay₁, hctrl₁, S'', hβ, -⟩ :=
      tree_block_step S P.L P.γ P.δ hd hL hYwf hDn hlt hBlay
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
    set HT := LeafApp.sliceProfiles LG H ((0 : Fin 1), π) u Y with hHT
    set BT : (Fin 1 × Path) → NNReal := fun z => Bd (LeafApp.sliceAddress LG ((0 : Fin 1), π) u Y z.2) with hBT
    have hβT0 : 0 ≤ leafSizeProduct G₁ BT := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    obtain ⟨-, hJT, hMT⟩ :=
      O.tree u _ nB (hup.trans hqp) hlt.le (by omega) B hwfBD.1 hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
    rw [hsig₁] at hMT
    have hmid := sep_middle_tree P hη1 HT B ζ hlt hBsize (by positivity) hJT hMT T' ![b₀, -(q' : ℝ)] hT'
    have hsl : SourceApp.chainSlice LG ((0 : Fin 1), π) u Y = B :=
      chainSlice_eq_take LG _ Y hSM fun _ => le_refl _
    have hXp' : X₀ = appendChain (appendChain R B) D := by rw [appendChain_assoc, hXe]; exact hXp
    have hlp : (appendChain R B).lonePath = π ++ B.lonePath := appendChain_lonePath R B
    have S''' : TreeLowState LG H Bd (appendChain R B).lonePath D LG'' := by rw [hlp]; exact S''
    have hrest := ih m₂ (by omega) (appendChain R B) D LG'' hXp' hsz₂ (by omega) S'''
    rw [hlp] at hrest
    have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ B.lonePath) z)) :=
      Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hprod := SepRep.mul hθ hTc hd hA (mul_nonneg (by positivity) (Ktr_nonneg _)) (by positivity)
      (mul_nonneg (pow_nonneg (zero_le_one.trans (one_le_KM _ hd hC)) _) hβ₂0) hmid hrest
    have hsplit := lowAppT_split P.δ LG H π Y hu.symm (spineMono_append_right LG B D _ hSMBD) hqu' hlow'' hlt
    rw [← hmm] at hprod
    refine (hprod.congr fun ts _ k => ?_).mono ?_ ?_
    · rw [hsplit (ts 1) k]
      unfold sliceFactorT
      rw [hsl]
    · rw [hmm]
      exact sep_step_J hθ hθ1 hC hnB1
    · rw [hβ, hmm]
      exact sep_step_M _ hd hC hβT0 hβ₂0 hnB1

end Induction

section Top

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1)

include O hC hd hL hη0 hη1

omit hL hη0 in
/-- **A single block in layer `q`.** -/
theorem tree_sep_single {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (F : TreeCohFacts LG X q' q)
    (hTAX : TopAll LG q ((0 : Fin 1), []) X)
    (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    SepRep (1 - P.η) P.δ (30 * P.d) 0 n (timeBoxGt q q')
      (fun ts k => LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k)
      (KJ (1 - P.η) C ^ (n + 1)) (KM (30 * P.d) P.d C ^ (n + 1) * leafSizeProduct LG Bd) := by
  have hθ : 0 ≤ 1 - P.η := by linarith
  set ζ := LG.garden.sig 0 with hζ
  have hβ0 : 0 ≤ leafSizeProduct LG Bd := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hC0 : 0 ≤ C := by linarith
  have hts1 : ∀ ts ∈ timeBoxGt (q : ℝ) q', ts 1 ≤ (q' : ℝ) + 1 := fun ts hts => hts.1.2.2
  have hq1 : (q' : ℝ) + 1 ≤ q := by exact_mod_cast hqq
  have hEmb := ChainEmb.of_decodesTree F.dec
  have hXlay : ∀ z ∈ chainNodesSet X ζ ((0 : Fin 1), []), layerAt LG z = q :=
    chainNodes_layer_of_topAll hEmb F.pl hTAX
  have hlay := layer_single_block F.dec F.lone hXlay
  obtain ⟨-, hJ, hM⟩ := O.tree q q' n hqp hqq.le hnN X F.wf hsize LG F.dec hlay H Bd hH
  have hprof : LeafApp.sliceProfiles LG H ((0 : Fin 1), []) q X = H := by
    funext z
    unfold LeafApp.sliceProfiles
    rw [sliceAddress_of_topAll LG q X _ _ hTAX]
    obtain ⟨j, p⟩ := z
    fin_cases j
    simp [addrExt]
  have hsep := sepRep_tree (θ := 1 - P.η) (δ := P.δ) (T := timeBoxGt (q : ℝ) q') (q : ℝ) H X ζ hsize
    (fun ts => ts 0) (fun ts => ts 1) (continuous_apply 0) (continuous_apply 1)
    (cJ := C * C ^ n) (fun hdom => (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (1 - P.η) _ _
      (fun ts (_ : Unit) => (X.JBtree q (ts 0) (ts 1) : ℂ))).symm.le.trans (hJ hdom)) hM
  refine (hsep.congr fun ts hts k => ?_).mono ?_ (sep_base_M _ hd hC hβ0 n)
  · have hsq : ts 1 ≤ (q : ℝ) := (hts1 ts hts).trans hq1
    rw [coherentTree_gt_eq P.δ LG H X hqq]
    rw [Finset.prod_eq_one fun r hr => by
      unfold sliceFactorT
      rw [chainSlice_of_topNe LG r X _ (TopAll.topNe LG (by simp only [Finset.mem_Ioo] at hr; omega) _ _ hTAX)]
      exact LeafApp.tree_nil _ _ _ _ _ _ _, one_mul]
    unfold lowBotT
    rw [chainSlice_of_topNe LG q' X _ (TopAll.topNe LG (by omega) _ _ hTAX), LeafApp.tree_nil, mul_one,
      chainSlice_of_topAll LG q X _ hTAX, hprof, ← LeafApp.tree_lower_eq P.δ q H X ζ (ts 0) hsq k]
  · have h1 := sep_base_J hθ hC n
    have hK := one_le_Ktr hθ
    have : C * C ^ n ≤ Ktr (1 - P.η) * (C * C ^ n) := le_mul_of_one_le_left (by positivity) hK
    linarith

/-- **The top block in layer `q`, and the rest.** -/
theorem tree_sep_top {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (F : TreeCohFacts LG X q' q)
    (htop : layerAt LG ((0 : Fin 1), []) = q) (hXn : X ≠ .nil)
    (hDn : dropLayer LG ((0 : Fin 1), []) q X ≠ .nil)
    (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    SepRep (1 - P.η) P.δ (30 * P.d) 0 n (timeBoxGt q q')
      (fun ts k => LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k)
      (KJ (1 - P.η) C ^ (n + 1)) (KM (30 * P.d) P.d C ^ (n + 1) * leafSizeProduct LG Bd) := by
  have hθ : 0 ≤ 1 - P.η := by linarith
  have hθ1 : 1 - P.η ≤ 1 := by linarith
  have hA : 30 * P.d ≠ 0 := by omega
  have hC0 : 0 ≤ C := by linarith
  set ζ := LG.garden.sig 0 with hζ
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
  obtain ⟨G₁, LG'', hdec₁, hsig₁, hlay₁, hctrl₁, S'', hβ, -⟩ :=
    tree_block_step S₀ P.L P.γ P.δ hd hL F.wf hDn hlt hBlay'
  simp only [List.nil_append] at hlay₁ S'' hβ
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
  obtain ⟨-, hJT, hMT⟩ :=
    O.tree q r'' nB hqp hlt.le (by omega) B hwfBD.1 hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
  rw [hsig₁] at hMT
  have hT₁ : ∀ ts ∈ timeBoxGt (q : ℝ) q', ts + ![-(q : ℝ), -(q' : ℝ)] ∈ (Layered.unitBox : Set (Fin 2 → ℝ)) :=
    hT
  have htopsep := sep_top_tree P hη1 HT B ζ hlt hBsize hJT hMT (timeBoxGt (q : ℝ) q') (-(q' : ℝ)) hT₁
  have hrest := tree_lower_sep P O hC hd hL hη0 hη1 H Bd F hqq.le hqp (timeBoxGt (q : ℝ) q')
    (timeBoxGt_closure_interior q q') (-(q : ℝ)) hT m₂ B D LG'' hXe.symm hsz₂ (by omega) S''
  have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) :=
    Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hprod := SepRep.mul hθ (timeBoxGt_closure_interior q q') hd hA (mul_nonneg (Ktr_nonneg _) (by positivity))
    (by positivity) (mul_nonneg (pow_nonneg (zero_le_one.trans (one_le_KM _ hd hC)) _) hβ₂0) htopsep hrest
  rw [← hnn'] at hprod
  refine (hprod.congr fun ts _ k => ?_).mono ?_ ?_
  · have hrest' := lowRestT_eq P.δ LG H [] X (u := q) hSMD hqq hlow'' hlt (ts 1) k
    simp only [List.nil_append] at hrest'
    rw [coherentTree_gt_eq P.δ LG H X hqq, hsl, ← hrest']
    ring
  · have h1 : 2 ^ (1 - P.η) * (Ktr (1 - P.η) * (C * C ^ nB)) * KJ (1 - P.η) C ^ (m₂ + 1) =
        2 ^ (1 - P.η) * (C * C ^ nB * Ktr (1 - P.η)) * KJ (1 - P.η) C ^ (m₂ + 1) := by ring
    rw [h1, hnn']
    exact sep_step_J hθ hθ1 hC hnB1
  · rw [hβe, hnn']
    exact sep_step_M _ hd hC hβT0 hβ₂0 hnB1

/-- **The root below `q`.** -/
theorem tree_sep_low {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (F : TreeCohFacts LG X q' q)
    (hr₁lt : layerAt LG ((0 : Fin 1), []) < q)
    (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    SepRep (1 - P.η) P.δ (30 * P.d) 0 n (timeBoxGt q q')
      (fun ts k => LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k)
      (KJ (1 - P.η) C ^ (n + 1)) (KM (30 * P.d) P.d C ^ (n + 1) * leafSizeProduct LG Bd) := by
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
  have hsep := tree_lower_sep P O hC hd hL hη0 hη1 H Bd F hqq.le hqp (timeBoxGt (q : ℝ) q')
    (timeBoxGt_closure_interior q q') (-(q : ℝ)) hT n .nil X LG rfl hsize hnN S₀
  simp only [RegChain.lonePath] at hsep
  rw [hBe] at hsep
  refine hsep.congr fun ts _ k => ?_
  have hslq : SourceApp.chainSlice LG ((0 : Fin 1), []) q X = .nil :=
    chainSlice_eq_nil LG _ X F.sm fun _ => hr₁lt
  rw [coherentTree_gt_eq P.δ LG H X hqq, hslq, LeafApp.tree_nil, mul_one]
  unfold lowAppT
  congr 1
  rw [← hr₁, Ioo_eq_Ico_succ, Ioo_eq_Ico_succ,
    ← prod_Ico_consecutive _ (show q' + 1 ≤ r₁ + 1 by omega) (show r₁ + 1 ≤ q by omega)]
  rw [Finset.prod_eq_one (s := Ico (r₁ + 1) q) fun r hr => by
    unfold sliceFactorT
    rw [chainSlice_eq_nil LG _ X F.sm fun _ => by simp only [Finset.mem_Ico] at hr; omega]
    exact LeafApp.tree_nil _ _ _ _ _ _ _, mul_one]

/-- **Prop 6.1, trees, `q > q'`: the separated representation** (TARGET prooflayer1-2). -/
theorem tree_sep_gt {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (X : RegChain) (hsize : X.size = 2 * n) (LG : LayeredGarden 1) (hcoh : IsCoherentTreeAt p q q' X LG)
    (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    SepRep (1 - P.η) P.δ (30 * P.d) 0 n (timeBoxGt q q')
      (fun ts k => LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k)
      (KJ (1 - P.η) C ^ (n + 1)) (KM (30 * P.d) P.d C ^ (n + 1) * leafSizeProduct LG Bd) := by
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
      exact tree_sep_single P O hC hd hη1 hqq hqp hnN X hsize LG F hTAX H Bd hH
    · exact tree_sep_top P O hC hd hL hη0 hη1 hqq hqp hnN X hsize LG F htop hXn hDn H Bd hH
  · exact tree_sep_low P O hC hd hL hη0 hη1 hqq hqp hnN X hsize LG F (lt_of_le_of_ne hr₁q htop) H Bd hH

end Top

end WaveTurbulence.PL234
