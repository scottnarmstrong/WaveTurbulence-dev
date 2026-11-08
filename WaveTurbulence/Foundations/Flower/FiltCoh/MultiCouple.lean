/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiTreeGate
public import WaveTurbulence.Foundations.Spine.PL2330Draft.CoupleInd

/-! # FILT-COH: coherent regular couples across layers (bound only)

Main's induction over the blocks of the `+` chain of a type-2 couple (`PL2330.lower_bounds30`) and its case split
(`couple_err_type1_30`, `couple_err_type2_30`, `couple_same30`), for the kernel alone, from the single-layer
bounds (`TreeKOracle`, `CoupleKOracle`) and the traces of `MultiPieces`. -/

public section
open WaveTurbulence.Induct
open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltCoh

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.PL2330 WaveTurbulence.Reg WaveTurbulence.Links

/-- The single-layer couple bound used by the induction (the couple clause of `single_layer_bounds`). -/
@[expose] def CoupleKOracle (d : ℕ) (L γ δ θ : ℝ) (Nmax : ℕ) (C : ℝ) : Prop :=
  ∀ (r n : ℕ), n ≤ Nmax → ∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n →
    ∀ LG : LayeredGarden 2, Q.Decodes LG.garden → (∀ a, LG.layer a = r) →
    ∀ (H : LeafProfiles 2 d) (B : (Fin 2 × Path) → NNReal), LeafwiseControlled LG H B →
    XNormRestr θ (30 * d) (30 * d) (timeBox r r) Set.univ
      (fun ts k => coupleLeaves L γ δ LG H (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (C * (C * δ) ^ n * leafSizeProduct LG B)

section Induction

variable (P : WTParams) {θ : ℝ} {Nmax : ℕ} {C : ℝ} (OT : TreeKOracle P.d P.L P.γ P.δ θ Nmax C)
  (OC : CoupleKOracle P.d P.L P.γ P.δ θ Nmax C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hθ0 : 0 ≤ θ) (hδ : 0 ≤ P.δ)
  {LG : LayeredGarden 2} (H : LeafProfiles 2 P.d) (Bd : (Fin 2 × Path) → NNReal)
  {Xp Xm : RegChain} {Qlp : RegCpl} {q' p : ℕ} (F : CohFacts LG Xp Xm Qlp q' p)
  (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox)

include OT OC hC hd hL hθ0 hδ F hT'

/-- **The lower couple kernels**, by induction over the blocks of the `+` chain (bound-only
`PL2330.lower_bounds30`), with `G = K_tr(θ) · cLeib · C²`. -/
theorem couple_lower_kernel : ∀ (m : ℕ) (R X : RegChain) (LG' : LayeredGarden 2), Xp = appendChain R X →
    (SourceApp.closeCouple X Xm Qlp).size = 2 * m → m ≤ Nmax →
    LowState LG H Bd Xm Qlp R.lonePath X LG' →
    rN θ (30 * P.d) (30 * P.d) T' (fun ts k =>
        coupleLeaves P.L P.γ P.δ LG' (fun z => H (botAddr R.lonePath z))
          ((layerAt LG ((0 : Fin 2), R.lonePath) : ℝ) + 1) (ts 1) k) ≤
        ENNReal.ofReal ((Ktr θ * cLeib P.d (30 * P.d) * C ^ 2) *
          ((Ktr θ * cLeib P.d (30 * P.d) * C ^ 2) * P.δ) ^ m *
          leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z))) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro R X LG' hXp hsize hmN S
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hC0 : 0 ≤ C := by linarith
  have hK1 : 1 ≤ Ktr θ := one_le_Ktr hθ0
  have hK0 : 0 ≤ Ktr θ := Ktr_nonneg _
  have hLc : 1 ≤ cLeib P.d (30 * P.d) := one_le_cLeib hd _
  set G := Ktr θ * cLeib P.d (30 * P.d) * C ^ 2 with hGdef
  have hCG : C ≤ G := by
    have h1 : 1 * 1 * C ^ 1 ≤ Ktr θ * cLeib P.d (30 * P.d) * C ^ 2 :=
      mul_le_mul (mul_le_mul hK1 hLc zero_le_one (by linarith)) (pow_le_pow_right₀ hC (by norm_num))
        (by positivity) (by positivity)
    simpa using h1
  have hG0 : 0 ≤ G := hC0.trans hCG
  have hβ0 : 0 ≤ leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) :=
    Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  obtain ⟨hXwf, hmwf, hlwf, hlt2⟩ := F.wf_suffix hXp
  by_cases hbase : X = .nil ∨ layerAt LG ((0 : Fin 2), R.lonePath) ≤ q'
  · -- the base: a single-layer couple in layer `q'`
    obtain ⟨hu, hTA, hlayq⟩ := base_layers P F hXp S hbase
    have hwfc : (SourceApp.closeCouple X Xm Qlp).wf = true := closeCouple_wf hXwf hmwf hlwf hlt2
    have hE := OC q' m hmN _ hwfc hsize LG' S.dec hlayq _ _ S.ctrl
    have hEb := couple_bottom_kernel hd hL hθ0 S.dec S.ctrl hE T' b₀ hT'
    rw [hu]
    refine hEb.trans (ENNReal.ofReal_le_ofReal ?_)
    calc Ktr θ * (C * (C * P.δ) ^ m * leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)))
        = (Ktr θ * C) * (C * P.δ) ^ m * leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) := by ring
      _ ≤ G * (G * P.δ) ^ m * leafSizeProduct LG' (fun z => Bd (botAddr R.lonePath z)) := by
          apply mul_le_mul_of_nonneg_right _ hβ0
          apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCG hδ) m)
            (by positivity) hG0
          calc Ktr θ * C = Ktr θ * 1 * C ^ 1 := by ring
            _ ≤ Ktr θ * cLeib P.d (30 * P.d) * C ^ 2 :=
                mul_le_mul (mul_le_mul_of_nonneg_left hLc hK0) (pow_le_pow_right₀ hC (by norm_num))
                  (by positivity) (by positivity)
  · simp only [not_or, not_le] at hbase
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
    have hBlay : ∀ z ∈ chainNodesSet B 1 ((0 : Fin 2), π), layerAt LG z = u :=
      chainNodes_layer_of_topAll (chainEmb_append_left hEmbBD)
        (chainPairLayers_append_left LG B D 1 _ hPLBD) hTA
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
    have hwf2 : (RegCpl.type2 X Xm Qlp).wf = true := by
      have hXnil : X.isNil = false := by cases X <;> simp_all [RegChain.isNil]
      simp [RegCpl.wf, hXwf, hmwf, hlwf, hlt2, hXnil]
    obtain ⟨G₁, LG'', hdec₁, hsig₁, hlay₁, hctrl₁, S'', hβ, hK⟩ :=
      couple_block_step S P.L P.γ P.δ hd hL hXn hwf2 hu.symm hlt hBlay
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
    have hBwf : B.wf = true := (wf_split (hXe ▸ hwf2 : (RegCpl.type2 (appendChain B D) Xm Qlp).wf = true)).1
    set HT := LeafApp.sliceProfiles LG H ((0 : Fin 2), π) u X with hHT
    set BT : (Fin 1 × Path) → NNReal := fun z => Bd (LeafApp.sliceAddress LG ((0 : Fin 2), π) u X z.2) with hBT
    have hβT0 : 0 ≤ leafSizeProduct G₁ BT := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hET := OT u _ nB hlt.le (by omega) B hBwf hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
    have hmid := tree_middle_kernel hd hL hθ0 hlt hdec₁ hlay₁ hctrl₁ hET
    -- the induction hypothesis on the rest
    have hXp' : Xp = appendChain (appendChain R B) D := by rw [appendChain_assoc, hXe]; exact hXp
    have hlp : (appendChain R B).lonePath = π ++ B.lonePath := appendChain_lonePath R B
    have S''' : LowState LG H Bd Xm Qlp (appendChain R B).lonePath D LG'' := by rw [hlp]; exact S''
    have hE₂ := ih m₂ (by omega) (appendChain R B) D LG'' hXp' hsz₂ (by omega) S'''
    rw [hlp] at hE₂
    have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ B.lonePath) z)) :=
      Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hstep := restr_mul_s_le hΛ hd (θ := θ) (30 * P.d) T'
      (c := fun k => treeLeaves P.L P.γ P.δ G₁ HT ((u : ℝ) + 1) u k)
      (fun ts k => coupleLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr (π ++ B.lonePath) z))
        ((layerAt LG ((0 : Fin 2), π ++ B.lonePath) : ℝ) + 1) (ts 1) k)
      (by positivity) hmid hE₂
    have heq : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        coupleLeaves P.L P.γ P.δ LG' (fun z => H (botAddr π z)) ((u : ℝ) + 1) (ts 1) k =
        (fun k => treeLeaves P.L P.γ P.δ G₁ HT ((u : ℝ) + 1) u k) k *
          (fun ts k => coupleLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr (π ++ B.lonePath) z))
            ((layerAt LG ((0 : Fin 2), π ++ B.lonePath) : ℝ) + 1) (ts 1) k) ts k := fun ts _ k _ => by
      rw [hK ((u : ℝ) + 1) (ts 1) k (by exact_mod_cast Nat.succ_le_succ hlt.le)]
    refine (restr_congr (θ := θ) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) T' Set.univ heq).trans_le (hstep.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have hab := absorb_kernel_step (c := cLeib P.d (30 * P.d)) (C := C) (G := G) (δ := P.δ)
      (βT := leafSizeProduct G₁ BT) (β₂ := leafSizeProduct LG'' (fun z => Bd (botAddr (π ++ B.lonePath) z)))
      (nB := nB) (m₂ := m₂) hLc hC (by
        calc cLeib P.d (30 * P.d) * C ^ 2 = 1 * cLeib P.d (30 * P.d) * C ^ 2 := by ring
          _ ≤ G := by
            rw [hGdef]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 (by positivity)) (by positivity))
      hδ hβT0 hβ₂0 hnB1
    rw [← hmm, ← hβ] at hab
    exact hab

end Induction

end WaveTurbulence.Flower.FiltCoh
