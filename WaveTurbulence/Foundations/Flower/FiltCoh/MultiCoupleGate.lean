/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiCouple
public import WaveTurbulence.Foundations.Spine.PL2330Draft.CoupleGate

/-! # FILT-COH: coherent regular couples `(q, q')`, any weight `θ ∈ [0, 1]` (bound only)

The case split of main's `PL2330.couple_err_gt30` and `couple_same30`, for the kernel alone. -/

public section
open WaveTurbulence.Induct
open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltCoh

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.PL2330 WaveTurbulence.Reg WaveTurbulence.Links

section Gate

variable (P : WTParams) {θ : ℝ} {Nmax : ℕ} {C : ℝ} (OT : TreeKOracle P.d P.L P.γ P.δ θ Nmax C)
  (OC : CoupleKOracle P.d P.L P.γ P.δ θ Nmax C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hδ : 0 ≤ P.δ)

include OT OC hC hd hL hθ0 hθ1 hδ

/-- **Coherent couples, type 2, `q' < q`.** -/
theorem couple_type2_kernel {p q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ Nmax)
    (Xp Xm : RegChain) (Qlp : RegCpl) (hsize : (RegCpl.type2 Xp Xm Qlp).size = 2 * n) (LG : LayeredGarden 2)
    (hcoh : IsCoherentCoupleAt p q q' (.type2 Xp Xm Qlp) LG) (H : LeafProfiles 2 P.d)
    (Bd : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    rN θ (30 * P.d) (30 * P.d) (timeBox q q') (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (treeG P.d θ C * (treeG P.d θ C * P.δ) ^ n * leafSizeProduct LG Bd) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  obtain ⟨hCG', hGG', hG1⟩ := le_treeG hd hθ0 hC
  set G' := treeG P.d θ C with hG'def
  set G := Ktr θ * cLeib P.d (30 * P.d) * C ^ 2 with hGdef
  have hC0 : 0 ≤ C := by linarith
  have hK1 : 1 ≤ Ktr θ := one_le_Ktr hθ0
  have hLc : 1 ≤ cLeib P.d (30 * P.d) := one_le_cLeib hd _
  have F := cohFacts_of_coherent hqq.le hqp hcoh
  have hQ := hcoh.2.1
  have hplain : LG.garden.IsPlain := hQ.1.1
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b := noFlowerParent_of_noFlower (not_flower_of_plain hplain)
  have hβ0 : 0 ≤ leafSizeProduct LG Bd := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hwf := F.wf
  have hnn : (Xp.isNil && Xm.isNil) = false := by
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hwf
    exact hwf.2
  have hcl : SourceApp.closeCouple Xp Xm Qlp = RegCpl.type2 Xp Xm Qlp := by
    unfold SourceApp.closeCouple
    rw [hnn]
    rfl
  have hHe : (fun z => H (botAddr [] z)) = H := funext fun z => by rw [botAddr_nil]
  have hBe : (fun z => Bd (botAddr [] z)) = Bd := funext fun z => by rw [botAddr_nil]
  have S₀ : LowState LG H Bd Xm Qlp RegChain.nil.lonePath Xp LG := by
    refine ⟨by rw [hcl]; exact hQ, fun z => by simp [RegChain.lonePath, botAddr_nil], ?_⟩
    show LeafwiseControlled LG (fun z => H (botAddr [] z)) (fun z => Bd (botAddr [] z))
    rw [hHe, hBe]
    exact hH
  have hsizeC : (SourceApp.closeCouple Xp Xm Qlp).size = 2 * n := by rw [hcl]; exact hsize
  have hT := timeBox_shift_unit q q'
  set r₁ := layerAt LG ((0 : Fin 2), []) with hr₁
  have hr₁q : r₁ ≤ q := root_le_type2 hqq.le hcoh
  by_cases htop : r₁ = q
  · have hXpn : Xp ≠ .nil := by
      intro hXpn
      have := F.lone_suffix (R := .nil) (X := Xp) rfl
      rw [hXpn] at this
      simp only [RegChain.lonePath, addrExt, List.append_nil] at this
      rw [← hr₁, htop] at this
      omega
    obtain ⟨hBlay, hlt, hlow'', hwf2, hSMD⟩ := block_facts F (R := .nil) rfl hXpn htop hqq
    simp only [RegChain.lonePath, List.nil_append] at hBlay hlt hlow'' hSMD
    set B := takeLayer LG ((0 : Fin 2), []) q Xp with hBdef
    set D := dropLayer LG ((0 : Fin 2), []) q Xp with hDdef
    set r'' := layerAt LG ((0 : Fin 2), B.lonePath) with hr''
    have hXe : appendChain B D = Xp := appendChain_take_drop LG _ q Xp
    obtain ⟨G₁, LG'', hdec₁, hsig₁, hlay₁, hctrl₁, S'', hβ, hK⟩ :=
      couple_block_step S₀ P.L P.γ P.δ hd hL hXpn hwf2 htop hlt hBlay
    simp only [RegChain.lonePath, List.nil_append] at hlay₁ S'' hβ hK
    have hsz : (RegCpl.type2 Xp Xm Qlp).size = B.size + (SourceApp.closeCouple D Xm Qlp).size := by
      rw [← hXe, closeCouple_size]
      simp only [RegCpl.size, appendChain_size]
      ring
    obtain ⟨nB, hnB⟩ := size_even_chain B
    obtain ⟨m₂, hm₂⟩ := size_even_cpl (SourceApp.closeCouple D Xm Qlp)
    have hBne : B ≠ .nil := by
      have := takeLayer_ne_nil LG Xp ((0 : Fin 2), []) hXpn
      rw [← hr₁, htop] at this
      exact this
    have hB2 := two_le_size_of_ne_nil B hBne
    have hBsize : B.size = 2 * nB := by omega
    have hsz₂ : (SourceApp.closeCouple D Xm Qlp).size = 2 * m₂ := by omega
    have hnn' : n = nB + m₂ := by omega
    have hnB1 : 1 ≤ nB := by omega
    have hBwf : B.wf = true :=
      (wf_split (hXe ▸ hwf2 : (RegCpl.type2 (appendChain B D) Xm Qlp).wf = true)).1
    set HT := LeafApp.sliceProfiles LG H ((0 : Fin 2), []) q Xp with hHT
    set BT : (Fin 1 × Path) → NNReal := fun z => Bd (LeafApp.sliceAddress LG ((0 : Fin 2), []) q Xp z.2)
      with hBT
    have hβT0 : 0 ≤ leafSizeProduct G₁ BT := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) :=
      Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    -- the top factor
    have hET := OT q r'' nB hlt.le (by omega) B hBwf hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
    have hX₁ := tree_top_kernel hd hL hθ0 hlt hdec₁ hlay₁ hctrl₁ hET (timeBox (q : ℝ) q') (-(q' : ℝ))
      (fun ts hts => hT ts hts)
    -- the lower factor
    have hX₂ := couple_lower_kernel P OT OC hC hd hL hθ0 hδ H Bd F (timeBox (q : ℝ) q') (-(q : ℝ)) hT
      m₂ B D LG'' hXe.symm hsz₂ (by omega) S''
    have hplain'' : LG''.garden.IsPlain := S''.dec.1.1
    have hcont : ∀ k, Continuous fun ts : Fin 2 → ℝ =>
        coupleLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z))
          ((layerAt LG ((0 : Fin 2), B.lonePath) : ℝ) + 1) (ts 1) k := fun k =>
      continuous_coupleLeaves_snd P.L P.γ P.δ LG'' _ hplain'' _ k (S''.ctrl.summable_coset hd hL k)
    have hprod := restr_mul_le hΛ hd hθ0 0 (30 * P.d) (B := timeBox (q : ℝ) q')
      (fun ts hts => by rw [closure_interior_timeBox]; exact hts)
      (fun ts k => treeLeaves P.L P.γ P.δ G₁ HT (ts 0) q k)
      (fun ts k => coupleLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z))
        ((layerAt LG ((0 : Fin 2), B.lonePath) : ℝ) + 1) (ts 1) k) hcont
      (hX₁.trans_lt ENNReal.ofReal_lt_top) (hX₂.trans_lt ENNReal.ofReal_lt_top)
    rw [zero_add] at hprod
    have heq : ∀ ts ∈ timeBox (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k =
          treeLeaves P.L P.γ P.δ G₁ HT (ts 0) q k *
            coupleLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z))
              ((layerAt LG ((0 : Fin 2), B.lonePath) : ℝ) + 1) (ts 1) k := by
      intro ts hts k _
      have ht0 : (q : ℝ) ≤ ts 0 := hts.1.1
      have hr1 : (r'' : ℝ) + 1 ≤ ts 0 := by
        have : (r'' : ℝ) + 1 ≤ q := by exact_mod_cast hlt
        linarith
      have hKe := hK (ts 0) (ts 1) k hr1
      rw [hHe] at hKe
      exact hKe
    refine (restr_congr (θ := θ) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) (timeBox (q : ℝ) q') Set.univ heq).trans_le
      (hprod.trans ((mul_le_mul' (mul_le_mul' le_rfl hX₁) hX₂).trans ?_))
    rw [ofReal_mul4 (Real.rpow_nonneg (by norm_num) θ) (cLeib_nonneg _ _)
      (mul_nonneg (Ktr_nonneg _) (by positivity))]
    apply ENNReal.ofReal_le_ofReal
    have h2θ : (2 : ℝ) ^ θ ≤ 2 := by
      calc (2 : ℝ) ^ θ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
        _ = 2 := Real.rpow_one 2
    have hab := absorb_kernel_step (c := 2 * (cLeib P.d (30 * P.d) * Ktr θ)) (C := C) (G := G')
      (δ := P.δ) (βT := leafSizeProduct G₁ BT)
      (β₂ := leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z))) (nB := nB) (m₂ := m₂)
      (by nlinarith) hC (by rw [hG'def]; unfold treeG; nlinarith) hδ hβT0 hβ₂0 hnB1
    have hβe : leafSizeProduct LG Bd = leafSizeProduct G₁ BT *
        leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) := by
      have h' := hβ
      rw [hBe] at h'
      exact h'
    rw [← hnn', ← hβe] at hab
    calc 2 ^ θ * cLeib P.d (30 * P.d) * (Ktr θ * (C * (C * P.δ) ^ nB * leafSizeProduct G₁ BT)) *
          (G * (G * P.δ) ^ m₂ * leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)))
        ≤ 2 * cLeib P.d (30 * P.d) * (Ktr θ * (C * (C * P.δ) ^ nB * leafSizeProduct G₁ BT)) *
          (G' * (G' * P.δ) ^ m₂ * leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z))) := by
          gcongr
      _ = 2 * (cLeib P.d (30 * P.d) * Ktr θ) * (C * (C * P.δ) ^ nB * leafSizeProduct G₁ BT) *
          (G' * (G' * P.δ) ^ m₂ * leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z))) := by ring
      _ ≤ _ := hab
  · -- the top block is below `q`
    have hr₁lt : r₁ < q := lt_of_le_of_ne hr₁q htop
    have hE := couple_lower_kernel P OT OC hC hd hL hθ0 hδ H Bd F (timeBox (q : ℝ) q') (-(q : ℝ)) hT
      n .nil Xp LG rfl hsizeC hnN S₀
    have heq : ∀ ts ∈ timeBox (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k =
        coupleLeaves P.L P.γ P.δ LG (fun z => H (botAddr RegChain.nil.lonePath z))
          ((layerAt LG ((0 : Fin 2), RegChain.nil.lonePath) : ℝ) + 1) (ts 1) k := by
      intro ts hts k _
      have ht0 : (q : ℝ) ≤ ts 0 := hts.1.1
      have hq1 : (r₁ : ℝ) + 1 ≤ q := by exact_mod_cast hr₁lt
      have hK : coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k =
          coupleLeaves P.L P.γ P.δ LG H ((r₁ : ℝ) + 1) (ts 1) k :=
        coupleLeaves_upper_eq P.L P.γ P.δ LG H hfl (ts 1) k fun b hb => by
          have hroot : ([] : Path) ∈ (LG.garden.tree 0).nodes := TTree.nil_mem_nodes _
          have hu : Under ((0 : Fin 2), ([] : Path)) b.toNode.1 := ⟨hb.symm, List.nil_prefix⟩
          have hl := layerAt_le_of_under LG hroot b.toNode.2 hu
          rw [layerAt_node] at hl
          have : (LG.layer b.toNode : ℝ) ≤ r₁ := by exact_mod_cast hl
          exact ⟨by linarith, by linarith⟩
      simp only [RegChain.lonePath]
      rw [hK, hHe]
    refine (restr_congr (θ := θ) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) (timeBox (q : ℝ) q') Set.univ heq).trans_le
      (hE.trans ?_)
    simp only [RegChain.lonePath]
    rw [hBe]
    exact ENNReal.ofReal_le_ofReal (bound_mono_G n (by positivity) hGG' hδ hβ0)

/-- **Coherent couples, all `q' ≤ q ≤ p`.** -/
theorem couple_coherent_kernel {p q q' n : ℕ} (hqq : q' ≤ q) (hqp : q ≤ p) (hnN : n ≤ Nmax)
    (Q : RegCpl) (hsize : Q.size = 2 * n) (LG : LayeredGarden 2) (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (H : LeafProfiles 2 P.d) (Bd : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    XNormRestr θ (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
      (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (treeG P.d θ C * (treeG P.d θ C * P.δ) ^ n * leafSizeProduct LG Bd) := by
  obtain ⟨hCG', hGG', hG1⟩ := le_treeG hd hθ0 hC
  have hβ0 : 0 ≤ leafSizeProduct LG Bd := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hC0 : 0 ≤ C := by linarith
  rcases eq_or_lt_of_le hqq with heq | hlt
  · subst heq
    exact (OC q' n hnN Q hcoh.1 hsize LG hcoh.2.1 (coherentCouple_layer_eq hcoh) H Bd hH).trans
      (ENNReal.ofReal_le_ofReal (bound_mono_G n hC0 hCG' hδ hβ0))
  · rw [XNormRestr_eq_rN]
    cases Q with
    | type2 Xp Xm Qlp =>
      exact couple_type2_kernel P OT OC hC hd hL hθ0 hθ1 hδ hlt hqp hnN Xp Xm Qlp hsize LG hcoh H Bd hH
    | triv | type1 c Q₁ Q₂ Q₃ =>
      all_goals
        have hwf := hcoh.1
        have hQ := hcoh.2.1
        have hlayq := layers_type1 hlt.le hcoh rfl
        have hplain : LG.garden.IsPlain := hQ.1.1
        have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b :=
          noFlowerParent_of_noFlower (not_flower_of_plain hplain)
        have hE := OC q' n hnN _ hwf hsize LG hQ hlayq H Bd hH
        have hEb := couple_bottom_kernel hd hL hθ0 hQ hH hE (timeBox (q : ℝ) q') (-(q : ℝ))
          (timeBox_shift_unit q q')
        have heq : ∀ ts ∈ timeBox (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)),
            coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k = coupleLeaves P.L P.γ P.δ LG H (q' + 1) (ts 1) k := by
          intro ts hts k _
          have ht0 : (q : ℝ) ≤ ts 0 := hts.1.1
          have hq1 : (q' : ℝ) + 1 ≤ q := by exact_mod_cast hlt
          exact coupleLeaves_upper_eq P.L P.γ P.δ LG H hfl (ts 1) k fun b _ => by
            rw [hlayq b.toNode]
            exact ⟨by linarith, le_rfl⟩
        refine (restr_congr (θ := θ) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) (timeBox (q : ℝ) q') Set.univ heq).trans_le
          (hEb.trans (ENNReal.ofReal_le_ofReal ?_))
        have hK1 : 1 ≤ Ktr θ := one_le_Ktr hθ0
        calc Ktr θ * (C * (C * P.δ) ^ n * leafSizeProduct LG Bd)
            = (Ktr θ * C) * (C * P.δ) ^ n * leafSizeProduct LG Bd := by ring
          _ ≤ treeG P.d θ C * (treeG P.d θ C * P.δ) ^ n * leafSizeProduct LG Bd := by
              apply mul_le_mul_of_nonneg_right _ hβ0
              apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCG' hδ) n)
                (by positivity) (by linarith)
              have hLc : 1 ≤ cLeib P.d (30 * P.d) := one_le_cLeib hd _
              have : Ktr θ * C ≤ Ktr θ * cLeib P.d (30 * P.d) * C ^ 2 := by
                have h1 : Ktr θ * 1 * C ^ 1 ≤ Ktr θ * cLeib P.d (30 * P.d) * C ^ 2 :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hLc (by linarith)) (pow_le_pow_right₀ hC (by norm_num))
                    (by positivity) (by positivity)
                simpa using h1
              exact this.trans hGG'

end Gate

end WaveTurbulence.Flower.FiltCoh
