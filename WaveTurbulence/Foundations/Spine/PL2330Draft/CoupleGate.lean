/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.CoupleInd

/-!
# Prop 6.1 at `Λ₁ = 30d`, `q > q'`, couples: the error estimate (PL23-30D)

**`couple_err_gt30`**: for a coherent embedded couple code with parent layers `q > q'`, on `ℬ = [q,q+1]×[q',q'+1]`,
`‖K*_𝒬 − 𝒜_𝒬‖_{𝔛^{η,30d,30d}(ℬ)} ≤ C_f (C_f δ)^n L^{-(γ₁-√η)} ∏ B_leaf`, `C_f = 6 K_tr² C⁴ L²`,
`L = (2d)^{30d}`, from the single-layer estimates (`Oracle`).
-/

@[expose] public section

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL2330

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.Reg WaveTurbulence.Links

/-- The final constant `C_f = 6 K_tr² C⁴ L²`. -/
noncomputable def Cf30 (θ C L2 : ℝ) : ℝ := 6 * Ktr θ ^ 2 * C ^ 4 * L2

theorem absorb_final30 {θ C δ Λ β L2 : ℝ} (hθ : 0 ≤ θ) (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hΛ : 0 ≤ Λ) (hβ : 0 ≤ β)
    (hL : 1 ≤ L2) (n : ℕ) :
    2 * Ktr θ * (3 ^ (n + 1) * (Ktr θ * C ^ 2 * L2) * (2 * C ^ 4 * L2) ^ n * δ ^ n * Λ * β) ≤
      Cf30 θ C L2 * (Cf30 θ C L2 * δ) ^ n * Λ * β := by
  have hK := one_le_Ktr hθ
  have hK0 : 0 ≤ Ktr θ := by linarith
  have hC0 : 0 ≤ C := by linarith
  have h1 : C ^ 2 ≤ C ^ 4 := pow_le_pow_right₀ hC (by norm_num)
  have hK2 : (1 : ℝ) ≤ Ktr θ ^ 2 := one_le_pow₀ hK
  have hL0 : 0 ≤ L2 := by linarith
  have h2 : 6 * C ^ 4 * L2 ≤ 6 * Ktr θ ^ 2 * C ^ 4 * L2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hK2) (mul_nonneg (pow_nonneg hC0 4) hL0)]
  have e6 : (6 * C ^ 4 * L2) ^ n = 3 ^ n * (2 * C ^ 4 * L2) ^ n := by
    rw [show (6 : ℝ) * C ^ 4 * L2 = 3 * (2 * C ^ 4 * L2) by ring, mul_pow]
  calc 2 * Ktr θ * (3 ^ (n + 1) * (Ktr θ * C ^ 2 * L2) * (2 * C ^ 4 * L2) ^ n * δ ^ n * Λ * β)
      = (6 * Ktr θ ^ 2 * C ^ 2 * L2) * (3 ^ n * (2 * C ^ 4 * L2) ^ n) * δ ^ n * Λ * β := by
        rw [pow_succ]
        ring
    _ = (6 * Ktr θ ^ 2 * C ^ 2 * L2) * (6 * C ^ 4 * L2) ^ n * δ ^ n * Λ * β := by rw [e6]
    _ ≤ (6 * Ktr θ ^ 2 * C ^ 4 * L2) * (6 * Ktr θ ^ 2 * C ^ 4 * L2) ^ n * δ ^ n * Λ * β := by
        gcongr
    _ = Cf30 θ C L2 * (Cf30 θ C L2 * δ) ^ n * Λ * β := by rw [Cf30, mul_pow]; ring

theorem absorb_final30' {θ C δ Λ β L2 : ℝ} (hθ : 0 ≤ θ) (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hΛ : 0 ≤ Λ) (hβ : 0 ≤ β)
    (hL : 1 ≤ L2) (n : ℕ) :
    3 ^ (n + 1) * (Ktr θ * C ^ 2 * L2) * (2 * C ^ 4 * L2) ^ n * δ ^ n * Λ * β ≤
      Cf30 θ C L2 * (Cf30 θ C L2 * δ) ^ n * Λ * β := by
  have hK := one_le_Ktr hθ
  refine le_trans ?_ (absorb_final30 hθ hC hδ hΛ hβ hL n)
  have h0 : 0 ≤ 3 ^ (n + 1) * (Ktr θ * C ^ 2 * L2) * (2 * C ^ 4 * L2) ^ n * δ ^ n * Λ * β := by
    have : 0 ≤ Ktr θ := by linarith
    have : 0 ≤ C := by linarith
    have : 0 ≤ L2 := by linarith
    positivity
  nlinarith

section Err

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1) (hη2 : P.η ≤ 1 - P.η) (hδ : 0 ≤ P.δ)
  (hΛ0 : 0 ≤ gainΛ P) (hΛ1 : gainΛ P ≤ 1)

include O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1

omit hη1 hΛ1 in
/-- **Trivial and type-1 codes.** -/
theorem couple_err_type1_30 {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (hsize : Q.size = 2 * n) (LG : LayeredGarden 2) (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (ht : Q.isType2 = false) (H : LeafProfiles 2 P.d) (Bd : (Fin 2 × Path) → NNReal)
    (hH : LeafwiseControlled LG H Bd) :
    rN P.η (30 * P.d) (30 * P.d) (timeBox q q') (fun ts k =>
        coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (Cf30 P.η C (Lsq P) * (Cf30 P.η C (Lsq P) * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) := by
  have hwf := hcoh.1
  have hQ := hcoh.2.1
  have hlayq := layers_type1 hqq.le hcoh ht
  have hplain : LG.garden.IsPlain := hQ.1.1
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b := noFlowerParent_of_noFlower (not_flower_of_plain hplain)
  have hβ0 : 0 ≤ leafSizeProduct LG Bd := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hC0 : 0 ≤ C := by linarith
  obtain ⟨hE, hJ, hM⟩ := O.couple q' n (by omega) hnN Q hwf hsize LG hQ hlayq H Bd hH
  obtain ⟨hEb, -⟩ := couple_bottom_bounds30 P Q LG H hd hL hη0 hη2 hδ hsize hQ Bd hH
    (by positivity : 0 ≤ C * C ^ n * leafSizeProduct LG Bd) (by positivity : 0 ≤ C * C ^ n) hE hJ hM
    (timeBox (q : ℝ) q') (-(q : ℝ)) (timeBox_shift_unit q q')
  have heq : ∀ ts ∈ timeBox (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)),
      (coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k) =
      (coupleLeaves P.L P.γ P.δ LG H (q' + 1) (ts 1) k - LeafApp.couple P.δ q' H Q (q' + 1) (ts 1) k) := by
    intro ts hts k _
    have ht0 : (q : ℝ) ≤ ts 0 := hts.1.1
    have hq1 : (q' : ℝ) + 1 ≤ q := by exact_mod_cast hqq
    have hK : coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k =
        coupleLeaves P.L P.γ P.δ LG H (q' + 1) (ts 1) k :=
      coupleLeaves_upper_eq P.L P.γ P.δ LG H hfl (ts 1) k fun b _ => by
        rw [hlayq b.toNode]
        exact ⟨by linarith, le_rfl⟩
    have hA : LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k =
        LeafApp.couple P.δ q' H Q (q' + 1) (ts 1) k := by
      have hne : q ≠ q' := by omega
      cases Q with
      | triv => simp only [LeafApp.coherentCouple, hne, hqq, ↓reduceIte]
      | type1 c Q₁ Q₂ Q₃ => simp only [LeafApp.coherentCouple, hne, hqq, ↓reduceIte]
      | type2 Xp Xm Qlp => simp [RegCpl.isType2] at ht
    rw [hK, hA]
  refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) (timeBox (q : ℝ) q') Set.univ heq).trans_le
    (hEb.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  exact (absorb_base_err30 hC hδ hΛ0 hβ0 (one_le_Lsq P hd) (Ktr_nonneg _) n).trans
    (absorb_final30' hη0 hC hδ hΛ0 hβ0 (one_le_Lsq P hd) n)


/-- **Type-2 codes.** -/
theorem couple_err_type2_30 {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (Xp Xm : RegChain) (Qlp : RegCpl) (hsize : (RegCpl.type2 Xp Xm Qlp).size = 2 * n) (LG : LayeredGarden 2)
    (hcoh : IsCoherentCoupleAt p q q' (.type2 Xp Xm Qlp) LG) (H : LeafProfiles 2 P.d)
    (Bd : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    rN P.η (30 * P.d) (30 * P.d) (timeBox q q') (fun ts k =>
        coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.coherentCouple P.δ LG H (.type2 Xp Xm Qlp) q q' (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (Cf30 P.η C (Lsq P) * (Cf30 P.η C (Lsq P) * P.δ) ^ n * gainΛ P *
        leafSizeProduct LG Bd) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hL2 : 1 ≤ Lsq P := one_le_Lsq P hd
  have hLle : cLeib P.d (30 * P.d) ≤ Lsq P := cLeib_le_Lsq P hd
  have hLc : 1 ≤ cLeib P.d (30 * P.d) := one_le_cLeib hd _
  have F := cohFacts_of_coherent hqq.le hqp hcoh
  have hQ := hcoh.2.1
  have hplain : LG.garden.IsPlain := hQ.1.1
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b := noFlowerParent_of_noFlower (not_flower_of_plain hplain)
  have hC0 : 0 ≤ C := by linarith
  have hK0 : 0 ≤ Ktr P.η := Ktr_nonneg _
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
  have hlowr₁ : q' ≤ r₁ := by
    by_cases hXpn : Xp = .nil
    · have := F.lone_suffix (R := .nil) (X := Xp) rfl
      rw [hXpn] at this
      simp only [RegChain.lonePath, addrExt, List.append_nil] at this
      rw [hr₁, this]
    · obtain ⟨m', Qr', Qg', inner', rest', hX'⟩ : ∃ m' Qr' Qg' inner' rest', Xp = .pair m' Qr' Qg' inner' rest' := by
        cases hXc : Xp with
        | nil => exact absurd hXc hXpn
        | pair m' Qr' Qg' inner' rest' => exact ⟨m', Qr', Qg', inner', rest', rfl⟩
      apply F.low
      rw [hX']
      exact PL234.root_mem_chainNodesSet _ _ _ _ _ _ _
  by_cases htop : r₁ = q
  · -- the top block is in layer `q`
    have hXpn : Xp ≠ .nil := by
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
    -- sizes
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
    set BT : (Fin 1 × Path) → NNReal := fun z => Bd (LeafApp.sliceAddress LG ((0 : Fin 2), []) q Xp z.2) with hBT
    have hβT0 : 0 ≤ leafSizeProduct G₁ BT := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    obtain ⟨hET, hJT, hMT⟩ := O.tree q r'' nB hqp hlt.le (by omega) B hBwf hBsize G₁ hdec₁ hlay₁ HT BT hctrl₁
    obtain ⟨hX, hY⟩ := tree_top_bounds30 P B G₁ HT hd hL hη0 hη2 hδ hlt hBsize hdec₁ hlay₁ BT hctrl₁
      (by positivity) (by positivity) (by positivity) hET hJT hMT (timeBox (q : ℝ) q') (-(q' : ℝ)) hT
    rw [hsig₁] at hX hY
    -- the lower bounds of the rest
    have S''' : LowState LG H Bd Xm Qlp B.lonePath D LG'' := S''
    obtain ⟨hE₂, hA₂⟩ := lower_bounds30 P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 H Bd F (timeBox (q : ℝ) q') (-(q : ℝ))
      hT m₂ B D LG'' hXe.symm hsz₂ (by omega) S'''
    have hβ₂0 : 0 ≤ leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) :=
      Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hplain'' : LG''.garden.IsPlain := S''.dec.1.1
    -- continuity of the lower functions in time
    have hcK : ∀ k : Mom P.d, Continuous fun ts : Fin 2 → ℝ =>
        coupleLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) ((r'' : ℝ) + 1) (ts 1) k :=
      fun k => continuous_coupleLeaves_snd P.L P.γ P.δ LG'' _ hplain'' _ k (S''.ctrl.summable_coset hd hL k)
    have hcA : ∀ k : Mom P.d, Continuous fun ts : Fin 2 → ℝ =>
        lowApp P.δ LG H Xm Qlp q' B.lonePath D (ts 1) k := fun k =>
      continuous_lowApp_snd P.δ LG H Xm Qlp q' B.lonePath D k
    have hc₁ : ∀ k : Mom P.d, Continuous fun ts : Fin 2 → ℝ =>
        (coupleLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) ((r'' : ℝ) + 1) (ts 1) k -
          lowApp P.δ LG H Xm Qlp q' B.lonePath D (ts 1) k) := fun k => (hcK k).sub (hcA k)
    have htopb := restr_top30 (θ := P.η) hΛ hd hη0 (30 * P.d) (timeBox (q : ℝ) q') (fun ts hts => by
        rw [closure_interior_timeBox]; exact hts)
      (fun ts k => treeLeaves P.L P.γ P.δ G₁ HT (ts 0) q k)
      (fun ts k => LeafApp.tree P.δ q HT B 1 (ts 0) q k)
      (fun ts k => coupleLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) ((r'' : ℝ) + 1) (ts 1) k)
      (fun ts k => lowApp P.δ LG H Xm Qlp q' B.lonePath D (ts 1) k) hc₁ hcA
      (by positivity) (by positivity) (by positivity) (by positivity) hX hY hE₂ hA₂
    have hsl : SourceApp.chainSlice LG ((0 : Fin 2), []) q Xp = B :=
      chainSlice_eq_take LG _ Xp F.sm fun _ => by rw [← hr₁, htop]
    have heq : ∀ ts ∈ timeBox (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        (coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.coherentCouple P.δ LG H (.type2 Xp Xm Qlp) q q' (ts 0) (ts 1) k) =
        ((fun ts k => treeLeaves P.L P.γ P.δ G₁ HT (ts 0) q k) ts k *
          (fun ts k => coupleLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z))
            ((r'' : ℝ) + 1) (ts 1) k) ts k -
          (fun ts k => LeafApp.tree P.δ q HT B 1 (ts 0) q k) ts k *
          (fun ts k => lowApp P.δ LG H Xm Qlp q' B.lonePath D (ts 1) k) ts k) := by
      intro ts hts k _
      have ht0 : (q : ℝ) ≤ ts 0 := hts.1.1
      have hr1 : (r'' : ℝ) + 1 ≤ ts 0 := by
        have : (r'' : ℝ) + 1 ≤ q := by exact_mod_cast hlt
        linarith
      have hKe := hK (ts 0) (ts 1) k hr1
      rw [hHe] at hKe
      have hrest : (∏ r ∈ Finset.Ioo q' q, sliceFactor P.δ LG H [] Xp r k) *
          lowBot P.δ LG H Xm Qlp q' [] Xp (ts 1) k = lowApp P.δ LG H Xm Qlp q' B.lonePath D (ts 1) k :=
        lowRest_eq P.δ LG H Xm Qlp [] Xp (by rw [← hr₁, htop]) hqq hSMD hlow'' hlt (ts 1) k
      have hA : LeafApp.coherentCouple P.δ LG H (.type2 Xp Xm Qlp) q q' (ts 0) (ts 1) k =
          LeafApp.tree P.δ q HT B 1 (ts 0) q k * lowApp P.δ LG H Xm Qlp q' B.lonePath D (ts 1) k := by
        rw [coherentCouple_type2_eq P.δ LG H Xp Xm Qlp hqq, hsl, ← hrest]
        ring
      rw [hKe, hA]
    refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) (timeBox (q : ℝ) q') Set.univ heq).trans_le (htopb.1.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    -- constants
    have h2η : (2 : ℝ) ^ P.η ≤ 2 := by
      calc (2 : ℝ) ^ P.η ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hη1
        _ = 2 := Real.rpow_one 2
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
    have hβe : leafSizeProduct LG Bd = leafSizeProduct G₁ BT *
        leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) := by
      have h' := hβ
      rw [hBe] at h'
      exact h'
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
  · -- the top block is below `q`
    have hr₁lt : r₁ < q := lt_of_le_of_ne hr₁q htop
    obtain ⟨hE, -⟩ := lower_bounds30 P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 H Bd F (timeBox (q : ℝ) q') (-(q : ℝ))
      hT n .nil Xp LG rfl hsizeC hnN S₀
    have heq : ∀ ts ∈ timeBox (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)),
        (coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.coherentCouple P.δ LG H (.type2 Xp Xm Qlp) q q' (ts 0) (ts 1) k) =
        (coupleLeaves P.L P.γ P.δ LG (fun z => H (botAddr RegChain.nil.lonePath z))
          ((layerAt LG ((0 : Fin 2), RegChain.nil.lonePath) : ℝ) + 1) (ts 1) k -
          lowApp P.δ LG H Xm Qlp q' RegChain.nil.lonePath Xp (ts 1) k) := by
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
      have hslq : SourceApp.chainSlice LG ((0 : Fin 2), []) q Xp = .nil :=
        chainSlice_eq_nil LG _ Xp F.sm fun _ => hr₁lt
      have hA : LeafApp.coherentCouple P.δ LG H (.type2 Xp Xm Qlp) q q' (ts 0) (ts 1) k =
          lowApp P.δ LG H Xm Qlp q' [] Xp (ts 1) k := by
        rw [coherentCouple_type2_eq P.δ LG H Xp Xm Qlp hqq, hslq, LeafApp.tree_nil, mul_one]
        unfold lowApp lowSlices
        congr 1
        rw [← hr₁, Ioo_eq_Ico_succ, Ioo_eq_Ico_succ, ← prod_Ico_consecutive _ (show q' + 1 ≤ r₁ + 1 by omega)
          (show r₁ + 1 ≤ q by omega)]
        rw [Finset.prod_eq_one (s := Ico (r₁ + 1) q) fun r hr => by
          unfold sliceFactor
          rw [chainSlice_eq_nil LG _ Xp F.sm fun _ => by simp only [Finset.mem_Ico] at hr; omega]
          exact LeafApp.tree_nil _ _ _ _ _ _ _, mul_one]
      simp only [RegChain.lonePath]
      rw [hK, hA, hHe]
    refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) (timeBox (q : ℝ) q') Set.univ heq).trans_le (hE.trans ?_)
    simp only [RegChain.lonePath]
    rw [hBe]
    exact ENNReal.ofReal_le_ofReal (absorb_final30' hη0 hC hδ hΛ0 hβ0 hL2 n)


/-- **Prop 6.1, couples, `q > q'`: the error estimate** (TARGET L1097–1111, prooflayer1-1), at `Λ₁ = 30d`. -/
theorem couple_err_gt30 {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (hsize : Q.size = 2 * n) (LG : LayeredGarden 2) (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (H : LeafProfiles 2 P.d) (Bd : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    rN P.η (30 * P.d) (30 * P.d) (timeBox q q') (fun ts k =>
        coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (Cf30 P.η C (Lsq P) * (Cf30 P.η C (Lsq P) * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) := by
  cases Q with
  | triv => exact couple_err_type1_30 P O hC hd hL hη0 hη2 hδ hΛ0 hqq hqp hnN _ hsize LG hcoh rfl H Bd hH
  | type1 c Q₁ Q₂ Q₃ => exact couple_err_type1_30 P O hC hd hL hη0 hη2 hδ hΛ0 hqq hqp hnN _ hsize LG hcoh rfl H Bd hH
  | type2 Xp Xm Qlp =>
    exact couple_err_type2_30 P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 hqq hqp hnN Xp Xm Qlp hsize LG hcoh H Bd hH

end Err

end WaveTurbulence.PL2330
