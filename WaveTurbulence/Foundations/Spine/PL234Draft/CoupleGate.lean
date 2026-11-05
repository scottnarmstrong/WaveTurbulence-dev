/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.CoupleTop

/-!
# Prop 6.1, `q > q'`, couples: the error estimate

**`couple_err_gt`**: for a coherent embedded couple code with parent layers `q > q'`, on `ℬ = [q,q+1]×[q',q'+1]`,
`‖⟨k⟩^{30d} (K*_𝒬 − 𝒜_𝒬)‖_{𝔛^{η,0,0}(ℬ)} ≤ C_f (C_f δ)^n L^{-(γ₁-√η)} ∏ B_leaf`, `C_f = 6 K_tr² C⁴`, from the
single-layer estimates (`Oracle`):

* trivial and type-1 codes lie in layer `q'` (LAYERREG): the bottom estimate (`couple_bottom_bounds`);
* type-2 codes whose top block is below `q`: the lower bounds (`lower_bounds`) with `π = []`;
* type-2 codes with a top block in layer `q`: the top factor (`tree_top_bounds`, product estimate `restr_top`)
  times the lower bounds of the rest.
-/

@[expose] public section

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-- The nodes of a coherent couple carrier, in the ambient garden. -/
theorem layer_of_coherent {p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2}
    (h : IsCoherentCoupleAt p q q' Q LG) :
    ∃ (w : ℕ) (HH : LayeredGarden w) (a b : Fin w × Path), IsCanonGC (p + 1) HH ∧ Embeds HH.garden Q a b ∧
      CohOn HH (Q.linksAt a b) ∧ parAt HH p a = q ∧ parAt HH p b = q' ∧
      ∀ z : GNode LG.garden.tree, rootEmb a b z.1 ∈ cplNodes Q a b ∧ LG.layer z = layerAt HH (rootEmb a b z.1) := by
  obtain ⟨hwf, hQ, w, HH, a, b, hcan, hE, -, -, hcoh, hpa, hpb, hlay⟩ := h
  refine ⟨w, HH, a, b, hcan, hE, hcoh, hpa, hpb, fun z => ⟨?_, ?_⟩⟩
  · have ha := addrExt_mem_cplNodes hQ ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) z
    have hae : addrExt (if z.1.1 = 0 then ((0 : Fin 2), ([] : Path)) else ((1 : Fin 2), ([] : Path))) z.1.2 =
        z.1 := by
      obtain ⟨⟨j, q⟩, _⟩ := z
      fin_cases j <;> simp [addrExt]
    rw [hae] at ha
    have hm := cplNodes_map Q (rootEmb a b) (rootEmb_hom a b) ((0 : Fin 2), []) ((1 : Fin 2), [])
    rw [rootEmb_zero, rootEmb_one] at hm
    rw [hm]
    exact Finset.mem_image_of_mem _ ha
  · rw [← layerAt_node, layerAt_rootEmb hQ hE hlay]

/-- **Trivial and type-1 coherent couples lie in layer `q'`** when `q' ≤ q`. -/
theorem layers_type1 {p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2} (hqq : q' ≤ q)
    (h : IsCoherentCoupleAt p q q' Q LG) (ht : Q.isType2 = false) : ∀ z : GNode LG.garden.tree, LG.layer z = q' := by
  have hwf := h.1
  obtain ⟨w, HH, a, b, hcan, hE, hcoh, hpa, hpb, hz⟩ := layer_of_coherent h
  have hL := layerreg1_type1 hcan.2.2 hcan.1 hwf hE hcoh ht
  intro z
  rw [(hz z).2, hL _ (hz z).1, hpa, hpb, min_eq_right hqq]

/-- The root of the `+` tree of a coherent type-2 couple is in a layer `≤ q`. -/
theorem root_le_type2 {p q q' : ℕ} {Xp Xm : RegChain} {Qlp : RegCpl} {LG : LayeredGarden 2} (_hqq : q' ≤ q)
    (h : IsCoherentCoupleAt p q q' (.type2 Xp Xm Qlp) LG) : layerAt LG ((0 : Fin 2), []) ≤ q := by
  have hwf := h.1
  have hQ := h.2.1
  obtain ⟨w, HH, a, b, hcan, hE, hcoh, hpa, hpb, hz⟩ := layer_of_coherent h
  have hnode : ([] : Path) ∈ (LG.garden.tree 0).nodes := TTree.nil_mem_nodes _
  have h0 := (hz ⟨((0 : Fin 2), []), hnode⟩).2
  rw [layerAt_node LG ⟨((0 : Fin 2), []), hnode⟩, h0, rootEmb_zero]
  rw [← hpa]
  exact layerAt_le_parAt HH p hcan.2.2.1 hE.nodeA

/-- The final constant `C_f = 6 K_tr² C⁴`. -/
noncomputable def Cf (θ C : ℝ) : ℝ := 6 * Ktr θ ^ 2 * C ^ 4

theorem absorb_final {θ C δ Λ β : ℝ} (hθ : 0 ≤ θ) (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hΛ : 0 ≤ Λ) (hβ : 0 ≤ β)
    (n : ℕ) :
    2 * Ktr θ * (3 ^ (n + 1) * (Ktr θ * C ^ 2) * (2 * C ^ 4) ^ n * δ ^ n * Λ * β) ≤
      Cf θ C * (Cf θ C * δ) ^ n * Λ * β := by
  have hK := one_le_Ktr hθ
  have hK0 : 0 ≤ Ktr θ := by linarith
  have hC0 : 0 ≤ C := by linarith
  have h1 : C ^ 2 ≤ C ^ 4 := pow_le_pow_right₀ hC (by norm_num)
  have h2 : 6 * C ^ 4 ≤ 6 * Ktr θ ^ 2 * C ^ 4 := by
    have : (1 : ℝ) ≤ Ktr θ ^ 2 := one_le_pow₀ hK
    nlinarith [pow_nonneg hC0 4]
  have e6 : (6 * C ^ 4) ^ n = 3 ^ n * (2 * C ^ 4) ^ n := by
    rw [show (6 : ℝ) * C ^ 4 = 3 * (2 * C ^ 4) by ring, mul_pow]
  calc 2 * Ktr θ * (3 ^ (n + 1) * (Ktr θ * C ^ 2) * (2 * C ^ 4) ^ n * δ ^ n * Λ * β)
      = (6 * Ktr θ ^ 2 * C ^ 2) * (3 ^ n * (2 * C ^ 4) ^ n) * δ ^ n * Λ * β := by
        rw [pow_succ]
        ring
    _ = (6 * Ktr θ ^ 2 * C ^ 2) * (6 * C ^ 4) ^ n * δ ^ n * Λ * β := by rw [e6]
    _ ≤ (6 * Ktr θ ^ 2 * C ^ 4) * (6 * Ktr θ ^ 2 * C ^ 4) ^ n * δ ^ n * Λ * β := by
        gcongr
    _ = Cf θ C * (Cf θ C * δ) ^ n * Λ * β := by rw [Cf, mul_pow]; ring

theorem absorb_final' {θ C δ Λ β : ℝ} (hθ : 0 ≤ θ) (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hΛ : 0 ≤ Λ) (hβ : 0 ≤ β)
    (n : ℕ) :
    3 ^ (n + 1) * (Ktr θ * C ^ 2) * (2 * C ^ 4) ^ n * δ ^ n * Λ * β ≤ Cf θ C * (Cf θ C * δ) ^ n * Λ * β := by
  have hK := one_le_Ktr hθ
  refine le_trans ?_ (absorb_final hθ hC hδ hΛ hβ n)
  have h0 : 0 ≤ 3 ^ (n + 1) * (Ktr θ * C ^ 2) * (2 * C ^ 4) ^ n * δ ^ n * Λ * β := by
    have : 0 ≤ Ktr θ := by linarith
    have : 0 ≤ C := by linarith
    positivity
  nlinarith

/-- **The facts of the top block** of a nonempty suffix of the `+` chain whose top layer `u` exceeds `q'`. -/
theorem block_facts {LG : LayeredGarden 2} {Xp Xm : RegChain} {Qlp : RegCpl} {q' p : ℕ}
    (F : CohFacts LG Xp Xm Qlp q' p) {R X : RegChain} (hXp : Xp = appendChain R X) (hXn : X ≠ .nil)
    {u : ℕ} (hu : layerAt LG ((0 : Fin 2), R.lonePath) = u) (hqu : q' < u) :
    (∀ z ∈ chainNodesSet (takeLayer LG ((0 : Fin 2), R.lonePath) u X) 1 ((0 : Fin 2), R.lonePath),
        layerAt LG z = u) ∧
      layerAt LG ((0 : Fin 2), R.lonePath ++ (takeLayer LG ((0 : Fin 2), R.lonePath) u X).lonePath) < u ∧
      q' ≤ layerAt LG ((0 : Fin 2), R.lonePath ++ (takeLayer LG ((0 : Fin 2), R.lonePath) u X).lonePath) ∧
      (RegCpl.type2 X Xm Qlp).wf = true ∧
      SpineMono LG ((0 : Fin 2), R.lonePath ++ (takeLayer LG ((0 : Fin 2), R.lonePath) u X).lonePath)
        (dropLayer LG ((0 : Fin 2), R.lonePath) u X) := by
  set π := R.lonePath with hπ
  obtain ⟨hXwf, hmwf, hlwf, hlt2⟩ := F.wf_suffix hXp
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
  have hnode : (addrExt ((0 : Fin 2), π) B.lonePath).2 ∈
      (LG.garden.tree (addrExt ((0 : Fin 2), π) B.lonePath).1).nodes := by
    have ht : (LG.garden.tree ((0 : Fin 2), π).1).subtreeAt ((0 : Fin 2), π).2 =
        B.plug 1 (D.plug 1 Qlp.trees.1) := by
      rw [hEmbBD.tree, appendChain_plug]
    exact (node_iff_of_subtree hEmb.node ht B.lonePath).1.mpr (lonePath_mem_plug B 1 _)
  have hle : layerAt LG ((0 : Fin 2), π ++ B.lonePath) ≤ u := by
    rw [← hu]
    exact layerAt_le_of_under LG hEmb.node hnode (under_ext _ _)
  have hlone := F.lone_suffix hXp
  have hloneB : D = .nil → layerAt LG ((0 : Fin 2), π ++ B.lonePath) = q' := fun hDn => by
    have e : ((0 : Fin 2), π ++ B.lonePath) = addrExt ((0 : Fin 2), π) X.lonePath := by
      rw [← hXe, appendChain_lonePath, hDn]
      simp [RegChain.lonePath, addrExt]
    rw [e]
    exact hlone
  refine ⟨hBlay, ?_, ?_, ?_, spineMono_append_right LG B D _ hSMBD⟩
  · by_cases hDn : D = .nil
    · rw [hloneB hDn]; exact hqu
    · exact lt_of_le_of_ne hle (layer_drop_ne LG u X _ hDn)
  · by_cases hDn : D = .nil
    · rw [hloneB hDn]
    · obtain ⟨m', Qr', Qg', inner', rest', hD'⟩ :
          ∃ m' Qr' Qg' inner' rest', D = .pair m' Qr' Qg' inner' rest' := by
        cases hDc : D with
        | nil => exact absurd hDc hDn
        | pair m' Qr' Qg' inner' rest' => exact ⟨m', Qr', Qg', inner', rest', rfl⟩
      apply F.low
      apply CohFacts.sub_suffix hXp
      rw [← hXe]
      apply chainNodesSet_append_right B D 1 ((0 : Fin 2), π)
      rw [hD']
      exact root_mem_chainNodesSet _ _ _ _ _ _ _
  · have hXnil : X.isNil = false := by cases X <;> simp_all [RegChain.isNil]
    simp [RegCpl.wf, hXwf, hmwf, hlwf, hlt2, hXnil]

theorem continuous_coupleLeaves_snd {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 2) (H : LeafProfiles 2 d)
    (hplain : LG.garden.IsPlain) (c : ℝ) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|) :
    Continuous fun ts : Fin 2 → ℝ => coupleLeaves L γ δ LG H c (ts 1) k := by
  have hc := continuous_coupleLeaves_time L γ δ H LG hplain k hF
  have hg : Continuous (fun ts : Fin 2 → ℝ => (![c, ts 1] : Fin 2 → ℝ)) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_const
    · exact continuous_apply 1
  exact (hc.comp hg).congr fun _ => rfl

theorem continuous_lowApp_snd {d : ℕ} (δ : ℝ) (LG : LayeredGarden 2) (H : LeafProfiles 2 d) (Xm : RegChain)
    (Qlp : RegCpl) (q' : ℕ) (π : Path) (X : RegChain) (k : Mom d) :
    Continuous fun ts : Fin 2 → ℝ => lowApp δ LG H Xm Qlp q' π X (ts 1) k := by
  unfold lowApp lowBot
  exact continuous_const.mul (continuous_LeafApp_couple_comp _ _ _ _ _ _ _ continuous_const
    (continuous_apply 1))

section Err

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1) (hη2 : P.η ≤ 1 - P.η) (hδ : 0 ≤ P.δ)
  (hΛ0 : 0 ≤ gainΛ P) (hΛ1 : gainΛ P ≤ 1)

theorem timeBox_shift_unit (q q' : ℕ) :
    ∀ ts ∈ timeBox (q : ℝ) q', ts + ![-(q : ℝ), -(q' : ℝ)] ∈ (Layered.unitBox : Set (Fin 2 → ℝ)) := by
  intro ts hts i
  obtain ⟨h0, h1⟩ := hts
  have e0 : (ts + ![-(q : ℝ), -(q' : ℝ)]) 0 = ts 0 - q := by simp; ring
  have e1 : (ts + ![-(q : ℝ), -(q' : ℝ)]) 1 = ts 1 - q' := by simp; ring
  fin_cases i
  · show (ts + ![-(q : ℝ), -(q' : ℝ)]) 0 ∈ Icc (0 : ℝ) 1
    rw [e0]
    constructor <;> linarith [h0.1, h0.2]
  · show (ts + ![-(q : ℝ), -(q' : ℝ)]) 1 ∈ Icc (0 : ℝ) 1
    rw [e1]
    constructor <;> linarith [h1.1, h1.2]

include O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1

omit hη1 hΛ1 in
/-- **Trivial and type-1 codes.** -/
theorem couple_err_type1 {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (hsize : Q.size = 2 * n) (LG : LayeredGarden 2) (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (ht : Q.isType2 = false) (H : LeafProfiles 2 P.d) (Bd : (Fin 2 × Path) → NNReal)
    (hH : LeafwiseControlled LG H Bd) :
    R00 P.η (timeBox q q') Set.univ (fun ts k => wt k *
        (coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k)) ≤
      ENNReal.ofReal (Cf P.η C * (Cf P.η C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) := by
  have hwf := hcoh.1
  have hQ := hcoh.2.1
  have hlayq := layers_type1 hqq.le hcoh ht
  have hplain : LG.garden.IsPlain := hQ.1.1
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b := noFlowerParent_of_noFlower (not_flower_of_plain hplain)
  have hβ0 : 0 ≤ leafSizeProduct LG Bd := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hC0 : 0 ≤ C := by linarith
  obtain ⟨hE, hJ, hM⟩ := O.couple q' n (by omega) hnN Q hwf hsize LG hQ hlayq H Bd hH
  obtain ⟨hEb, -⟩ := couple_bottom_bounds P Q LG H hd hL hη0 hη2 hδ hsize hQ Bd hH
    (by positivity : 0 ≤ C * C ^ n * leafSizeProduct LG Bd) hE hJ hM (timeBox (q : ℝ) q') (-(q : ℝ))
    (timeBox_shift_unit q q')
  have heq : ∀ ts ∈ timeBox (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)), wt k *
      (coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k) =
      wt k * (coupleLeaves P.L P.γ P.δ LG H (q' + 1) (ts 1) k -
        LeafApp.couple P.δ q' H Q (q' + 1) (ts 1) k) := by
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
  refine (Layered.restr_congr P.η (timeBox (q : ℝ) q') Set.univ heq).trans_le (hEb.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  exact (absorb_base_err hC hδ hΛ0 hβ0 (Ktr_nonneg _) n).trans (absorb_final' hη0 hC hδ hΛ0 hβ0 n)

/-- **Type-2 codes.** -/
theorem couple_err_type2 {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (Xp Xm : RegChain) (Qlp : RegCpl) (hsize : (RegCpl.type2 Xp Xm Qlp).size = 2 * n) (LG : LayeredGarden 2)
    (hcoh : IsCoherentCoupleAt p q q' (.type2 Xp Xm Qlp) LG) (H : LeafProfiles 2 P.d)
    (Bd : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    R00 P.η (timeBox q q') Set.univ (fun ts k => wt k *
        (coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.coherentCouple P.δ LG H (.type2 Xp Xm Qlp) q q' (ts 0) (ts 1) k)) ≤
      ENNReal.ofReal (Cf P.η C * (Cf P.η C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) := by
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
      exact root_mem_chainNodesSet _ _ _ _ _ _ _
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
    obtain ⟨hX, hY⟩ := tree_top_bounds P B G₁ HT hd hL hη0 hη2 hδ hlt hBsize hdec₁ hlay₁ BT hctrl₁
      (by positivity) (by positivity) (by positivity) hET hJT hMT (timeBox (q : ℝ) q') (-(q' : ℝ)) hT
    rw [hsig₁] at hX hY
    -- the lower bounds of the rest
    have S''' : LowState LG H Bd Xm Qlp B.lonePath D LG'' := S''
    obtain ⟨hE₂, hA₂⟩ := lower_bounds P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 H Bd F (timeBox (q : ℝ) q') (-(q : ℝ))
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
    have hc₁ : ∀ k ∈ (Set.univ : Set (Mom P.d)), Continuous fun ts : Fin 2 → ℝ => wt k *
        (coupleLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) ((r'' : ℝ) + 1) (ts 1) k -
          lowApp P.δ LG H Xm Qlp q' B.lonePath D (ts 1) k) := fun k _ =>
      continuous_const.mul ((hcK k).sub (hcA k))
    have hc₂ : ∀ k ∈ (Set.univ : Set (Mom P.d)), Continuous fun ts : Fin 2 → ℝ => wt k *
        lowApp P.δ LG H Xm Qlp q' B.lonePath D (ts 1) k := fun k _ => continuous_const.mul (hcA k)
    have htopb := Layered.restr_top hη0 (timeBox (q : ℝ) q') (fun ts hts => by
        rw [closure_interior_timeBox]; exact hts) (Set.univ : Set (Mom P.d)) wt
      (fun ts k => treeLeaves P.L P.γ P.δ G₁ HT (ts 0) q k)
      (fun ts k => LeafApp.tree P.δ q HT B 1 (ts 0) q k)
      (fun ts k => coupleLeaves P.L P.γ P.δ LG'' (fun z => H (botAddr B.lonePath z)) ((r'' : ℝ) + 1) (ts 1) k)
      (fun ts k => lowApp P.δ LG H Xm Qlp q' B.lonePath D (ts 1) k) hc₁ hc₂
      (by positivity) (by positivity) (by positivity) (by positivity) hX hY hE₂ hA₂
    have hsl : SourceApp.chainSlice LG ((0 : Fin 2), []) q Xp = B :=
      chainSlice_eq_take LG _ Xp F.sm fun _ => by rw [← hr₁, htop]
    have heq : ∀ ts ∈ timeBox (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)), wt k *
        (coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.coherentCouple P.δ LG H (.type2 Xp Xm Qlp) q q' (ts 0) (ts 1) k) =
        wt k * ((fun ts k => treeLeaves P.L P.γ P.δ G₁ HT (ts 0) q k) ts k *
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
    refine (Layered.restr_congr P.η (timeBox (q : ℝ) q') Set.univ heq).trans_le (htopb.1.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    -- constants
    have h2η : (2 : ℝ) ^ P.η ≤ 2 := by
      calc (2 : ℝ) ^ P.η ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hη1
        _ = 2 := Real.rpow_one 2
    have hε := absorb_tree_err hC hδ hΛ0 hβT0 hnB1
    have hα := absorb_tree_app hC hδ hβT0 hnB1
    have habs := absorb_step (δ := P.δ) (Λ := gainΛ P) (D₀ := 2 * C ^ 4) (M₀ := Ktr P.η * C ^ 2) (m₂ := m₂)
      (n := nB) (β₁ := Ktr P.η * leafSizeProduct G₁ BT) (by positivity) (by positivity) hδ hΛ0 hΛ1
      (by positivity) hβ₂0 (by positivity) (by positivity)
      (ε := Ktr P.η * (C * (C * P.δ) ^ nB * gainΛ P * leafSizeProduct G₁ BT))
      (α := P.δ ^ nB * 2 ^ nB * (C * C ^ nB * leafSizeProduct G₁ BT) * (Ktr P.η * (C * C ^ nB)))
      (by nlinarith) (by
        have : P.δ ^ nB * 2 ^ nB * (C * C ^ nB * leafSizeProduct G₁ BT) * (Ktr P.η * (C * C ^ nB)) =
            Ktr P.η * (P.δ ^ nB * 2 ^ nB * (C * C ^ nB) * (C * C ^ nB * leafSizeProduct G₁ BT)) := by ring
        rw [this]
        nlinarith) le_rfl le_rfl (by positivity) (by positivity) hnB1
    rw [← hnn'] at habs
    have hβe : leafSizeProduct LG Bd = leafSizeProduct G₁ BT *
        leafSizeProduct LG'' (fun z => Bd (botAddr B.lonePath z)) := by
      have h' := hβ
      rw [hBe] at h'
      exact h'
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
  · -- the top block is below `q`
    have hr₁lt : r₁ < q := lt_of_le_of_ne hr₁q htop
    obtain ⟨hE, -⟩ := lower_bounds P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 H Bd F (timeBox (q : ℝ) q') (-(q : ℝ))
      hT n .nil Xp LG rfl hsizeC hnN S₀
    have heq : ∀ ts ∈ timeBox (q : ℝ) q', ∀ k ∈ (Set.univ : Set (Mom P.d)), wt k *
        (coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.coherentCouple P.δ LG H (.type2 Xp Xm Qlp) q q' (ts 0) (ts 1) k) =
        wt k * (coupleLeaves P.L P.γ P.δ LG (fun z => H (botAddr RegChain.nil.lonePath z))
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
    refine (Layered.restr_congr P.η (timeBox (q : ℝ) q') Set.univ heq).trans_le (hE.trans ?_)
    simp only [RegChain.lonePath]
    rw [hBe]
    exact ENNReal.ofReal_le_ofReal (absorb_final' hη0 hC hδ hΛ0 hβ0 n)

/-- **Prop 6.1, couples, `q > q'`: the error estimate** (TARGET L1097–1111, prooflayer1-1). -/
theorem couple_err_gt {q q' n : ℕ} (hqq : q' < q) (hqp : q ≤ p) (hnN : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (hsize : Q.size = 2 * n) (LG : LayeredGarden 2) (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (H : LeafProfiles 2 P.d) (Bd : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H Bd) :
    R00 P.η (timeBox q q') Set.univ (fun ts k => wt k *
        (coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k)) ≤
      ENNReal.ofReal (Cf P.η C * (Cf P.η C * P.δ) ^ n * gainΛ P * leafSizeProduct LG Bd) := by
  cases Q with
  | triv => exact couple_err_type1 P O hC hd hL hη0 hη2 hδ hΛ0 hqq hqp hnN _ hsize LG hcoh rfl H Bd hH
  | type1 c Q₁ Q₂ Q₃ => exact couple_err_type1 P O hC hd hL hη0 hη2 hδ hΛ0 hqq hqp hnN _ hsize LG hcoh rfl H Bd hH
  | type2 Xp Xm Qlp =>
    exact couple_err_type2 P O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 hqq hqp hnN Xp Xm Qlp hsize LG hcoh H Bd hH

end Err

end WaveTurbulence.PL234
