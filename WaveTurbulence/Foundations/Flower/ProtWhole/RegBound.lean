/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtWhole.RegValue
public import WaveTurbulence.Foundations.Flower.ProtWhole.Cont
public import WaveTurbulence.Foundations.Flower.ProtKer.Sanity
public import WaveTurbulence.Foundations.Flower.ProtPtw.Statement
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Pointwise
public import WaveTurbulence.Foundations.Spine.LeafwisePointwise
public import WaveTurbulence.Foundations.Spine.PL234Draft.SplitCouple

/-! # D6b: the protected kernel of a wholly regular component, bounded

`CapG.kernel_bound`: the kernel of `compValue_capG` (paired tree `T1`, upper clock `t`, pins of `objCfg`) is
bounded by `∏ cω · L^{31d+6} · [R⁻¹ if selected] · regBound P n g · leafSize`:
* `objCfg = term` (plain pattern, possibly one selected vertex): D6a's pointwise `ProtPtwAt` directly;
* `rootTerm`, `penTerm`, `termChild i` (no selection, F-D0-8): D3's `ProtBoundAt` (`θ = η`, `L^{31d+6}`) on the box
  `cfg.box X t p p` (R176), evaluated at the point `(t, s)` of the closure of its interior; the kernel is continuous
  in the upper clock (`continuous_kernelProt_up`) and does not see the lone-port time (the lone parent, the flower
  parent, is pinned). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory Filter Topology
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtWhole

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtGeo
open WaveTurbulence.Flower.MkDefs

/-- The point `(t, s)` lies in the closure of the interior of every configuration box (`p < s < t < p + 1`). -/
theorem mem_closure_interior_box (cfg : ProtCfg) (X : RegChain) {p : ℕ} {s t : ℝ} (hps : (p : ℝ) < s)
    (hst : s < t) (htp : t < p + 1) : (![t, s] : Fin 2 → ℝ) ∈ closure (interior (cfg.box X t p p)) := by
  let U : Set (Fin 2 → ℝ) := {ts | t < ts 0 ∧ ts 0 < p + 1 ∧ (p : ℝ) < ts 1 ∧ ts 1 < t}
  have hUo : IsOpen U := by
    simp only [U, Set.setOf_and]
    exact (isOpen_lt continuous_const (continuous_apply 0)).inter ((isOpen_lt (continuous_apply 0)
      continuous_const).inter ((isOpen_lt continuous_const (continuous_apply 1)).inter
        (isOpen_lt (continuous_apply 1) continuous_const)))
  have hUsub : U ⊆ cfg.box X t p p := by
    rintro ts ⟨h1, h2, h3, h4⟩
    have hb : ts ∈ timeBoxGt (p : ℝ) (p : ℝ) :=
      ⟨⟨⟨by linarith, h2.le⟩, ⟨h3.le, by linarith⟩⟩, h4.trans h1⟩
    unfold ProtCfg.box
    split_ifs
    · exact ⟨hb, h1.le⟩
    · exact hb
  refine closure_mono (interior_maximal hUsub hUo) ?_
  have hf : Continuous fun u : ℝ => (![t + u, s] : Fin 2 → ℝ) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_const.add continuous_id
    · exact continuous_const
  have h0 : (![t + 0, s] : Fin 2 → ℝ) = ![t, s] := by simp
  refine mem_closure_of_tendsto (f := fun u : ℝ => (![t + u, s] : Fin 2 → ℝ)) (b := 𝓝[>] (0 : ℝ)) ?_ ?_
  · have := hf.tendsto 0
    rw [h0] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < p + 1 - t by linarith)] with u hu
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith [hu.1, hu.2]

theorem fix_up_indep (cfg : ProtCfg) (hcfg : cfg ≠ .trace) (X : RegChain) (s t up up' : ℝ) {w : ℕ}
    {T : Fin w → TTree} : (cfg.fix X s t up : GBranch T → Option ℝ) = cfg.fix X s t up' := by
  cases cfg <;> first | rfl | exact absurd rfl hcfg

namespace CapG

variable {LG : LayeredGarden 2} {j0 c : Fin 2} {X : RegChain} {ζ : ℤˣ} (D : CapG LG j0 c X ζ)
include D

variable {d : ℕ}

theorem portFlower : PortFlower LG {c} X (j0, []) :=
  ⟨D.ℓ0, (D.isCapFlower_iff _).2 rfl, rfl⟩

theorem objCfg_cases (pat : Fin 2 → FixPat) :
    objCfg LG {c} pat X (j0, []) = .term ∨ objCfg LG {c} pat X (j0, []) = .rootTerm ∨
      objCfg LG {c} pat X (j0, []) = .penTerm ∨ ∃ i, objCfg LG {c} pat X (j0, []) = .termChild i := by
  have hpf := D.portFlower
  unfold objCfg
  cases hq : pat j0 with
  | plain => simp [hpf]
  | dRoot =>
    simp only [hpf, if_true]
    split_ifs <;> simp
  | dParent =>
    simp only [hpf, if_true]
    split_ifs <;> simp
  | dChild i =>
    simp only [hpf, if_true]
    split_ifs <;> simp

theorem objCfg_term_of_sel (pat : Fin 2 → FixPat) {kSel : Fin 2 → Option ℕ}
    (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain) (hs : (selCap LG {c} kSel j0).isSome) :
    objCfg LG {c} pat X (j0, []) = .term := by
  obtain ⟨vj, hv⟩ := Option.isSome_iff_exists.1 hs
  have hp := hplain j0 (selCap_spec hv).1
  have hpf := D.portFlower
  unfold objCfg
  simp [hp, hpf]

theorem lonePin (cfg : ProtCfg)
    (hcfg : cfg = .term ∨ cfg = .rootTerm ∨ cfg = .penTerm ∨ ∃ i, cfg = .termChild i) (s t up : ℝ) :
    ∀ b : GBranch D.T1.garden.tree, D.T1.garden.IsLoneParent b → cfg.fix X s t up b ≠ none := by
  rintro b ⟨ℓ, hl, hpar⟩
  have hlone : ℓ.1.2 = X.lonePath := by
    by_contra hne
    have hm := (D.mark1_iff ℓ).2 hne
    unfold Garden.IsLone at hl
    rw [hm] at hl
    exact absurd hl (by simp)
  obtain ⟨-, i, hi⟩ := hpar
  have hb : b.1.2 = X.lonePath.dropLast := by
    rw [← hlone, hi, List.dropLast_concat]
  unfold ProtCfg.fix
  rw [if_pos (Fin.val_eq_zero b.1.1), hb]
  rcases hcfg with rfl | rfl | rfl | ⟨i, rfl⟩
  · simp [ProtCfg.pins, List.lookup]
  · simp only [ProtCfg.pins, List.lookup]
    split <;> simp
  · simp only [ProtCfg.pins, List.lookup]
    split <;> simp
  · simp [ProtCfg.pins, List.lookup]

theorem lone_ne_nil (hS : StemChain LG {c} X ζ (j0, []) .leaf) : X.lonePath ≠ [] := by
  obtain ⟨v, hv, -⟩ := hS.meets
  obtain ⟨q, hq, -⟩ := mem_branchAddresses'.mp hv
  exact lone_ne_nil_of_branch X ζ hq

theorem summable_H1 {p : ℕ} (hlay : ∀ a, LG.layer a ≤ p) (h : ℕ → Fin 2 → Fin 2 → Mom d → ℝ) (b : NNReal)
    (hb : ∀ q ≤ p, ∀ j j', SNormR (40 * d) (40 * d) (h q j j') ≤ ENNReal.ofReal (b : ℝ)) {L : ℝ} (hL : 1 ≤ L)
    (k : Mom d) : ∀ ℓ ∈ inputLeaves D.T1.garden,
      Summable fun n : Fin d → ℤ => |regH1 LG j0 h ℓ.1 (k + latticePoint L n)| := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · intro ℓ _
    exact Summable.of_finite
  · exact (D.leafwise_H1 hlay h b hb).summable_coset (Nat.succ_le_of_lt hd) hL k

/-- The multiplier without selection is bounded by `1`. -/
theorem norm_mult3_le (p : ℕ) (L : ℝ) (Rf : Fin 2 → Option ℝ) (σ : Fin 2 → Option ℕ)
    (dag : Option (Fin 2 → Fin 3 → Mom d)) (M : GBranch D.T1.garden.tree → ℝ) (K : GNode D.T1.garden.tree → Mom d) :
    ‖IncTop.starWeight (D.frontS p) (IncTop.topStar (fun _ => Stage1W.frontierG (Rf j0))) K *
        filtWeight (∅ : Finset (GBranch D.T1.garden.tree)) (fun _ => false) M K *
        filtWeight (D.stemF σ) (fun _ => false) (fun _ => regStemScale j0 σ L) K * (D.ind1 dag K : ℂ)‖ ≤ 1 := by
  have h0 : ∀ u, |chi0 u| ≤ 1 := fun u => by
    rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg u)]; exact XChain.ProductCut.chi0_le_one u
  have hs : ‖IncTop.starWeight (D.frontS p) (IncTop.topStar (fun _ => Stage1W.frontierG (Rf j0))) K‖ ≤ 1 := by
    unfold IncTop.starWeight
    rw [norm_prod]
    refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun a _ => ?_
    unfold IncTop.topStar Stage1W.frontierG
    rw [Complex.norm_real, Real.norm_eq_abs]
    cases Rf j0 with
    | none => simp
    | some r => exact h0 _
  have hi : ‖(D.ind1 dag K : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (D.ind1_01 dag K).1]
    exact (D.ind1_01 dag K).2
  rw [filtWeight_empty, mul_one, norm_mul, norm_mul]
  calc _ ≤ 1 * 1 * 1 :=
        mul_le_mul (mul_le_mul hs (filtWeight_norm_le _ _ _ h0) (norm_nonneg _) zero_le_one) hi (norm_nonneg _)
          (by norm_num)
    _ = 1 := by norm_num

/-- **The kernel bound of a wholly regular component.** -/
theorem kernel_bound (P : WTParams) (hptw : ProtPtw.ProtPtwAt P) (hpin : ProtBoundAt P) (hL : 1 ≤ P.L)
    (hη : 0 ≤ P.η) {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hsize : X.size = 2 * n)
    (hG : CapGeo LG {c} p) (hS : StemChain LG {c} X ζ (j0, []) .leaf) {pat : Fin 2 → FixPat}
    (hpat : CapPatValid LG {c} pat p) (hcan : IsCanonGC (p + 1) LG) {t s : ℝ} (hps : (p : ℝ) < s) (hst : s < t)
    (htp : t < p + 1) {kSel : Fin 2 → Option ℕ} (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain)
    (h : ℕ → Fin 2 → Fin 2 → Mom P.d → ℝ) (b : NNReal)
    (hb : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal (b : ℝ))
    (Rf : Fin 2 → Option ℝ) (σ : Fin 2 → Option ℕ) (Rs : Fin 2 → ℝ) (dag : Option (Fin 2 → Fin 3 → Mom P.d))
    (hRf : ∀ r, Rf j0 = some r → 1 ≤ r) (hRs : P.L ≤ Rs j0) (k₀ : Mom P.d) :
    ‖kernelProt P.L P.γ P.δ D.T1 (regH1 LG j0 h) (D.mult p P.L Rf σ Rs kSel dag) (fun _ => t) 0
        ((objCfg LG {c} pat X (j0, [])).fix X s t t) k₀ (fun _ => 0) 0‖ₑ ≤
      (∏ _a ∈ D.frontS p, ENNReal.ofReal (Stage1W.frontierConst P.d)) *
        ENNReal.ofReal (P.L ^ (31 * P.d + 6) * (if (selCap LG {c} kSel j0).isSome then (Rs j0)⁻¹ else 1)) *
        regBound P n (protIncoh X D.T1) * ENNReal.ofReal (leafSizeProduct D.T1 (fun _ => b)) := by
  have hshape : ProtShape p X D.T1 := protShape_objTree hG hS
  have hsz : protSize X D.T1 = 2 * n := hsize
  have hpres : ∀ a ∈ D.frontS p, IncTop.StarPresented (30 * P.d)
      (IncTop.topStar (fun _ => Stage1W.frontierG (Rf j0)) a) (Stage1W.frontierConst P.d) :=
    fun a _ => IncTop.topStar_presented _ (fun _ => Stage1W.gPresented_frontierG P.d (Rf j0) hRf) a
  have hLC := D.leafwise_H1 hG.layer_le h b hb
  have hscale : ∀ x ∈ D.stemF σ, P.L ≤ (fun _ => regStemScale j0 σ P.L) x := fun _ _ => by
    show P.L ≤ 2 ^ ((σ j0).getD 0) * P.L
    have : (1 : ℝ) ≤ 2 ^ ((σ j0).getD 0) := one_le_pow₀ (by norm_num)
    nlinarith
  by_cases hcfg : objCfg LG {c} pat X (j0, []) = .term
  · -- D6a, pointwise
    have hspec := objSelT_spec (J := ({c} : Finset (Fin 2))) hG hS hplain s t t
    have key := hptw p hp n hn 1 D.T1 X hshape hsz true (objSelT (J := ({c} : Finset (Fin 2))) D.emb kSel)
      (fun _ => D.lone_ne_nil hS)
      (fun b' hb' => by
        obtain ⟨h1, h2, h3, h4, -⟩ := hspec b' hb'
        exact ⟨h1, h2, h3, fun _ => h4 hcfg⟩)
      (objSelT_card _ _) (Rs j0) hRs s (D.frontS p) (IncTop.topStar fun _ => Stage1W.frontierG (Rf j0))
      (fun _ => Stage1W.frontierConst P.d) hpres (D.selF kSel) (fun _ => Rs j0) (fun _ _ => hRs)
      (D.stemF σ) (fun _ => regStemScale j0 σ P.L) hscale (D.ind1 dag) (D.termChild_ind1 dag)
      (fun h => absurd h (by simp)) (regH1 LG j0 h) (fun _ => b) hLC t 0 k₀
    have heq : (objCfg LG {c} pat X (j0, [])).fix X s t t =
        (if true = true then ProtCfg.term else ProtCfg.none).fix X s s t (T := D.T1.garden.tree) := by
      rw [hcfg]; rfl
    rw [heq]
    refine key.trans ?_
    gcongr ?_ * ENNReal.ofReal ?_ * _ * _
    · exact le_rfl
    · cases hsel : selCap LG {c} kSel j0 with
      | none =>
        rw [D.objSelT_none kSel hsel]
        simp only [Finset.card_empty, add_zero, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one,
          Option.isSome_none, Bool.false_eq_true, if_false, if_true]
        exact pow_le_pow_right₀ hL (by omega)
      | some vj =>
        rw [D.objSelT_some kSel hsel]
        simp only [Finset.card_singleton, Nat.cast_one, Option.isSome_some, if_true, Real.rpow_neg_one]
        have hR : 0 ≤ (Rs j0)⁻¹ := inv_nonneg.2 (le_trans (by linarith) hRs)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (by omega)) hR
  · -- D3, at the point (t, s)
    have hnone : selCap LG {c} kSel j0 = none := by
      cases hv : selCap LG {c} kSel j0 with
      | none => rfl
      | some vj => exact absurd (D.objCfg_term_of_sel pat hplain (by simp [hv])) hcfg
    set cfg := objCfg LG {c} pat X (j0, []) with hcfgdef
    have hcases : cfg = .term ∨ cfg = .rootTerm ∨ cfg = .penTerm ∨ ∃ i, cfg = .termChild i :=
      D.objCfg_cases pat
    have hnt : cfg ≠ .trace := by
      rcases hcases with h1 | h1 | h1 | ⟨i, h1⟩ <;> rw [h1] <;> simp
    have hnr : ¬ (cfg = .none ∨ cfg = .root ∨ cfg = .trace) := by
      rintro (h1 | h1 | h1) <;> rcases hcases with h2 | h2 | h2 | ⟨i, h2⟩ <;> rw [h1] at h2 <;> simp at h2
    have hζ : nodeSign LG.garden.sig (j0, []) = ζ := by rw [← D.sig]; simp [nodeSign, TTree.pathSign]
    have hamb : ProtAmbient p X D.T1 := ⟨2, LG, (j0, []), .leaf, hcan, D.emb, hζ, fun _ => rfl⟩
    have key := hpin p hp n hn 1 D.T1 X hshape hsz cfg (objCfg_valid_objTree hpat hS) hamb P.η (31 * P.d + 6)
      (Or.inl ⟨rfl, rfl⟩) s t hps hst htp p le_rfl (D.frontS p) (IncTop.topStar fun _ => Stage1W.frontierG (Rf j0))
      (fun _ => Stage1W.frontierConst P.d) hpres ∅ (fun _ => P.L) (by simp) (D.stemF σ)
      (fun _ => regStemScale j0 σ P.L) hscale (D.ind1 dag) (D.termChild_ind1 dag) (fun h => absurd h hnr)
      (regH1 LG j0 h) (fun _ => b) hLC k₀ k₀
    set m3 : (GNode D.T1.garden.tree → Mom P.d) → ℂ := fun κ =>
      IncTop.starWeight (D.frontS p) (IncTop.topStar fun _ => Stage1W.frontierG (Rf j0)) κ *
        filtWeight (∅ : Finset (GBranch D.T1.garden.tree)) (fun _ => false) (fun _ => P.L) κ *
        filtWeight (D.stemF σ) (fun _ => false) (fun _ => regStemScale j0 σ P.L) κ * (D.ind1 dag κ : ℂ) with hm3
    have hmult : D.mult p P.L Rf σ Rs kSel dag = m3 := by
      funext K
      have hsF : D.selF kSel = ∅ := by simp [CapG.selF, hnone]
      unfold mult
      rw [hm3, hsF, D.objSelT_none kSel hnone, Finset.empty_union, filtWeight_empty]
      simp only [filtWeight_empty]
    have hpinned := D.lonePin cfg hcases s t
    have hG' : ∀ ts : Fin 2 → ℝ, kernelProt P.L P.γ P.δ D.T1 (regH1 LG j0 h) m3 (fun _ => ts 0) (ts 1)
        (cfg.fix X s t (ts 0)) k₀ (fun _ => 0) 0 =
        kernelProt P.L P.γ P.δ D.T1 (regH1 LG j0 h) m3 (fun _ => ts 0) 0 (cfg.fix X s t t) k₀ (fun _ => 0) 0 := by
      intro ts
      rw [fix_up_indep cfg hnt X s t (ts 0) t]
      exact kernelProt_port _ _ _ _ _ _ _ _ _ _ _ _ _ (hpinned t)
    have hcont : Continuous fun ts : Fin 2 → ℝ => kernelProt P.L P.γ P.δ D.T1 (regH1 LG j0 h) m3 (fun _ => ts 0)
        (ts 1) (cfg.fix X s t (ts 0)) k₀ (fun _ => 0) 0 := by
      simp only [hG']
      exact (continuous_kernelProt_up P.L P.γ P.δ D.T1 (regH1 LG j0 h) m3 1
        (fun K => D.norm_mult3_le p P.L Rf σ dag _ K) 0 (cfg.fix X s t t) k₀
        (card_lone_le_of_decodesTree (decodedTree_decodes X ζ))
        (D.summable_H1 hG.layer_le h b hb hL k₀)).comp (continuous_apply 0)
    have hk : k₀ ∈ latticeBall P.L k₀ k₀ := ⟨by simp, 0, by simp [WaveTurbulence.Links.latticePoint_zero]⟩
    have hpt := VineEstS3.enorm_le_XNormRestr_of_continuous hη (30 * P.d) 0 (cfg.box X t p p)
      (latticeBall P.L k₀ k₀) (fun ts k => kernelProt P.L P.γ P.δ D.T1 (regH1 LG j0 h) m3 (fun _ => ts 0) (ts 1)
        (cfg.fix X s t (ts 0)) k (fun _ => 0) 0) ![t, s] k₀ (mem_closure_interior_box cfg X hps hst htp) hk hcont
    rw [hmult]
    have hval : kernelProt P.L P.γ P.δ D.T1 (regH1 LG j0 h) m3 (fun _ => t) 0 (cfg.fix X s t t) k₀ (fun _ => 0) 0 =
        kernelProt P.L P.γ P.δ D.T1 (regH1 LG j0 h) m3 (fun _ => (![t, s] : Fin 2 → ℝ) 0)
          ((![t, s] : Fin 2 → ℝ) 1) (cfg.fix X s t ((![t, s] : Fin 2 → ℝ) 0)) k₀ (fun _ => 0) 0 := by
      rw [hG' ![t, s]]
      simp
    rw [hval]
    refine hpt.trans (key.trans ?_)
    simp only [hnone, Option.isSome_none, Bool.false_eq_true, if_false, mul_one]
    rw [show (31 * (P.d : ℝ) + 6) = ((31 * P.d + 6 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]

end CapG

end WaveTurbulence.Flower.ProtWhole
