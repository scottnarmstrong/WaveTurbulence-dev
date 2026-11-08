/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.CapPSup

/-! # B3s-HELPER3 (B5): a nontrivial cap slot under a pattern

For a nontrivial cap slot (B3s's `CapSide`) of the reconstruction with the pattern pins `fixCap … pat`, the relaxed
(R187) slot kernel at the cap momentum is `c₀ · capCfgKer … (ts j0)` (`CapP.capSlot_kernel_pat`, `CapP.cfgKer_m1`),
with `cfg = objCfg … pat X u` (`term`, `rootTerm`, `penTerm` or `termChild i`, valid by D2b). Then, from D3's
`ProtBoundAt`:
* `cfg` does not pin the root (`pinsRoot = false`): the superposition on the whole slot box (`capSlotPat_sup`, the twin
  of B3s's `CapSide.capSlot_sup`);
* `cfg` pins the root (`rootTerm`: root at `t`; `penTerm` with `Xp = nil`: root at `s`): every pin is at most the root
  pin `rootPinVal cfg s t` (`pinsRoot_fix`), so the kernel is CONSTANT in `ts j0 ≥ rootPinVal` (`kernelProt_up_const`)
  and bounded by D3's bound (`capCfg_pointwise` at `t`): `capSlotPat_const`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.VineEstS3.FS WaveTurbulence.Flower.MkSlots

namespace WaveTurbulence.Flower.MkSlotsB

/-! ### The pins of a root-pinning configuration -/

/-- The root pin of a configuration that pins the root: `s` for `penTerm`, `t` otherwise. -/
def rootPinVal (cfg : ProtCfg) (s t : ℝ) : ℝ := if cfg = .penTerm then s else t

theorem rootPinVal_le (cfg : ProtCfg) {s t : ℝ} (hst : s ≤ t) : rootPinVal cfg s t ≤ t := by
  unfold rootPinVal
  split_ifs
  · exact hst
  · exact le_rfl

theorem lookup_some_mem {β : Type*} (a : Path) (l : List (Path × β)) (v : β) (h : l.lookup a = some v) :
    ∃ k, (k, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    obtain ⟨k, v'⟩ := hd
    rw [lookup_cons'] at h
    split_ifs at h with hk
    · refine ⟨k, ?_⟩
      rw [Option.some_inj] at h
      rw [h]
      exact List.mem_cons_self
    · obtain ⟨k', hk'⟩ := ih h
      exact ⟨k', List.mem_cons_of_mem _ hk'⟩

/-- **At a root-pinning configuration the root is pinned at `rootPinVal`, and every pin is at most `rootPinVal`.** -/
theorem pinsRoot_fix {cfg : ProtCfg} {X : RegChain} (hr : cfg.pinsRoot X = true) (s t up : ℝ) (hst : s ≤ t)
    {T : Fin 1 → TTree} :
    (∀ b : GBranch T, b.1.2 = [] → cfg.fix X s t up b = some (rootPinVal cfg s t)) ∧
      ∀ (b : GBranch T) (v : ℝ), cfg.fix X s t up b = some v → v ≤ rootPinVal cfg s t := by
  have h0 : ∀ b : GBranch T, b.1.1.val = 0 := fun b => Fin.val_eq_zero b.1.1
  have hfix : ∀ b : GBranch T, cfg.fix X s t up b = (cfg.pins X s t up).lookup b.1.2 := fun b => by
    unfold ProtCfg.fix
    simp only [h0 b, ↓reduceIte]
  cases cfg with
  | root =>
    refine ⟨fun b hb => ?_, fun b v hv => ?_⟩
    · rw [hfix, hb]
      simp [ProtCfg.pins, rootPinVal]
    · rw [hfix] at hv
      obtain ⟨k, hk⟩ := lookup_some_mem _ _ _ hv
      simp only [ProtCfg.pins, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hk
      rw [hk.2]
      simp [rootPinVal]
  | rootTerm =>
    refine ⟨fun b hb => ?_, fun b v hv => ?_⟩
    · rw [hfix, hb]
      simp [ProtCfg.pins, rootPinVal]
    · rw [hfix] at hv
      obtain ⟨k, hk⟩ := lookup_some_mem _ _ _ hv
      simp only [ProtCfg.pins, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hk
      simp only [rootPinVal, reduceCtorEq, ↓reduceIte]
      rcases hk with hk | hk
      · rw [hk.2]
      · rw [hk.2]; exact hst
  | penTerm =>
    have hXp : X.lonePath.dropLast.dropLast = [] := by
      simpa [ProtCfg.pinsRoot] using hr
    refine ⟨fun b hb => ?_, fun b v hv => ?_⟩
    · rw [hfix, hb]
      simp [ProtCfg.pins, rootPinVal, hXp]
    · rw [hfix] at hv
      obtain ⟨k, hk⟩ := lookup_some_mem _ _ _ hv
      simp only [ProtCfg.pins, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hk
      simp only [rootPinVal, ↓reduceIte]
      rcases hk with hk | hk
      · rw [hk.2]
      · rw [hk.2]
  | none => simp [ProtCfg.pinsRoot] at hr
  | term => simp [ProtCfg.pinsRoot] at hr
  | termChild i => simp [ProtCfg.pinsRoot] at hr
  | trace => simp [ProtCfg.pinsRoot] at hr

namespace CapP

variable {w : ℕ} {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {J : Finset (Fin w)}
  {q : SourcePair S} (K : CapSide D hS J q)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {p : ℕ} (hGeo : CapGeo (layeredReconstruction D hS layer hLayer) J p)

theorem cfgPat_valid {pat : Fin w → FixPat} (hpat : CapPatValid (layeredReconstruction D hS layer hLayer) J pat p) :
    (cfgPat K layer hLayer pat).Valid K.X (K.Dq layer hLayer).T1 p := by
  rw [K.capT1_eq layer hLayer]
  exact objCfg_valid_objTree hpat (K.capStem layer hLayer)

/-- The root branch of the paired tree. -/
def rootT1 : GBranch (K.Dq layer hLayer).T1.garden.tree :=
  ⟨((0 : Fin 1), []), by
    show [] ∈ (K.X.plug K.ζ .leaf).branching
    exact prefix_lone_branching K.X K.ζ List.nil_prefix (lonePath_ne_nil K.ne).symm⟩

include hGeo in
/-- **The slot kernel of a nontrivial cap slot under a pattern, as a function of the chain clock.** -/
theorem capSlotPat_eq {d : ℕ} (L γ δ : ℝ) (pat : Fin w → FixPat) (t s : ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (roots : Fin w → (Fin d → ℤ)) (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d))
    (ts : Fin 2 → ℝ) :
    slotFnGWFRL D hS L γ δ (anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots)
        (capNodeW L γ δ p s (layeredReconstruction D hS layer hLayer) J Rf dag) (fun _ _ _ => 1) layer hLayer
        (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inl q) ts (latticePoint L (roots K.cleaf.1.1)) =
      K.capC0 L γ δ s (latticePoint L (roots K.cleaf.1.1)) dag *
        capCfgKer L γ δ (K.Dq layer hLayer)
          (CapG.capH1 K.j0 (MkSlots.CapSide.Hq (q := q) layer hLayer
            (anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots)))
          (fun K' => IncTop.starWeight (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) K' *
            (K.capInd layer hLayer dag K' : ℂ))
          (cfgPat K layer hLayer pat) s t (latticePoint L (roots K.cleaf.1.1)) (ts K.j0) :=
  (capSlot_kernel_pat K layer hLayer hGeo L γ δ pat t s _ _ ts _).trans
    (cfgKer_m1 K layer hLayer hGeo L γ δ s h roots Rf dag _ _ 0 _)

include hGeo in
/-- **The superposition of a nontrivial cap slot whose configuration does not pin the root**, from D3. -/
theorem capSlotPat_sup {P : WTParams} (hD3 : ProtBoundAt P) {Csup : ℝ≥0∞} (hC : CapSupProp P.d P.η Csup)
    (hη : 0 ≤ P.η) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (hcan : IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer)) (hp : p < P.D)
    (hsize : D.size ≤ P.N (p + 1) ^ 4) {pat : Fin w → FixPat}
    (hpat : CapPatValid (layeredReconstruction D hS layer hLayer) J pat p)
    (hroot : (cfgPat K layer hLayer pat).pinsRoot K.X = false)
    {t s : ℝ} (hps : (p : ℝ) < s) (hst : s < t) (htp : t < p + 1)
    (h : ℕ → Fin w → Fin w → Mom P.d → ℝ) (b : ℝ) (hb1 : 1 ≤ b)
    (hb : ∀ q' ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q' j j') ≤ ENNReal.ofReal b)
    (Rf : Fin w → Option ℝ) (hRf : ∀ j r, Rf j = some r → 1 ≤ r) (dag : Option (Fin w → Fin 3 → Mom P.d))
    (roots : Fin w → (Fin P.d → ℤ)) :
    ∃ (wt : (Fin 2 → ℤ) → ℝ) (u : (Fin 2 → ℤ) → ℂ), (∀ m, 0 ≤ wt m) ∧ Summable wt ∧ (∀ m, ‖u m‖ ≤ 1) ∧
      (∀ ts ∈ Represents.slotBox p (fun b => layer (D.coreBranch hS b).toNode) hS (.inl q),
        HasSum (fun m => (wt m : ℂ) * u m * fsPhase (capMode K.j0 m) ts)
          (slotFnGWFRL D hS P.L P.γ P.δ (anchProfiles J (layeredReconstruction D hS layer hLayer) h P.L roots)
            (capNodeW P.L P.γ P.δ p s (layeredReconstruction D hS layer hLayer) J Rf dag) (fun _ _ _ => 1) layer
            hLayer (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inl q) ts
            (latticePoint P.L (roots K.cleaf.1.1)))) ∧
      ∑' m, maxBracketPow P.η (half (capMode K.j0 m)) * ENNReal.ofReal (wt m) ≤
        Csup * (2 * ((∏ _a ∈ K.frontS layer hLayer p, ENNReal.ofReal (frontierConst P.d)) *
          ENNReal.ofReal (P.L ^ (31 * (P.d : ℝ) + 6)) *
          regBound P (K.X.size / 2) (Represents.slotIncoh D hS layer hLayer (.inl q)) *
          ENNReal.ofReal (b⁻¹ * Represents.slotLeaf D hS layer hLayer (fun _ => b.toNNReal) (.inl q)))) := by
  set x₀ := latticePoint P.L (roots K.cleaf.1.1)
  have hb0 : 0 ≤ b := le_trans zero_le_one hb1
  have hsz : protSize K.X (K.Dq layer hLayer).T1 = 2 * (K.X.size / 2) := by
    show K.X.size = 2 * (K.X.size / 2)
    obtain ⟨r, hr⟩ := chain_size_even K.X
    omega
  have hn : K.X.size / 2 ≤ P.N (p + 1) ^ 4 := by
    have h1 : K.X.size ≤ D.size := K.slotSize_eq ▸ Represents.slotSize_le D (.inl q)
    omega
  have hpres : ∀ a ∈ K.frontS layer hLayer p, IncTop.StarPresented (30 * P.d)
      (IncTop.topStar (fun _ => frontierG (Rf K.u.1)) a) (frontierConst P.d) :=
    fun a _ => IncTop.topStar_presented _ (fun _ => gPresented_frontierG P.d (Rf K.u.1) (hRf K.u.1)) a
  have hm : ∀ K', ‖IncTop.starWeight (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) K' *
      (K.capInd layer hLayer dag K' : ℂ)‖ ≤ 1 := by
    intro K'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (K.capInd_01 layer hLayer dag K').1]
    calc _ ≤ 1 * 1 := mul_le_mul (K.norm_starWeight_le layer hLayer p Rf K') (K.capInd_01 layer hLayer dag K').2
          (K.capInd_01 layer hLayer dag K').1 zero_le_one
      _ = 1 := one_mul 1
  obtain ⟨wt, u, hw0, hws, hu, hsum, hmass⟩ := capCfg_sup hD3 hC hη hd hL (K.Dq layer hLayer) hp hn
    (K.protShape_T1 layer hLayer hGeo) hsz (cfgPat K layer hLayer pat) (cfgPat_valid K layer hLayer hpat)
    (objCfg_cases K layer hLayer pat) hroot (K.protAmbient_T1 layer hLayer hcan) hps hst htp
    (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) (fun _ => frontierConst P.d) hpres
    (K.capInd layer hLayer dag) (K.termChild_capInd layer hLayer dag) 1 hm
    (CapG.capH1 K.j0 (MkSlots.CapSide.Hq (q := q) layer hLayer
      (anchProfiles J (layeredReconstruction D hS layer hLayer) h P.L roots))) (fun _ => b.toNNReal)
    (K.capH1_leafwise layer hLayer hGeo h P.L roots b hb0 hb) x₀
  set c₀ := K.capC0 P.L P.γ P.δ s x₀ dag
  have hc₀ : ‖c₀‖ = 1 := K.norm_capC0 P.L P.γ P.δ s x₀ dag
  set F : ℝ → ℂ := fun x => c₀ * capCfgKer P.L P.γ P.δ (K.Dq layer hLayer)
    (CapG.capH1 K.j0 (MkSlots.CapSide.Hq (q := q) layer hLayer
      (anchProfiles J (layeredReconstruction D hS layer hLayer) h P.L roots)))
    (fun K' => IncTop.starWeight (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) K' *
      (K.capInd layer hLayer dag K' : ℂ)) (cfgPat K layer hLayer pat) s t x₀ x with hF
  have hsumF : ∀ x ∈ Set.Icc (p : ℝ) (p + 1),
      HasSum (fun m => (wt m : ℂ) * (c₀ * u m) * fsPhase m ![x, p]) (F x) := by
    intro x hx
    refine ((hsum x hx).mul_left c₀).congr_fun fun m => ?_
    ring
  have hcu : ∀ m, ‖c₀ * u m‖ ≤ 1 := fun m => by rw [norm_mul, hc₀, one_mul]; exact hu m
  obtain ⟨hu', hbox⟩ := capSup_box K.j0 (p : ℝ) F wt (fun m => c₀ * u m) id hcu hsumF
    (Represents.slotBox p (fun b => layer (D.coreBranch hS b).toNode) hS (.inl q))
    (fun ts hts => K.slotBox_j0 layer hLayer hGeo ts hts)
  refine ⟨wt, fun m => c₀ * u m * fsPhase m ![0, p], hw0, hws, hu', fun ts hts => ?_, ?_⟩
  · rw [capSlotPat_eq K layer hLayer hGeo P.L P.γ P.δ pat t s h roots Rf dag ts]
    exact hbox ts hts
  · refine le_trans (ENNReal.tsum_le_tsum fun m => mul_le_mul_left (maxBracketPow_capMode_le hη K.j0 m) _ |>.trans'
      le_rfl) (hmass.trans ?_)
    rw [K.protIncoh_T1 layer hLayer]
    gcongr
    exact K.leafSize_T1_le layer hLayer b hb1

include hGeo in
/-- **A nontrivial cap slot whose configuration pins the root is constant above the root pin**, with D3's bound. -/
theorem capSlotPat_const {P : WTParams} (hD3 : ProtBoundAt P) (hη : 0 ≤ P.η) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (hcan : IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer)) (hp : p < P.D)
    (hsize : D.size ≤ P.N (p + 1) ^ 4) {pat : Fin w → FixPat}
    (hpat : CapPatValid (layeredReconstruction D hS layer hLayer) J pat p)
    (hroot : (cfgPat K layer hLayer pat).pinsRoot K.X = true)
    {t s : ℝ} (hps : (p : ℝ) < s) (hst : s < t) (htp : t < p + 1)
    (h : ℕ → Fin w → Fin w → Mom P.d → ℝ) (b : ℝ) (hb1 : 1 ≤ b)
    (hb : ∀ q' ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q' j j') ≤ ENNReal.ofReal b)
    (Rf : Fin w → Option ℝ) (hRf : ∀ j r, Rf j = some r → 1 ≤ r) (dag : Option (Fin w → Fin 3 → Mom P.d))
    (roots : Fin w → (Fin P.d → ℤ)) :
    ∃ V : ℂ, ‖V‖ₑ ≤ (∏ _a ∈ K.frontS layer hLayer p, ENNReal.ofReal (frontierConst P.d)) *
          ENNReal.ofReal (P.L ^ (31 * (P.d : ℝ) + 6)) *
          regBound P (K.X.size / 2) (Represents.slotIncoh D hS layer hLayer (.inl q)) *
          ENNReal.ofReal (b⁻¹ * Represents.slotLeaf D hS layer hLayer (fun _ => b.toNNReal) (.inl q)) ∧
      ∀ ts : Fin 2 → ℝ, rootPinVal (cfgPat K layer hLayer pat) s t ≤ ts K.j0 →
        slotFnGWFRL D hS P.L P.γ P.δ (anchProfiles J (layeredReconstruction D hS layer hLayer) h P.L roots)
          (capNodeW P.L P.γ P.δ p s (layeredReconstruction D hS layer hLayer) J Rf dag) (fun _ _ _ => 1) layer
          hLayer (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inl q) ts
          (latticePoint P.L (roots K.cleaf.1.1)) = V := by
  set x₀ := latticePoint P.L (roots K.cleaf.1.1)
  have hb0 : 0 ≤ b := le_trans zero_le_one hb1
  have hsz : protSize K.X (K.Dq layer hLayer).T1 = 2 * (K.X.size / 2) := by
    show K.X.size = 2 * (K.X.size / 2)
    obtain ⟨r, hr⟩ := chain_size_even K.X
    omega
  have hn : K.X.size / 2 ≤ P.N (p + 1) ^ 4 := by
    have h1 : K.X.size ≤ D.size := K.slotSize_eq ▸ Represents.slotSize_le D (.inl q)
    omega
  have hpres : ∀ a ∈ K.frontS layer hLayer p, IncTop.StarPresented (30 * P.d)
      (IncTop.topStar (fun _ => frontierG (Rf K.u.1)) a) (frontierConst P.d) :=
    fun a _ => IncTop.topStar_presented _ (fun _ => gPresented_frontierG P.d (Rf K.u.1) (hRf K.u.1)) a
  have hm : ∀ K', ‖IncTop.starWeight (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) K' *
      (K.capInd layer hLayer dag K' : ℂ)‖ ≤ 1 := by
    intro K'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (K.capInd_01 layer hLayer dag K').1]
    calc _ ≤ 1 * 1 := mul_le_mul (K.norm_starWeight_le layer hLayer p Rf K') (K.capInd_01 layer hLayer dag K').2
          (K.capInd_01 layer hLayer dag K').1 zero_le_one
      _ = 1 := one_mul 1
  set cfg := cfgPat K layer hLayer pat with hcfgdef
  have hcfg := objCfg_cases K layer hLayer pat
  have hne := cfg_ne_trace cfg hcfg
  set H1 := CapG.capH1 K.j0 (MkSlots.CapSide.Hq (q := q) layer hLayer
      (anchProfiles J (layeredReconstruction D hS layer hLayer) h P.L roots))
  set mW : (GNode (K.Dq layer hLayer).T1.garden.tree → Mom P.d) → ℂ := fun K' =>
    IncTop.starWeight (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) K' *
      (K.capInd layer hLayer dag K' : ℂ)
  set G := capCfgKer P.L P.γ P.δ (K.Dq layer hLayer) H1 mW cfg s t x₀ with hG
  have hconst : ∀ x, rootPinVal cfg s t ≤ x → G x = G t := by
    intro x hx
    rw [hG]
    unfold capCfgKer
    rw [fix_up_indep cfg hne K.X s t x 0, fix_up_indep cfg hne K.X s t t 0]
    obtain ⟨hr1, hr2⟩ := pinsRoot_fix hroot s t 0 hst.le (T := (K.Dq layer hLayer).T1.garden.tree)
    exact kernelProt_up_const _ _ _ _ _ _ 0 _ _ _ _ (rootPinVal cfg s t)
      (fun b hb => by rw [hr1 b hb]; exact Option.some_ne_none _) hr2 x t hx (rootPinVal_le cfg hst.le)
  have hbound := capCfg_pointwise hD3 (K.Dq layer hLayer) hη hd hL hp hn (K.protShape_T1 layer hLayer hGeo) hsz cfg
    (cfgPat_valid K layer hLayer hpat) hcfg hroot (K.protAmbient_T1 layer hLayer hcan) hps hst htp
    (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) (fun _ => frontierConst P.d) hpres
    (K.capInd layer hLayer dag) (K.termChild_capInd layer hLayer dag) 1 hm H1 (fun _ => b.toNNReal)
    (K.capH1_leafwise layer hLayer hGeo h P.L roots b hb0 hb) x₀ t ⟨le_rfl, htp.le⟩
  set c₀ := K.capC0 P.L P.γ P.δ s x₀ dag
  have hc₀ : ‖c₀‖ = 1 := K.norm_capC0 P.L P.γ P.δ s x₀ dag
  refine ⟨c₀ * G t, ?_, fun ts hts => ?_⟩
  · rw [← ofReal_norm, norm_mul, hc₀, one_mul, ofReal_norm]
    refine hbound.trans ?_
    rw [K.protIncoh_T1 layer hLayer]
    gcongr
    exact K.leafSize_T1_le layer hLayer b hb1
  · rw [capSlotPat_eq K layer hLayer hGeo P.L P.γ P.δ pat t s h roots Rf dag ts]
    exact congrArg (c₀ * ·) (hconst _ hts)

end CapP

end WaveTurbulence.Flower.MkSlotsB
