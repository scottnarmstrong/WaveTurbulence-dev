/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.CapMass
public import WaveTurbulence.Foundations.Flower.MkSlots.CapCen

/-! # B3s MK-SLOTS (cap slots): the superposition of a nontrivial cap slot

`capSlot_sup_nontriv`: at a parameter record where D3's `ProtBoundNTAt` holds, the pinned slot kernel of a
nontrivial cap slot, at the cap momentum, is on the slot box a superposition (modes `capMode j0 m`, amplitudes
`|u| ≤ 1`) with moment mass at most `C · 2 · c_F^{#frontS} · L^{31d+6} · regBound · b⁻¹ · slotLeaf`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.VineEstS3.FS

namespace WaveTurbulence.Flower.MkSlots

namespace CapSide

variable {w : ℕ} {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {J : Finset (Fin w)}
  {q : SourcePair S} (K : CapSide D hS J q)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {p : ℕ} (hGeo : CapGeo (layeredReconstruction D hS layer hLayer) J p)

include hGeo in
/-- **The superposition of a nontrivial cap slot**, from D3. -/
theorem capSlot_sup {P : WTParams} (hD3 : ProtPin.ProtBoundNTAt P) {Csup : ℝ≥0∞} (hC : CapSupProp P.d P.η Csup)
    (hη : 0 ≤ P.η) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (hcan : IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer)) (hp : p < P.D)
    (hsize : D.size ≤ P.N (p + 1) ^ 4) {t s : ℝ} (hps : (p : ℝ) < s) (hst : s < t) (htp : t < p + 1)
    (h : ℕ → Fin w → Fin w → Mom P.d → ℝ) (b : ℝ) (hb1 : 1 ≤ b)
    (hb : ∀ q' ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q' j j') ≤ ENNReal.ofReal b)
    (Rf : Fin w → Option ℝ) (hRf : ∀ j r, Rf j = some r → 1 ≤ r) (dag : Option (Fin w → Fin 3 → Mom P.d))
    (roots : Fin w → (Fin P.d → ℤ)) :
    ∃ (wt : (Fin 2 → ℤ) → ℝ) (u : (Fin 2 → ℤ) → ℂ), (∀ m, 0 ≤ wt m) ∧ Summable wt ∧ (∀ m, ‖u m‖ ≤ 1) ∧
      (∀ ts ∈ Represents.slotBox p (fun b => layer (D.coreBranch hS b).toNode) hS (.inl q),
        HasSum (fun m => (wt m : ℂ) * u m * fsPhase (capMode K.j0 m) ts)
          (slotFnNWF D hS P.L P.γ P.δ (anchProfiles J (layeredReconstruction D hS layer hLayer) h P.L roots)
            (capNodeW P.L P.γ P.δ p s (layeredReconstruction D hS layer hLayer) J Rf dag) layer hLayer
            (fixCap (layeredReconstruction D hS layer hLayer) J (fun _ => FixPat.plain) t s) (.inl q) ts
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
    exact mul_le_one₀ (K.norm_starWeight_le layer hLayer p Rf K') (K.capInd_01 layer hLayer dag K').1
      (K.capInd_01 layer hLayer dag K').2
  obtain ⟨wt, u, hw0, hws, hu, hsum, hmass⟩ := capTerm_sup hD3 hC hη hd hL (K.Dq layer hLayer) hp hn
    (K.protShape_T1 layer hLayer hGeo) hsz (lonePath_ne_nil K.ne) (K.protAmbient_T1 layer hLayer hcan) hps hst htp
    (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) (fun _ => frontierConst P.d) hpres
    (K.capInd layer hLayer dag) (K.termChild_capInd layer hLayer dag) 1 hm
    (CapG.capH1 K.j0 (Hq (q := q) layer hLayer (anchProfiles J (layeredReconstruction D hS layer hLayer) h P.L roots))) (fun _ => b.toNNReal)
    (K.capH1_leafwise layer hLayer hGeo h P.L roots b hb0 hb) x₀
  set c₀ := K.capC0 P.L P.γ P.δ s x₀ dag
  have hc₀ : ‖c₀‖ = 1 := K.norm_capC0 P.L P.γ P.δ s x₀ dag
  -- the slot function as a function of the chain clock
  set F : ℝ → ℂ := fun x => c₀ * capTermKer P.L P.γ P.δ (K.Dq layer hLayer)
    (CapG.capH1 K.j0 (Hq (q := q) layer hLayer (anchProfiles J (layeredReconstruction D hS layer hLayer) h P.L roots)))
    (fun K' => IncTop.starWeight (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) K' *
      (K.capInd layer hLayer dag K' : ℂ)) s t x₀ x with hF
  have hslot : ∀ ts, slotFnNWF D hS P.L P.γ P.δ (anchProfiles J (layeredReconstruction D hS layer hLayer) h P.L roots)
      (capNodeW P.L P.γ P.δ p s (layeredReconstruction D hS layer hLayer) J Rf dag) layer hLayer (fixCap (layeredReconstruction D hS layer hLayer) J (fun _ => FixPat.plain) t s) (.inl q) ts x₀ =
      F (ts K.j0) := by
    intro ts
    exact (K.capSlot_kernel layer hLayer hGeo P.L P.γ P.δ t s hps (hst.trans htp) _ _ ts x₀).trans
      (K.capTermKer_m1 layer hLayer hGeo P.L P.γ P.δ s t h roots Rf dag _ (ts K.j0))
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
  · rw [hslot ts]
    exact hbox ts hts
  · refine le_trans (ENNReal.tsum_le_tsum fun m => mul_le_mul_left (maxBracketPow_capMode_le hη K.j0 m) _ |>.trans'
      le_rfl) (hmass.trans ?_)
    rw [K.protIncoh_T1 layer hLayer]
    gcongr
    exact K.leafSize_T1_le layer hLayer b hb1

end CapSide

end WaveTurbulence.Flower.MkSlots
