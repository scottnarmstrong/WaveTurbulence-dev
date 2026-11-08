/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.RT2Ker
public import WaveTurbulence.Foundations.Flower.ProtRT.RT2Aux
public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2ATrace

/-! # RT-GATE (ii), both roots pinned: a type-2 couple with a nonempty `+` chain, pointwise

Both roots (layer `p`) pinned at `s`. D2c's type-2 root cut with the second root pinned (`rt2_kernelProt_root2`):
`c²(iζ_a)(iζ_b) Σ'_e Mc ε_e ∫_{root2U} e^{πiA_e(s−u)} K_rest(u) K_int Q_r Q_g(s, u) du`, `K_rest` the rest couple with
its tree-`1` root pinned at `s` and its tree `0` at `u ∈ (𝔏_b, 𝔏_b + 1)`: a ONE-pinned couple, partner window `𝔏_b`,
bounded in `L¹(du)` by `RtOne` (`rt2_lint_le_rn`). The closing-pair pieces pointwise (D3-HELPER's `tc2a_core`,
ProtPin/TChild2A.lean; copy recorded in RT2-COPIED.md), the exceptional sum by `(latC L^d)²`, `RtOne`'s output
weight `tcWt`, two cuts `c²(latC L^d)² · c² C₁⁶ rb(n−2)`, the lost root link `L` (`rb_pred_le`) and `RtOne`'s `L`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **A type-2 couple with a nonempty `+` chain and both roots pinned at `s`**, pointwise. -/
theorem rt2_t2a_both {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) {Ct₁ : ℝ} (hCt₁ : 0 ≤ Ct₁) (h1 : RtOne θ 0 Ct₁) :
    ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b)
      (_hFC : TcFC P) (_hC11 : 1 ≤ P.C₁) (_hθc : PieceLoss P θ 0) {p : ℕ} (_hp : p < P.D) {n : ℕ}
      (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest Xm : RegChain} {Qlp : RegCpl}
      {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2} (D : Root2Data LG m Qr Qg inner LGZ LGB)
      {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} (Pp : PairOnly LGZ m Qr Qg inner LGi LGr LGg)
      (_hdB : (SourceApp.closeCouple rest Xm Qlp).Decodes LGB.garden) (_hsZ : LGZ.garden.sig 0 = 1)
      (_hwf : (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).wf = true)
      (_hsz : (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).size = 2 * n)
      (_hdec : (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).Decodes LG.garden) (_hle : ∀ a, LG.layer a ≤ p)
      (_hA : TcCplAmbS p (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp) LG)
      (_hj : ∀ t : Fin 2, layerAt LG (t, []) = p) (_hjb1 : ([] : TTree.Path) ∈ (LG.garden.tree 1).branching)
      {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1)
      (Hr : LeafProfiles 2 P.d) (Br : (Fin 2 × TTree.Path) → NNReal) (_hHr : LeafwiseControlled LG Hr Br)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (k : Mom P.d),
      ‖kernelProt P.L P.γ P.δ LG Hr (gateM S ω F M Fu Mu) (fun _ => s) 0 (MkSlotsO.rootPins (fun _ => True) s) k
          (fun _ => 0) 0‖ₑ ≤
        ENNReal.ofReal (Ct₁ * (P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 *
            rb P (n - 2) (LG.incoherency (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).links)))) *
              leafSizeProduct LG Br * starCost S cω)) * tcWt P.L k := by
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp n hn LG m Qr Qg inner rest Xm Qlp LGZ LGB D LGi LGr LGg Pp hdB hsZ hwf
    hsz hdec hle hA hj0 hjb1 s hps hsp Hr Br hHr S ω cω hpres F M hM Fu Mu hMu k
  have hj : layerAt LG ((0 : Fin 2), []) = p := hj0 0
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hd1 : 1 ≤ P.d := by have := K.hd; omega
  have hrb : ∀ j g, 0 ≤ rb P j g := fun j g => rb_nonneg hC1 K.hδ hL0 j g
  obtain ⟨hwI, hwR, hwG, hwB⟩ := tc2a_wf hwf
  obtain ⟨nB, nI, nR, nG, hnB, hnI, hnR, hnG, hnsum⟩ := tc2a_sizes hsz
  obtain ⟨hHB, hHI, hHR, hHG⟩ := tc2a_leafwise D Pp hHr
  have hleA := layerAt_le_of_forall_layer_le hle
  have hle_n : ∀ i, i ≤ n → i ≤ P.N (p + 1) ^ 4 := fun i hi => hi.trans hn
  -- layers
  set 𝔏 : ℕ := layerAt LG ((0 : Fin 2), bPath m inner) with h𝔏
  have h𝔏p : 𝔏 ≤ p := hleA _
  have h𝔏pR : (𝔏 : ℝ) ≤ p := by exact_mod_cast h𝔏p
  have hleB : ∀ a, LGB.layer a ≤ p := fun a => by rw [D.layB]; exact hleA _
  have hleI : ∀ a, LGi.layer a ≤ p := fun a => by rw [← layerAt_node, tc2a_layI D Pp a.1 a.2]; exact hleA _
  have hleR : ∀ a, LGr.layer a ≤ p := fun a => by rw [← layerAt_node, tc2a_layR D Pp a.1 a.2]; exact hleA _
  have hleG : ∀ a, LGg.layer a ≤ p := fun a => by rw [← layerAt_node, tc2a_layG D Pp a.1 a.2]; exact hleA _
  have hrB0 := tc2a_rootB0_le D Pp hle
  have hrB1 : LGB.layer (GNode.root LGB.garden.tree 1) ≤ p := hleB _
  have hrI := tc2a_rootI_le D Pp hle hj
  have hloneI := tc2a_loneI D Pp
  have hrR := tc2a_rootR_le D Pp hle hj
  have hrG := tc2a_rootG_le D Pp hle hj
  -- coherence
  have hcB : LGB.incoherency (SourceApp.closeCouple rest Xm Qlp).links = 0 →
      IsCoherentCoupleAt p 𝔏 p (SourceApp.closeCouple rest Xm Qlp) LGB := fun h0 => tc2a_cohB D Pp hA hwB hdB h0
  have hcI : LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) = 0 → IsCoherentTreeAt p p 𝔏 inner LGi :=
    fun h0 => tc2a_cohI D Pp hsZ hA hj hwI h0
  have hcR : LGr.incoherency Qr.links = 0 → IsCoherentCoupleAt p (tc2aQR m inner (LGZ.garden.sig 0) p 𝔏 0)
      (tc2aQR m inner (LGZ.garden.sig 0) p 𝔏 1) Qr LGr := fun h0 => by
    have := tc2a_cohR D Pp hsZ hA hwR h0; rwa [hj] at this
  have hcG : LGg.incoherency Qg.links = 0 → IsCoherentCoupleAt p (tc2aQG m inner (LGZ.garden.sig 0) p 𝔏 0)
      (tc2aQG m inner (LGZ.garden.sig 0) p 𝔏 1) Qg LGg := fun h0 => by
    have := tc2a_cohG D Pp hsZ hA hwG h0; rwa [hj] at this
  -- multipliers
  set ζ : ℤˣ := LGZ.garden.sig 0 with hζ
  set Sb := tc2aSb S with hSb
  set SB := tc2aSB D S with hSB
  set ωB : GNode LGB.garden.tree → Flower.IncTop.Star P.d → ℂ := fun z => ω (D.gd.ι₂ z) with hωB
  set cB : GNode LGB.garden.tree → ℝ := fun z => cω (D.gd.ι₂ z) with hcBd
  set FB := pullF (fun y => D.gd.ofSum (.inr y)) F with hFB
  set MB' : GBranch LGB.garden.tree → ℝ := fun y => M (D.gd.ofSum (.inr y)) with hMB'
  set FuB := pullF (fun y => D.gd.ofSum (.inr y)) Fu with hFuB
  set MuB : GBranch LGB.garden.tree → ℝ := fun y => Mu (D.gd.ofSum (.inr y)) with hMuB
  set mB := gateM SB ωB FB MB' FuB MuB with hmB
  set mI := pullMult (fun z => D.gd.ι₁ (Pp.hp.ιi z)) (fun x => D.gd.ofSum (.inl (Pp.hp.βi x))) Sb ω F M Fu Mu
    with hmI
  set mR := pullMult (fun z => D.gd.ι₁ (Pp.hp.ιr z)) (fun y => D.gd.ofSum (.inl (Pp.hp.βr y))) Sb ω F M Fu Mu
    with hmR
  set mG := pullMult (fun z => D.gd.ι₁ (Pp.hp.ιg z)) (fun y => D.gd.ofSum (.inl (Pp.hp.βg y))) Sb ω F M Fu Mu
    with hmG
  obtain ⟨hMg, hMZ⟩ := tc2a_mult D Pp S ω F M Fu Mu
  have hpB : ∀ z ∈ SB, Flower.IncTop.StarPresented (30 * P.d) (ωB z) (cB z) := tc2a_presB D hpres
  have hpSb : ∀ a ∈ Sb, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a) := tc2a_presSb hpres
  have hGI := pull_pres (J := 30 * P.d) (fun z => D.gd.ι₁ (Pp.hp.ιi z)) hpSb
  have hGR := pull_pres (J := 30 * P.d) (fun z => D.gd.ι₁ (Pp.hp.ιr z)) hpSb
  have hGG := pull_pres (J := 30 * P.d) (fun z => D.gd.ι₁ (Pp.hp.ιg z)) hpSb
  have hmBB := FiltCoh.norm_d5Mult_le SB ωB cB hpB FB (fun _ => false) MB' FuB MuB
  have hmIB := FiltCoh.norm_d5Mult_le (pullS (fun z => D.gd.ι₁ (Pp.hp.ιi z)) Sb) (fun z => ω (D.gd.ι₁ (Pp.hp.ιi z)))
    (fun z => cω (D.gd.ι₁ (Pp.hp.ιi z))) hGI (pullF (fun x => D.gd.ofSum (.inl (Pp.hp.βi x))) F) (fun _ => false)
    (fun y => M (D.gd.ofSum (.inl (Pp.hp.βi y)))) (pullF (fun x => D.gd.ofSum (.inl (Pp.hp.βi x))) Fu)
    (fun y => Mu (D.gd.ofSum (.inl (Pp.hp.βi y))))
  have hmRB := FiltCoh.norm_d5Mult_le (pullS (fun z => D.gd.ι₁ (Pp.hp.ιr z)) Sb) (fun z => ω (D.gd.ι₁ (Pp.hp.ιr z)))
    (fun z => cω (D.gd.ι₁ (Pp.hp.ιr z))) hGR (pullF (fun x => D.gd.ofSum (.inl (Pp.hp.βr x))) F) (fun _ => false)
    (fun y => M (D.gd.ofSum (.inl (Pp.hp.βr y)))) (pullF (fun x => D.gd.ofSum (.inl (Pp.hp.βr x))) Fu)
    (fun y => Mu (D.gd.ofSum (.inl (Pp.hp.βr y))))
  have hmGB := FiltCoh.norm_d5Mult_le (pullS (fun z => D.gd.ι₁ (Pp.hp.ιg z)) Sb) (fun z => ω (D.gd.ι₁ (Pp.hp.ιg z)))
    (fun z => cω (D.gd.ι₁ (Pp.hp.ιg z))) hGG (pullF (fun x => D.gd.ofSum (.inl (Pp.hp.βg x))) F) (fun _ => false)
    (fun y => M (D.gd.ofSum (.inl (Pp.hp.βg y)))) (pullF (fun x => D.gd.ofSum (.inl (Pp.hp.βg x))) Fu)
    (fun y => Mu (D.gd.ofSum (.inl (Pp.hp.βg y))))
  set BB : ℝ := (∏ a ∈ SB, max (cB a) 0) * FiltCoh.chiDSup ^ FB.card * FiltCoh.chiDSup ^ FuB.card with hBB
  set BI : ℝ := (∏ a ∈ pullS (fun z => D.gd.ι₁ (Pp.hp.ιi z)) Sb, max (cω (D.gd.ι₁ (Pp.hp.ιi a))) 0) *
    FiltCoh.chiDSup ^ (pullF (fun x => D.gd.ofSum (.inl (Pp.hp.βi x))) F).card *
    FiltCoh.chiDSup ^ (pullF (fun x => D.gd.ofSum (.inl (Pp.hp.βi x))) Fu).card with hBI
  set BR : ℝ := (∏ a ∈ pullS (fun z => D.gd.ι₁ (Pp.hp.ιr z)) Sb, max (cω (D.gd.ι₁ (Pp.hp.ιr a))) 0) *
    FiltCoh.chiDSup ^ (pullF (fun x => D.gd.ofSum (.inl (Pp.hp.βr x))) F).card *
    FiltCoh.chiDSup ^ (pullF (fun x => D.gd.ofSum (.inl (Pp.hp.βr x))) Fu).card with hBR
  set BG : ℝ := (∏ a ∈ pullS (fun z => D.gd.ι₁ (Pp.hp.ιg z)) Sb, max (cω (D.gd.ι₁ (Pp.hp.ιg a))) 0) *
    FiltCoh.chiDSup ^ (pullF (fun x => D.gd.ofSum (.inl (Pp.hp.βg x))) F).card *
    FiltCoh.chiDSup ^ (pullF (fun x => D.gd.ofSum (.inl (Pp.hp.βg x))) Fu).card with hBG
  set Ca : ℝ := costB Sb cω (D.aR Pp) * costB Sb cω (D.bR Pp) with hCa
  have hCa0 : 0 ≤ Ca := mul_nonneg (costB_nonneg _ _ _) (costB_nonneg _ _ _)
  have hMc := tc2a_Mc_le D Pp S ω cω hpres F M Fu Mu
  set CM : ℝ := max BB (max Ca (max BI (max BR BG))) with hCMd
  have hHs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom P.d,
      Summable fun i : Fin P.d → ℤ => |Hr ℓ.1 (k' + latticePoint P.L i)| :=
    fun ℓ hℓ k' => summable_coset_piece hHr hL1 k' ℓ hℓ
  -- profiles
  set HB := t2HQ (cpair m Qr Qg inner) Hr with hHBd
  set HI := cutHi .nil m (t2HX Hr) with hHId
  set HR := cutHr .nil m inner ζ (t2HX Hr) with hHRd
  set HG := cutHg .nil m inner ζ (t2HX Hr) with hHGd
  -- the identity
  set cc : ℂ := (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * (Complex.I * (((ζ : ℤˣ) : ℤ) : ℂ)) *
    (Complex.I * (((slotSign ζ m.c : ℤˣ) : ℤ) : ℂ)) with hcc
  set R : Set ℝ := root2U LG m inner s s with hR
  set KI : PairE m P.d → ℝ → ℂ := fun e u => kernelProt P.L P.γ P.δ LGi HI mI (fun _ => s) u (fun _ => none)
    (k + latticePoint P.L e.1.1) (fun _ => 0) 0 with hKId
  set KR : PairE m P.d → ℝ → ℂ := fun e u => kernelProt P.L P.γ P.δ LGr HR mR (fun y => cupR m inner ζ s u y.1.1) 0
    (fun _ => none) (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 with hKRd
  set KG : PairE m P.d → ℝ → ℂ := fun e u => kernelProt P.L P.γ P.δ LGg HG mG (fun y => cupG m inner ζ s u y.1.1) 0
    (fun _ => none) (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0 with hKGd
  set KB : ℝ → ℂ := fun u => kernelProt P.L P.γ P.δ LGB HB mB (fun y => bClock (fun _ => s) u y.1.1) 0
    (trFix 1 s) k (fun _ => 0) 0 with hKBd
  have hid : kernelProt P.L P.γ P.δ LG Hr (gateM S ω F M Fu Mu) (fun _ => s) 0
      (MkSlotsO.rootPins (fun _ => True) s) k (fun _ => 0) 0 =
      cc * ∑' e : PairE m P.d, (fD3' Sb ω F (fun _ => false) M Fu Mu (D.aR Pp) (starA m P.L k e) *
          fD3' Sb ω F (fun _ => false) M Fu Mu (D.bR Pp) (starB m P.L k e)) * (cutEps m e : ℂ) *
        ∫ u in R, cutPh m ζ P.L P.γ P.δ k u e s * (KB u * (KI e u * (KR e u * KG e u))) := by
    have hid0 := Root2B.rt2_kernelProt_root2 D Pp P.L P.γ P.δ Hr hHs (gateM S ω F M Fu Mu) _ mB _ mI mR mG hMg hMZ CM
      (fun κ => (hmBB κ).trans (le_max_left _ _))
      (fun A B => (hMc A B).trans ((le_max_left _ _).trans (le_max_right _ _)))
      (fun κ => (hmIB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
      (fun κ => (hmRB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _)))))
      (fun κ => (hmGB κ).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _)))))
      0 s k
    exact hid0
  set J : Mom P.d → ℝ := fun x => (jbr x ^ (30 * P.d))⁻¹ with hJ
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hJ0 : ∀ y, 0 ≤ J y := fun y => (inv_pos.2 (hjpos y)).le
  -- the interior and the side couples, pointwise
  have hsI : s ∈ Icc (p : ℝ) (p + 1) := ⟨hps.le, hsp.le⟩
  have hRsub : ∀ u ∈ R, u ∈ Ioo (𝔏 : ℝ) (𝔏 + 1) ∧ u < s := fun u hu => ⟨⟨hu.1, hu.2.1⟩, hu.2.2.2.2⟩
  set bI : ℝ := P.L ^ (0 : ℝ) * rb P nI (LGi.incoherency (inner.treeLinks (LGi.garden.sig 0))) *
    leafSizeProduct LGi (tc2aBI m Br) * starCost (pullS (fun z => D.gd.ι₁ (Pp.hp.ιi z)) Sb)
      (fun z => cω (D.gd.ι₁ (Pp.hp.ιi z))) with hbI
  set bR : ℝ := P.L ^ (0 : ℝ) * rb P nR (LGr.incoherency Qr.links) * leafSizeProduct LGr (tc2aBR m inner ζ Br) *
    starCost (pullS (fun z => D.gd.ι₁ (Pp.hp.ιr z)) Sb) (fun z => cω (D.gd.ι₁ (Pp.hp.ιr z))) with hbR
  set bG : ℝ := P.L ^ (0 : ℝ) * rb P nG (LGg.incoherency Qg.links) * leafSizeProduct LGg (tc2aBG m inner ζ Br) *
    starCost (pullS (fun z => D.gd.ι₁ (Pp.hp.ιg z)) Sb) (fun z => cω (D.gd.ι₁ (Pp.hp.ιg z))) with hbG
  have hKIb : ∀ e, ∀ u ∈ R, ‖KI e u‖ₑ ≤ ENNReal.ofReal bI := fun e u hu => by
    obtain ⟨hu1, hus⟩ := hRsub u hu
    simp only [hKId]
    rw [cut_kernel_tree_m P.L P.γ P.δ LGi Pp.decI HI mI s u (k + latticePoint P.L e.1.1)]
    have hc := FiltCoh.continuous_treeKW_time P.L P.γ P.δ LGi HI Pp.decI mI BI hmIB (k + latticePoint P.L e.1.1)
      (summable_coset_piece hHI hL1 _)
    have hx : (![s, u] : Fin 2 → ℝ) ∈ timeBoxGt (p : ℝ) 𝔏 := by
      refine ⟨⟨by simpa using hsI, by simpa using (⟨hu1.1.le, hu1.2.le⟩ : u ∈ Icc (𝔏 : ℝ) (𝔏 + 1))⟩, ?_⟩
      simpa using hus
    have h1 := enorm_le_rn hθ0 (fun t ht => VineEstS3.timeBoxGt_subset_closure_interior h𝔏pR ht) hc hx
    refine h1.trans ?_
    rw [hbI, ← piece_conv hL0 hrb _ _ 0 nI _ _]
    exact tc_tree_mixed K hFC hp (hle_n nI (by omega)) hθc inner LGi hwI hnI Pp.decI hleI (q := p) (q' := 𝔏) h𝔏p
      le_rfl hrI hloneI hcI _ _ _ hGI _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hHI _
  have hKRb : ∀ e, ∀ u ∈ R, ‖KR e u‖ₑ ≤ ENNReal.ofReal bR * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) :=
    fun e u hu => by
    obtain ⟨hu1, -⟩ := hRsub u hu
    simp only [hKRd]
    rw [cut_kernel_couple_m P.L P.γ P.δ LGr Pp.decR HR mR (fun t => cupR m inner ζ s u t)]
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbR, ← piece_conv hL0 hrb _ _ 0 nR _ _]
    exact tc_couple_pt K hFC hp (hle_n nR (by omega)) hθc Qr LGr hwR hnR Pp.decR hleR (tc2a_qR_le D Pp hle 0)
      (tc2a_qR_le D Pp hle 1) (hrR 0) (hrR 1) hcR _ _ _ hGR _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hHR _
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGr HR Pp.decR.1.1 mR BR hmRB _
        (summable_coset_piece hHR hL1 _)) (x := fun t => cupR m inner ζ s u t)
      (tc2a_cupR_mem hsI ⟨hu1.1.le, hu1.2.le⟩)
  have hKGb : ∀ e, ∀ u ∈ R, ‖KG e u‖ₑ ≤ ENNReal.ofReal bG * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2)) :=
    fun e u hu => by
    obtain ⟨hu1, -⟩ := hRsub u hu
    simp only [hKGd]
    rw [cut_kernel_couple_m P.L P.γ P.δ LGg Pp.decG HG mG (fun t => cupG m inner ζ s u t)]
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbG, ← piece_conv hL0 hrb _ _ 0 nG _ _]
    exact tc_couple_pt K hFC hp (hle_n nG (by omega)) hθc Qg LGg hwG hnG Pp.decG hleG (tc2a_qG_le D Pp hle 0)
      (tc2a_qG_le D Pp hle 1) (hrG 0) (hrG 1) hcG _ _ _ hGG _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hHG _
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGg HG Pp.decG.1.1 mG BG hmGB _
        (summable_coset_piece hHG hL1 _)) (x := fun t => cupG m inner ζ s u t)
      (tc2a_cupG_mem hsI ⟨hu1.1.le, hu1.2.le⟩)
  -- continuity in the port time
  have hcI : ∀ e : PairE m P.d, Continuous (KI e) := fun e => by
    have hc := FiltCoh.continuous_treeKW_time P.L P.γ P.δ LGi HI Pp.decI mI BI hmIB (k + latticePoint P.L e.1.1)
      (summable_coset_piece hHI hL1 _)
    have := hc.comp (show Continuous fun u : ℝ => (![s, u] : Fin 2 → ℝ) by fun_prop)
    refine this.congr fun u => ?_
    simp only [Function.comp_apply, hKId]
    rw [cut_kernel_tree_m P.L P.γ P.δ LGi Pp.decI HI mI s u (k + latticePoint P.L e.1.1)]
    rfl
  have hcR' : ∀ e : PairE m P.d, Continuous (KR e) := fun e => by
    have hc := FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGr HR Pp.decR.1.1 mR BR hmRB
      (k + latticePoint P.L e.1.2.1) (summable_coset_piece hHR hL1 _)
    have := hc.comp (tc2a_cupR_cont m inner ζ s)
    refine this.congr fun u => ?_
    simp only [Function.comp_apply, hKRd]
    rw [cut_kernel_couple_m P.L P.γ P.δ LGr Pp.decR HR mR (fun t => cupR m inner ζ s u t)]
    rfl
  have hcG' : ∀ e : PairE m P.d, Continuous (KG e) := fun e => by
    have hc := FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGg HG Pp.decG.1.1 mG BG hmGB
      (k + latticePoint P.L e.1.2.2) (summable_coset_piece hHG hL1 _)
    have := hc.comp (tc2a_cupG_cont m inner ζ s)
    refine this.congr fun u => ?_
    simp only [Function.comp_apply, hKGd]
    rw [cut_kernel_couple_m P.L P.γ P.δ LGg Pp.decG HG mG (fun t => cupG m inner ζ s u t)]
    rfl
  -- the weights
  set Φ : PairE m P.d → ℝ → ℂ := fun e u => cutPh m ζ P.L P.γ P.δ k u e s * (KI e u * (KR e u * KG e u)) with hΦ
  have hΦc : ∀ e, Continuous (Φ e) := fun e => by
    have hph : Continuous fun u : ℝ => cutPh m ζ P.L P.γ P.δ k u e s := by unfold cutPh; fun_prop
    exact hph.mul ((hcI e).mul ((hcR' e).mul (hcG' e)))
  set Me : PairE m P.d → ℝ := fun e => bI * bR * bG * (J (k + latticePoint P.L e.1.2.1) *
    J (k + latticePoint P.L e.1.2.2)) with hMe
  have hb0 : ∀ {w : ℕ} (LGx : LayeredGarden w) (Bx : (Fin w × TTree.Path) → NNReal),
      0 ≤ leafSizeProduct LGx Bx := fun LGx Bx => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hbI0 : 0 ≤ bI := by
    rw [hbI, Real.rpow_zero, one_mul]; exact mul_nonneg (mul_nonneg (hrb _ _) (hb0 _ _)) (starCost_nonneg' _ _)
  have hbR0 : 0 ≤ bR := by
    rw [hbR, Real.rpow_zero, one_mul]; exact mul_nonneg (mul_nonneg (hrb _ _) (hb0 _ _)) (starCost_nonneg' _ _)
  have hbG0 : 0 ≤ bG := by
    rw [hbG, Real.rpow_zero, one_mul]; exact mul_nonneg (mul_nonneg (hrb _ _) (hb0 _ _)) (starCost_nonneg' _ _)
  have hMe0 : ∀ e, 0 ≤ Me e := fun e => by
    have := hJ0 (k + latticePoint P.L e.1.2.1); have := hJ0 (k + latticePoint P.L e.1.2.2)
    simp only [hMe]; positivity
  have hΦb : ∀ e, ∀ u ∈ R, ‖Φ e u‖ ≤ Me e := fun e u hu => by
    have h1 : ‖Φ e u‖ₑ ≤ ENNReal.ofReal (Me e) := by
      simp only [hΦ]
      rw [enorm_mul, enorm_mul, enorm_mul, ← ofReal_norm, norm_cutPh, ENNReal.ofReal_one, one_mul]
      calc _ ≤ ENNReal.ofReal bI * ((ENNReal.ofReal bR * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1))) *
            (ENNReal.ofReal bG * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2)))) :=
            mul_le_mul' (hKIb e u hu) (mul_le_mul' (hKRb e u hu) (hKGb e u hu))
        _ = _ := by
            simp only [hMe]
            rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hbI0 hbR0) hbG0), ENNReal.ofReal_mul (mul_nonneg hbI0 hbR0),
              ENNReal.ofReal_mul hbI0, ENNReal.ofReal_mul (hJ0 _)]
            ring
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (hMe0 e)).1 h1
  set ψ : PairE m P.d → ℝ → ℂ := fun e => R.indicator (Φ e) with hψ
  have hRm : MeasurableSet R := measurableSet_root2U LG m inner s s
  have hψm : ∀ e, Measurable (ψ e) := fun e => (hΦc e).measurable.indicator hRm
  have hψb : ∀ e u, ‖ψ e u‖ ≤ Me e := fun e u => by
    by_cases hu : u ∈ R
    · simp only [hψ, Set.indicator_of_mem hu]; exact hΦb e u hu
    · simp only [hψ, Set.indicator_of_notMem hu, norm_zero]; exact hMe0 e
  -- the rest couple: one root pinned (`RtOne`), in `L¹(du)`
  have hjbB : ([] : TTree.Path) ∈ (LGB.garden.tree 1).branching := by
    rw [← D.gd.treej 1 (by decide)]; exact hjb1
  have hB1 : layerAt LGB ((1 : Fin 2), []) = p := by
    have hm : ([] : TTree.Path) ∈ (LGB.garden.tree 1).nodes := TTree.branching_subset_nodes _ hjbB
    rw [layerAt_node LGB (⟨((1 : Fin 2), []), hm⟩ : GNode LGB.garden.tree)]
    exact (D.layB _).trans (by simpa [botAddr] using hj0 1)
  have hrB : layerAt LGB (t1sw 1, []) ≤ 𝔏 := by
    have hm : ([] : TTree.Path) ∈ (LGB.garden.tree 0).nodes := TTree.nil_mem_nodes _
    rw [show t1sw (1 : Fin 2) = 0 from rfl, layerAt_node LGB (⟨((0 : Fin 2), []), hm⟩ : GNode LGB.garden.tree)]
    exact hrB0
  have hambB : MkSlotsO.CplAmbient p (rtWin p 𝔏 1 0) (rtWin p 𝔏 1 1) (SourceApp.closeCouple rest Xm Qlp) LGB := by
    obtain ⟨w', H, a, b, hcan, hE, hsa, hsb, -, hpb, hlay⟩ := hA
    obtain ⟨hX, hY, hQ⟩ := hE.type2
    obtain ⟨-, -, -, hRr⟩ := hX.parts
    rw [slotSign_lone] at hRr
    have hlp := tc2a_lone_path D Pp
    have hQ' : Embeds H.garden Qlp (addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath)
        (addrExt b Xm.lonePath) := by
      rw [addrExt_append]
      simpa [RegChain.lonePath, List.append_assoc] using hQ
    have hind : Indep (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) b := by
      have := hE.indep.ext ([m.c] ++ inner.lonePath ++ [m.lone]) []
      rwa [show addrExt b ([] : TTree.Path) = b by simp [addrExt]] at this
    have hEB := tc2a_embeds_close hRr hY hQ' hind
    have hl : ∀ z : GNode LGB.garden.tree, LGB.layer z = layerAt H
        (addrExt (if z.1.1 = 0 then addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]) else b) z.1.2) := by
      intro z
      have hm := (D.gd.bot_iff z.1).1.2 z.2
      rw [D.layB z, layerAt_of_mem LG hm, hlay ⟨botAddr (cpair m Qr Qg inner).lonePath z.1, hm⟩]
      rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
      · simp [botAddr, hz, addrExt, hlp, List.append_assoc]
      · simp [botAddr, hz, addrExt]
    have hlb := (tc2a_amb_layers D Pp hlay).2
    refine ⟨w', H, _, _, hcan, hEB, ?_, hsb, ?_, ?_, hl⟩
    · rw [show [m.c] ++ inner.lonePath ++ [m.lone] = (RegChain.pair m Qr Qg inner .nil).lonePath by
        simp [RegChain.lonePath], nodeSign_spine, hsa]
    · have e : addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]) = addrExt (addrExt a (bPath m inner)) [m.lone] := by
        rw [addrExt_append]; simp [bPath]
      rw [show rtWin p 𝔏 1 0 = 𝔏 from rfl, e, parAt_child H p m.lone (by rw [← e]; exact hEB.nodeA), hlb]
    · rw [show rtWin p 𝔏 1 1 = p from rfl]; exact hpb
  have hone := h1 K hFC hC11 hθc hp (hle_n nB (by omega)) _ LGB hwB hnB hdB hleB 1 h𝔏p hambB hB1 hjbB hrB hps hsp
    HB (tc2aBB m Qr Qg inner Br) hHB SB ωB cB hpB FB MB' (pull_scale _ hM) FuB MuB (pull_scale _ hMu) k
  have hKBf : ∀ u, KB u = kernelProt P.L P.γ P.δ LGB HB (gateM SB ωB FB MB' FuB MuB)
      (fun b => if b.1.1 = 1 then s else (fun _ : Fin 1 => u) 0) 0 (trFix 1 s) k (fun _ => 0) 0 := fun u => by
    simp only [hKBd]
    congr 1
    funext y
    unfold bClock
    rcases Fin.exists_fin_two.mp ⟨y.1.1, rfl⟩ with hy | hy <;> simp [hy]
  have hRsubI : R ⊆ Icc (𝔏 : ℝ) (𝔏 + 1) := fun u hu => ⟨hu.1.le, hu.2.1.le⟩
  have hvolR : volume R ≤ 1 := by
    have hsub : R ⊆ Ioo (𝔏 : ℝ) (𝔏 + 1) := fun u hu => ⟨hu.1, hu.2.1⟩
    refine (measure_mono hsub).trans ?_
    rw [Real.volume_Ioo, show (𝔏 : ℝ) + 1 - 𝔏 = 1 by ring, ENNReal.ofReal_one]
  have hl1 := rt2_lint_le_rn hθ0 (𝔏 : ℝ) (fun y => kernelProt P.L P.γ P.δ LGB HB (gateM SB ωB FB MB' FuB MuB)
      (fun b => if b.1.1 = 1 then s else y 0) 0 (trFix 1 s) k (fun _ => 0) 0) hRsubI hRm hvolR
  set Xone : ℝ≥0∞ := ENNReal.ofReal (Ct₁ * (P.L ^ (4 * (0 : ℝ)) * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
      (P.C₁ ^ 3 * rb P (nB - 1) (LGB.incoherency (SourceApp.closeCouple rest Xm Qlp).links)) *
        leafSizeProduct LGB (tc2aBB m Qr Qg inner Br) * starCost SB cB)))) * tcWt P.L k with hXone
  have hKBint : ∫⁻ u in R, ‖KB u‖ₑ ≤ Xone := by
    simp_rw [hKBf]
    exact hl1.trans hone
  -- the modulus
  set c2 : ℝ := coupling P.d P.L P.γ P.δ ^ 2 with hc2
  have hc20 : 0 ≤ c2 := sq_nonneg _
  have hccn : ‖cc‖ = c2 := by
    rw [hcc]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.norm_I, one_mul]
    simp only [tc2a_abs_units, tc2a_norm_units, Complex.norm_intCast, mul_one, hc2]
  have haeb : ∀ e : PairE m P.d, ‖(fD3' Sb ω F (fun _ => false) M Fu Mu (D.aR Pp) (starA m P.L k e) *
      fD3' Sb ω F (fun _ => false) M Fu Mu (D.bR Pp) (starB m P.L k e)) * (cutEps m e : ℂ)‖ₑ ≤
        ENNReal.ofReal Ca := fun e => by
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul (hMc _ _) (abs_cutEps_le m e) (abs_nonneg _) hCa0).trans (by rw [mul_one])
  have hint : ∀ e : PairE m P.d, ‖∫ u in R, cutPh m ζ P.L P.γ P.δ k u e s * (KB u * (KI e u * (KR e u * KG e u)))‖ₑ ≤
      ENNReal.ofReal (Me e) * Xone := fun e => by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ u in R, ‖cutPh m ζ P.L P.γ P.δ k u e s * (KB u * (KI e u * (KR e u * KG e u)))‖ₑ
        ≤ ∫⁻ u in R, ENNReal.ofReal (Me e) * ‖KB u‖ₑ := by
          refine setLIntegral_mono' hRm fun u hu => ?_
          have h1 : ‖cutPh m ζ P.L P.γ P.δ k u e s * (KB u * (KI e u * (KR e u * KG e u)))‖ₑ =
              ‖Φ e u‖ₑ * ‖KB u‖ₑ := by
            simp only [hΦ, enorm_mul]; ring
          rw [h1, ← ofReal_norm]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hΦb e u hu)) le_rfl
      _ = ENNReal.ofReal (Me e) * ∫⁻ u in R, ‖KB u‖ₑ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul' le_rfl hKBint
  have hS := tsum_decay_le hd1 hL1 k
  have hMsum : ∑' e, ENNReal.ofReal (Me e) ≤
      ENNReal.ofReal (bI * bR * bG) * ENNReal.ofReal ((latC P.d * P.L ^ P.d) ^ 2) := by
    have he : ∀ e : PairE m P.d, ENNReal.ofReal (Me e) = ENNReal.ofReal (bI * bR * bG) *
        (tcJ (k + latticePoint P.L e.1.2.1) * tcJ (k + latticePoint P.L e.1.2.2)) := fun e => by
      simp only [hMe, tcJ, hJ]
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hbI0 hbR0) hbG0),
        ENNReal.ofReal_mul (inv_pos.2 (hjpos _)).le]
    simp_rw [he]
    rw [ENNReal.tsum_mul_left]
    refine mul_le_mul' le_rfl ((tc_tsum_pairE_le2 m (fun y => tcJ (k + latticePoint P.L y))
      (fun y => tcJ (k + latticePoint P.L y))).trans ?_)
    have hl0 : 0 ≤ latC P.d * P.L ^ P.d := mul_nonneg (latC_nonneg _) (pow_nonneg hL0 _)
    rw [sq, ENNReal.ofReal_mul hl0]
    exact mul_le_mul' hS hS
  rw [hid, enorm_mul, ← ofReal_norm cc, hccn]
  have hmod : ENNReal.ofReal c2 * ‖∑' e : PairE m P.d, (fD3' Sb ω F (fun _ => false) M Fu Mu (D.aR Pp) (starA m P.L k e) *
          fD3' Sb ω F (fun _ => false) M Fu Mu (D.bR Pp) (starB m P.L k e)) * (cutEps m e : ℂ) *
        ∫ u in R, cutPh m ζ P.L P.γ P.δ k u e s * (KB u * (KI e u * (KR e u * KG e u)))‖ₑ ≤
      ENNReal.ofReal (c2 * Ca) * (ENNReal.ofReal (bI * bR * bG) * ENNReal.ofReal ((latC P.d * P.L ^ P.d) ^ 2)) *
        Xone := by
    refine (mul_le_mul' le_rfl (enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun e =>
      (enorm_mul _ _).le.trans (mul_le_mul' (haeb e) (hint e))))).trans ?_
    rw [show (fun e : PairE m P.d => ENNReal.ofReal Ca * (ENNReal.ofReal (Me e) * Xone)) =
        fun e => (ENNReal.ofReal Ca * Xone) * ENNReal.ofReal (Me e) from funext fun e => by ring,
      ENNReal.tsum_mul_left, ENNReal.ofReal_mul hc20]
    calc ENNReal.ofReal c2 * (ENNReal.ofReal Ca * Xone * ∑' e, ENNReal.ofReal (Me e))
        ≤ ENNReal.ofReal c2 * (ENNReal.ofReal Ca * Xone *
          (ENNReal.ofReal (bI * bR * bG) * ENNReal.ofReal ((latC P.d * P.L ^ P.d) ^ 2))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hMsum)
      _ = _ := by ring
  refine hmod.trans ?_
  -- the algebra
  have hnB1 : 1 ≤ nB := tc_size_pos hwB hdB hjbB hnB
  have hg := tc2a_incoh D Pp hdec hdB hsZ
  set g := LG.incoherency (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).links with hgdef
  set gB := LGB.incoherency (SourceApp.closeCouple rest Xm Qlp).links with hgB
  set g' := gB + LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) + LGr.incoherency Qr.links +
    LGg.incoherency Qg.links with hg'
  have hn2 : nB - 1 + nI + nR + nG = n - 2 := by omega
  have hleaf := tc2a_leafSize D Pp Br
  have hcost := tc2a_cost D Pp S cω
  rw [← hSb, ← hSB, ← hcBd] at hcost
  try rw [← hζ] at hleaf
  have h4 := rb_four (P := P) (by linarith : (0 : ℝ) < P.L) (n₁ := nB - 1) (n₂ := nI) (n₃ := nR) (n₄ := nG)
    (g₁ := gB) (g₂ := LGi.incoherency (inner.treeLinks (LGi.garden.sig 0))) (g₃ := LGr.incoherency Qr.links)
    (g₄ := LGg.incoherency Qg.links)
  have h4' : rb P (nB - 1) gB * rb P nI (LGi.incoherency (inner.treeLinks (LGi.garden.sig 0))) *
      rb P nR (LGr.incoherency Qr.links) * rb P nG (LGg.incoherency Qg.links) = P.C₁ ^ 3 * rb P (n - 2) g' := by
    rw [h4, hn2]; rfl
  have hrbL : rb P (n - 2) g' ≤ P.L * rb P (n - 2) g := by
    by_cases hc : layerAt LG ((0 : Fin 2), []) = layerAt LG ((0 : Fin 2), bPath m inner)
    · rw [if_pos hc, add_zero] at hg
      have hgg : g' = g := by rw [hg]
      rw [hgg]
      exact le_mul_of_one_le_left (hrb _ _) hL1
    · rw [if_neg hc] at hg
      have hgg : g' = g - 1 := by omega
      have hpred := rb_pred_le hL1 hC1 K.hδ K.hη0 (n - 2) (show 1 ≤ g by omega)
      rw [Real.rpow_one] at hpred
      rw [hgg]
      exact hpred
  have hleafB0 : 0 ≤ leafSizeProduct LGB (tc2aBB m Qr Qg inner Br) := hb0 _ _
  have hCSB0 : 0 ≤ starCost SB cB := starCost_nonneg' _ _
  have hrbB0 := hrb (nB - 1) gB
  have hXr0 : 0 ≤ Ct₁ * (P.L ^ (4 * (0 : ℝ)) * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
      (P.C₁ ^ 3 * rb P (nB - 1) gB) * leafSizeProduct LGB (tc2aBB m Qr Qg inner Br) * starCost SB cB))) := by
    have := Real.rpow_nonneg hL0 (4 * (0 : ℝ)); positivity
  have hl20 : 0 ≤ (latC P.d * P.L ^ P.d) ^ 2 := sq_nonneg _
  have e1 : ENNReal.ofReal (c2 * Ca) * (ENNReal.ofReal (bI * bR * bG) * ENNReal.ofReal ((latC P.d * P.L ^ P.d) ^ 2)) =
      ENNReal.ofReal (c2 * Ca * (bI * bR * bG * (latC P.d * P.L ^ P.d) ^ 2)) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hbI0 hbR0) hbG0), ← ENNReal.ofReal_mul (mul_nonneg hc20 hCa0)]
  rw [e1, hXone, ← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hc20 hCa0)
    (mul_nonneg (mul_nonneg (mul_nonneg hbI0 hbR0) hbG0) hl20))]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hY : 0 ≤ Ct₁ * P.L * c2 ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.C₁ ^ 6 * leafSizeProduct LG Br *
      starCost S cω := by
    have := starCost_nonneg' S cω
    have := hb0 LG Br
    positivity
  calc _ = (Ct₁ * P.L * c2 ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.C₁ ^ 3 * leafSizeProduct LG Br * starCost S cω) *
        (rb P (nB - 1) gB * rb P nI (LGi.incoherency (inner.treeLinks (LGi.garden.sig 0))) *
          rb P nR (LGr.incoherency Qr.links) * rb P nG (LGg.incoherency Qg.links)) := by
        rw [hbI, hbR, hbG, hleaf, hcost, hCa, hc2]
        simp only [mul_zero, Real.rpow_zero]
        ring
    _ = (Ct₁ * P.L * c2 ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.C₁ ^ 3 * leafSizeProduct LG Br * starCost S cω) *
        (P.C₁ ^ 3 * rb P (n - 2) g') := by rw [h4']
    _ = (Ct₁ * P.L * c2 ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.C₁ ^ 6 * leafSizeProduct LG Br * starCost S cω) *
        rb P (n - 2) g' := by ring
    _ ≤ (Ct₁ * P.L * c2 ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.C₁ ^ 6 * leafSizeProduct LG Br * starCost S cω) *
        (P.L * rb P (n - 2) g) := mul_le_mul_of_nonneg_left hrbL hY
    _ = _ := by rw [hc2]; ring

end WaveTurbulence.Flower.ProtRT
