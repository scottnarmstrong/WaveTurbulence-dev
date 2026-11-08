/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.RT1ACoh
public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2A

/-! # RT-GATE (ii), shape (a+): the one-pinned root trace with partner window `q'` and piece loss `c'`

D3-HELPER's `tc2a_core` (ProtPin/TChild2A.lean L40–457, sha256 0f3b321b…; the coherence lemmas from
ProtPin/TChild2ACoh.lean, sha256 f4a87ee0…, in RT1ACoh.lean) generalized: the partner clock window is `q' ≤ p` (the rest
couple on `timeBox 𝔏_b q'`, coherent pieces from the windowed ambient `CplAmbient p p q'`), and every piece carries the
loss `L^{c'}` of `PieceLoss P θ c'` (four pieces: `L^{4c'}`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **The one-pinned root trace of a type-2 couple with a nonempty `+` chain** (o104 Prop 7.4 (a), `ε = +`), partner
window `q'`, piece loss `c'`. -/
theorem rt1a_core {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b)
      (_hFC : TcFC P) {c' : ℝ} (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest Xm : RegChain} {Qlp : RegCpl}
      {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2} (D : Root2Data LG m Qr Qg inner LGZ LGB)
      {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} (Pp : PairOnly LGZ m Qr Qg inner LGi LGr LGg)
      (_hdB : (SourceApp.closeCouple rest Xm Qlp).Decodes LGB.garden) (_hsZ : LGZ.garden.sig 0 = 1)
      (_hwf : (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).wf = true)
      (_hsz : (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).size = 2 * n)
      (_hdec : (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).Decodes LG.garden) (_hle : ∀ a, LG.layer a ≤ p)
      {q' : ℕ} (_hq' : q' ≤ p) (_hA : MkSlotsO.CplAmbient p p q' (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp) LG)
      (_hj : layerAt LG ((0 : Fin 2), []) = p) (_hr : layerAt LG ((1 : Fin 2), []) ≤ q') {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1)
      (Hr : LeafProfiles 2 P.d) (Br : (Fin 2 × TTree.Path) → NNReal) (_hHr : LeafwiseControlled LG Hr Br)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (k : Mom P.d),
      rn θ (win (q' : ℝ)) (fun y => kernelProt P.L P.γ P.δ LG Hr
          (gateM S ω F M Fu Mu) (fun b => if b.1.1 = 0 then s else y 0) 0 (trFix 0 s) k (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
          (P.C₁ ^ 3 * rb P (n - 1) (LG.incoherency (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).links)) *
            leafSizeProduct LG Br * starCost S cω))) * tcWt P.L k := by
  obtain ⟨Cs, hCs, hsumivl⟩ := tc2a_sum_ivl hθ0
  refine ⟨Cs, hCs, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hFC c' hθc p hp n hn LG m Qr Qg inner rest Xm Qlp LGZ LGB D LGi LGr LGg Pp hdB hsZ hwf
    hsz hdec hle q' hq' hA hj hr s hps hsp Hr Br hHr S ω cω hpres F M hM Fu Mu hMu k
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hd1 : 1 ≤ P.d := by have := K.hd; omega
  have hrb : ∀ j g, 0 ≤ rb P j g := fun j g => rb_nonneg hC1 K.hδ hL0 j g
  have hLc : 0 ≤ P.L ^ c' := Real.rpow_nonneg hL0 _
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
  have hrB1 : LGB.layer (GNode.root LGB.garden.tree 1) ≤ q' := rt1a_rootB1_le D Pp hr
  have hrI := tc2a_rootI_le D Pp hle hj
  have hloneI := tc2a_loneI D Pp
  have hrR := tc2a_rootR_le D Pp hle hj
  have hrG := tc2a_rootG_le D Pp hle hj
  -- coherence
  have hcB : LGB.incoherency (SourceApp.closeCouple rest Xm Qlp).links = 0 →
      IsCoherentCoupleAt p 𝔏 q' (SourceApp.closeCouple rest Xm Qlp) LGB := fun h0 => rt1a_cohB D Pp hA hwB hdB h0
  have hcI : LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) = 0 → IsCoherentTreeAt p p 𝔏 inner LGi :=
    fun h0 => rt1a_cohI D Pp hsZ hA hj hwI h0
  have hcR : LGr.incoherency Qr.links = 0 → IsCoherentCoupleAt p (tc2aQR m inner (LGZ.garden.sig 0) p 𝔏 0)
      (tc2aQR m inner (LGZ.garden.sig 0) p 𝔏 1) Qr LGr := fun h0 => by
    have := rt1a_cohR D Pp hsZ hA hwR h0; rwa [hj] at this
  have hcG : LGg.incoherency Qg.links = 0 → IsCoherentCoupleAt p (tc2aQG m inner (LGZ.garden.sig 0) p 𝔏 0)
      (tc2aQG m inner (LGZ.garden.sig 0) p 𝔏 1) Qg LGg := fun h0 => by
    have := rt1a_cohG D Pp hsZ hA hwG h0; rwa [hj] at this
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
  have hid : ∀ y : Fin 1 → ℝ, kernelProt P.L P.γ P.δ LG Hr (gateM S ω F M Fu Mu)
      (fun b => if b.1.1 = 0 then s else y 0) 0 (trFix 0 s) k (fun _ => 0) 0 =
      cc * ∑' e : PairE m P.d, (fD3' Sb ω F (fun _ => false) M Fu Mu (D.aR Pp) (starA m P.L k e) *
          fD3' Sb ω F (fun _ => false) M Fu Mu (D.bR Pp) (starB m P.L k e)) * (cutEps m e : ℂ) *
        ∫ u in R, cutPh m ζ P.L P.γ P.δ k u e s *
          (kernelProt P.L P.γ P.δ LGB HB mB
              (fun y' => bClock (fun t : Fin 2 => if t = 0 then s else y 0) u y'.1.1) 0
              (fun _ => none) k (fun _ => 0) 0 * (KI e u * (KR e u * KG e u))) := by
    intro y
    set U : Fin 2 → ℝ := fun t => if t = 0 then s else y 0 with hU
    have hU0 : U 0 = s := by simp [hU]
    have hid0 := D.kernelProt_root2 Pp P.L P.γ P.δ Hr hHs (gateM S ω F M Fu Mu) _ mB _ mI mR mG hMg hMZ CM
      (fun κ => (hmBB κ).trans (le_max_left _ _))
      (fun A B => (hMc A B).trans ((le_max_left _ _).trans (le_max_right _ _)))
      (fun κ => (hmIB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
      (fun κ => (hmRB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _)))))
      (fun κ => (hmGB κ).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _)))))
      U 0 s hU0.symm.le k
    rw [hU0] at hid0
    exact hid0
  -- the rest couple as a function of (partner clock, port)
  set f : (Fin 2 → ℝ) → ℂ := fun x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGB HB
    (fun b => if b.1.1 = 0 then x 0 else x 1) 0 k (fun _ => 0) 0 mB with hf
  have hfc : Continuous f := FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGB HB D.plainB mB BB hmBB k
    (summable_coset_piece hHB hL1 k)
  set Gf : (Fin 2 → ℝ) → ℂ := fun t => f ![t 1, t 0] with hGf
  have hGc : Continuous Gf := hfc.comp (show Continuous fun x : Fin 2 → ℝ => ![x 1, x 0] by fun_prop)
  have hKB : ∀ (y0 u : ℝ), kernelProt P.L P.γ P.δ LGB HB mB
      (fun y' => bClock (fun t : Fin 2 => if t = 0 then s else y0) u y'.1.1) 0 (fun _ => none) k (fun _ => 0) 0 =
      Gf ![y0, u] := by
    intro y0 u
    have e : (fun y' : GBranch LGB.garden.tree => bClock (fun t : Fin 2 => if t = 0 then s else y0) u y'.1.1) =
        fun y' => (![u, y0] : Fin 2 → ℝ) y'.1.1 := funext fun y' => tc2a_bClock_eq s y0 u y'.1.1
    rw [e, cut_kernel_couple_m P.L P.γ P.δ LGB hdB HB mB ![u, y0] k]
    rfl
  set J : Mom P.d → ℝ := fun x => (jbr x ^ (30 * P.d))⁻¹ with hJ
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hJ0 : ∀ y, 0 ≤ J y := fun y => (inv_pos.2 (hjpos y)).le
  set gB := LGB.incoherency (SourceApp.closeCouple rest Xm Qlp).links with hgB
  set bB : ℝ := P.L ^ c' * rb P nB gB * leafSizeProduct LGB (tc2aBB m Qr Qg inner Br) * starCost SB cB with hbB
  have hfb : rn θ (timeBox (𝔏 : ℝ) q') f ≤ ENNReal.ofReal bB * ENNReal.ofReal (J k) := by
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbB, ← piece_conv hL0 hrb _ _ c' nB _ _]
    exact tc_couple_mixed K hFC hp (hle_n nB (by omega)) hθc _ LGB hwB hnB hdB hleB (q₀ := 𝔏) (q₁ := q') h𝔏p hq'
      hrB0 hrB1 hcB SB ωB cB hpB FB MB' (pull_scale _ hM) FuB MuB (pull_scale _ hMu) HB _ hHB k
  have hGb : rn θ (timeBox (q' : ℝ) 𝔏) Gf ≤ ENNReal.ofReal bB * ENNReal.ofReal (J k) :=
    (le_of_eq (tc2a_swap_box θ (𝔏 : ℝ) q' f)).trans hfb
  -- the interior and the side couples, pointwise
  have hsI : s ∈ Icc (p : ℝ) (p + 1) := ⟨hps.le, hsp.le⟩
  have hRsub : ∀ u ∈ R, u ∈ Ioo (𝔏 : ℝ) (𝔏 + 1) ∧ u < s := fun u hu => ⟨⟨hu.1, hu.2.1⟩, hu.2.2.2.2⟩
  set bI : ℝ := P.L ^ c' * rb P nI (LGi.incoherency (inner.treeLinks (LGi.garden.sig 0))) *
    leafSizeProduct LGi (tc2aBI m Br) * starCost (pullS (fun z => D.gd.ι₁ (Pp.hp.ιi z)) Sb)
      (fun z => cω (D.gd.ι₁ (Pp.hp.ιi z))) with hbI
  set bR : ℝ := P.L ^ c' * rb P nR (LGr.incoherency Qr.links) * leafSizeProduct LGr (tc2aBR m inner ζ Br) *
    starCost (pullS (fun z => D.gd.ι₁ (Pp.hp.ιr z)) Sb) (fun z => cω (D.gd.ι₁ (Pp.hp.ιr z))) with hbR
  set bG : ℝ := P.L ^ c' * rb P nG (LGg.incoherency Qg.links) * leafSizeProduct LGg (tc2aBG m inner ζ Br) *
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
    rw [hbI, ← piece_conv hL0 hrb _ _ c' nI _ _]
    exact tc_tree_mixed K hFC hp (hle_n nI (by omega)) hθc inner LGi hwI hnI Pp.decI hleI (q := p) (q' := 𝔏) h𝔏p
      le_rfl hrI hloneI hcI _ _ _ hGI _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hHI _
  have hKRb : ∀ e, ∀ u ∈ R, ‖KR e u‖ₑ ≤ ENNReal.ofReal bR * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) :=
    fun e u hu => by
    obtain ⟨hu1, -⟩ := hRsub u hu
    simp only [hKRd]
    rw [cut_kernel_couple_m P.L P.γ P.δ LGr Pp.decR HR mR (fun t => cupR m inner ζ s u t)]
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbR, ← piece_conv hL0 hrb _ _ c' nR _ _]
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
    rw [hbG, ← piece_conv hL0 hrb _ _ c' nG _ _]
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
  have hbI0 : 0 ≤ bI := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hb0 _ _)) (starCost_nonneg' _ _)
  have hbR0 : 0 ≤ bR := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hb0 _ _)) (starCost_nonneg' _ _)
  have hbG0 : 0 ≤ bG := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hb0 _ _)) (starCost_nonneg' _ _)
  have hbB0 : 0 ≤ bB := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hb0 _ _)) (starCost_nonneg' _ _)
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
  -- the terms
  set ae : PairE m P.d → ℂ := fun e => cc * ((fD3' Sb ω F (fun _ => false) M Fu Mu (D.aR Pp) (starA m P.L k e) *
    fD3' Sb ω F (fun _ => false) M Fu Mu (D.bR Pp) (starB m P.L k e)) * (cutEps m e : ℂ)) with hae
  set c2 : ℝ := coupling P.d P.L P.γ P.δ ^ 2 with hc2
  have hc20 : 0 ≤ c2 := sq_nonneg _
  have hccn : ‖cc‖ = c2 := by
    rw [hcc]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.norm_I, one_mul]
    simp only [tc2a_abs_units, tc2a_norm_units, Complex.norm_intCast, mul_one, hc2]
  have haeb : ∀ e, ‖ae e‖ₑ ≤ ENNReal.ofReal (c2 * Ca) := fun e => by
    have hn : ‖ae e‖ = c2 * (‖fD3' Sb ω F (fun _ => false) M Fu Mu (D.aR Pp) (starA m P.L k e) *
        fD3' Sb ω F (fun _ => false) M Fu Mu (D.bR Pp) (starB m P.L k e)‖ * |cutEps m e|) := by
      show ‖cc * ((fD3' Sb ω F (fun _ => false) M Fu Mu (D.aR Pp) (starA m P.L k e) *
        fD3' Sb ω F (fun _ => false) M Fu Mu (D.bR Pp) (starB m P.L k e)) * (cutEps m e : ℂ))‖ = _
      rw [norm_mul, hccn, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [← ofReal_norm, hn]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ((mul_le_mul (hMc _ _) (abs_cutEps_le m e)
      (abs_nonneg _) hCa0).trans (by rw [mul_one])) hc20)
  set tm : PairE m P.d → (Fin 1 → ℝ) → ℂ := fun e y => ae e * ∫ u in (𝔏 : ℝ)..(𝔏 + 1), ψ e u * Gf ![y 0, u]
    with htm
  have hRIoc : R ⊆ Ioc (𝔏 : ℝ) (𝔏 + 1) := fun u hu => ⟨hu.1, hu.2.1.le⟩
  have hint : ∀ e (y0 : ℝ), (∫ u in R, cutPh m ζ P.L P.γ P.δ k u e s *
      (kernelProt P.L P.γ P.δ LGB HB mB (fun y' => bClock (fun t : Fin 2 => if t = 0 then s else y0) u y'.1.1) 0
          (fun _ => none) k (fun _ => 0) 0 * (KI e u * (KR e u * KG e u)))) =
      ∫ u in (𝔏 : ℝ)..(𝔏 + 1), ψ e u * Gf ![y0, u] := by
    intro e y0
    rw [intervalIntegral.integral_of_le (by linarith)]
    have e1 : (fun u => ψ e u * Gf ![y0, u]) = R.indicator (fun u => Φ e u * Gf ![y0, u]) := by
      funext u
      by_cases hu : u ∈ R
      · rw [Set.indicator_of_mem hu, show ψ e u = Φ e u from Set.indicator_of_mem hu (Φ e)]
      · rw [Set.indicator_of_notMem hu, show ψ e u = 0 from Set.indicator_of_notMem hu (Φ e), zero_mul]
    rw [e1, setIntegral_indicator hRm, Set.inter_eq_right.mpr hRIoc]
    refine setIntegral_congr_fun hRm fun u _ => ?_
    simp only [hΦ]
    rw [hKB y0 u]
    ring
  have hwin : ∀ y ∈ win (q' : ℝ), kernelProt P.L P.γ P.δ LG Hr (gateM S ω F M Fu Mu)
      (fun b => if b.1.1 = 0 then s else y 0) 0 (trFix 0 s) k (fun _ => 0) 0 = ∑' e, tm e y := by
    intro y _
    rw [hid y, ← tsum_mul_left]
    refine tsum_congr fun e => ?_
    simp only [htm, hae]
    rw [← hint e (y 0)]
    ring
  -- the sum of the weights
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
  have hWfin : ENNReal.ofReal (bI * bR * bG) * ENNReal.ofReal ((latC P.d * P.L ^ P.d) ^ 2) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  rw [rn_congr θ hwin]
  refine (hsumivl q' 𝔏 ae ψ Me (ENNReal.ofReal (c2 * Ca)) Gf (ENNReal.ofReal bB * ENNReal.ofReal (J k)) hψm hψb
    haeb hGc hGb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top
    (hMsum.trans_lt hWfin)).trans ?_
  -- the algebra
  have hg := tc2a_incoh D Pp hdec hdB hsZ
  set g := LG.incoherency (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).links with hgdef
  set g' := gB + LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) + LGr.incoherency Qr.links +
    LGg.incoherency Qg.links with hg'
  have hn1 : nB + nI + nR + nG = n - 1 := by omega
  have hleaf := tc2a_leafSize D Pp Br
  have hcost := tc2a_cost D Pp S cω
  have hval : c2 * Ca * bB * (bI * bR * bG) = P.L ^ (4 * c') *
      (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g') * leafSizeProduct LG Br * starCost S cω) := by
    have h4c : P.L ^ (4 * c') = P.L ^ c' * P.L ^ c' * P.L ^ c' * P.L ^ c' := by
      rw [show 4 * c' = c' + c' + c' + c' by ring, Real.rpow_add (by linarith), Real.rpow_add (by linarith),
        Real.rpow_add (by linarith)]
    have h4 := rb_four (P := P) (by linarith : (0 : ℝ) < P.L) (n₁ := nB) (n₂ := nI) (n₃ := nR) (n₄ := nG)
      (g₁ := gB) (g₂ := LGi.incoherency (inner.treeLinks (LGi.garden.sig 0))) (g₃ := LGr.incoherency Qr.links)
      (g₄ := LGg.incoherency Qg.links)
    have h4' : rb P nB gB * rb P nI (LGi.incoherency (inner.treeLinks (LGi.garden.sig 0))) *
        rb P nR (LGr.incoherency Qr.links) * rb P nG (LGg.incoherency Qg.links) = P.C₁ ^ 3 * rb P (n - 1) g' := by
      rw [h4, ← hn1]; rfl
    rw [hbB, hbI, hbR, hbG, hleaf, hcost, hc2, ← h4', hCa, h4c]
    ring
  have hrbL : rb P (n - 1) g' ≤ P.L * rb P (n - 1) g := by
    by_cases hc : layerAt LG ((0 : Fin 2), []) = layerAt LG ((0 : Fin 2), bPath m inner)
    · rw [if_pos hc, add_zero] at hg
      have hgg : g' = g := by rw [hg]
      rw [hgg]
      exact le_mul_of_one_le_left (hrb _ _) hL1
    · rw [if_neg hc] at hg
      have hgg : g' = g - 1 := by omega
      have hpred := rb_pred_le hL1 hC1 K.hδ K.hη0 (n - 1) (show 1 ≤ g by omega)
      rw [Real.rpow_one] at hpred
      rw [hgg]
      exact hpred
  have hY : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 * P.C₁ ^ 3 * leafSizeProduct LG Br * starCost S cω := by
    have := starCost_nonneg' S cω
    have := hb0 LG Br
    positivity
  have hfin : coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g') * leafSizeProduct LG Br * starCost S cω ≤
      P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) * leafSizeProduct LG Br * starCost S cω) :=
    calc coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g') * leafSizeProduct LG Br * starCost S cω
        = (coupling P.d P.L P.γ P.δ ^ 2 * P.C₁ ^ 3 * leafSizeProduct LG Br * starCost S cω) * rb P (n - 1) g' := by
          ring
      _ ≤ (coupling P.d P.L P.γ P.δ ^ 2 * P.C₁ ^ 3 * leafSizeProduct LG Br * starCost S cω) *
            (P.L * rb P (n - 1) g) := mul_le_mul_of_nonneg_left hrbL hY
      _ = _ := by ring
  have hJk : ENNReal.ofReal (J k) = tcJ k := rfl
  have hwt : tcJ k * ENNReal.ofReal ((latC P.d * P.L ^ P.d) ^ 2) ≤ tcWt P.L k := le_add_self
  calc Cs * (ENNReal.ofReal (c2 * Ca) * (ENNReal.ofReal bB * ENNReal.ofReal (J k)) * ∑' e, ENNReal.ofReal (Me e))
      ≤ Cs * (ENNReal.ofReal (c2 * Ca) * (ENNReal.ofReal bB * ENNReal.ofReal (J k)) *
          (ENNReal.ofReal (bI * bR * bG) * ENNReal.ofReal ((latC P.d * P.L ^ P.d) ^ 2))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hMsum)
    _ = Cs * (ENNReal.ofReal (c2 * Ca * bB * (bI * bR * bG)) *
          (tcJ k * ENNReal.ofReal ((latC P.d * P.L ^ P.d) ^ 2))) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hc20 hCa0) hbB0), ENNReal.ofReal_mul (mul_nonneg hc20 hCa0),
          hJk]
        ring
    _ ≤ Cs * (ENNReal.ofReal (P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
          (P.C₁ ^ 3 * rb P (n - 1) g) * leafSizeProduct LG Br * starCost S cω))) * tcWt P.L k) := by
        rw [hval]
        exact mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hfin (Real.rpow_nonneg hL0 _))) hwt)
    _ = _ := by ring

end WaveTurbulence.Flower.ProtRT
