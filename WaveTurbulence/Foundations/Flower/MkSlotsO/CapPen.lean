/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.CapNontriv

/-! # B3s-HELPER8 / CAP: what holds on the STOP configuration

On a nontrivial cap slot whose configuration pins the root (`penTerm` / `rootTerm`), with no selected branch, the
general slot kernel is CONSTANT on the points of the general box with `ts j0 ≥ rootPinVal` (`= s` for `penTerm`), and
the constant obeys the slot mass bound (`constN`). On the STOP configuration `CapK.CapPenFree` (`penTerm` with a free
chain clock) there is no selected branch (`penFree_noSel`: the pattern is `dParent`) and `penFree_const` gives the
one-mode family on `genBoxAt ∩ {s ≤ ts j0}` — the box of β's `capPatBox` / R187's `lb`. The obligation as stated asks
in addition for `p ≤ ts j0 < s`, where the kernel is not constant and no proved gate applies (`Cap-NOTES.md`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Set
open WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.Induct
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsB WaveTurbulence.Flower.MkSlotsI

namespace WaveTurbulence.Flower.MkSlotsO

namespace CapN

section Slot

variable {P : WTParams} (hD3 : ProtBoundAt P) (hD6 : ProtAnnBoundAt P) (hd : 3 ≤ P.d) (hη : 0 < P.η)
  (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hL : 2 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ)
  (C : ℝ) (hC : P.C₁ ≤ C) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
  (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (hp : p < P.D) (hcan : IsCanonGC (p + 1) (recLG a)) (hsz : a.prime.data.size ≤ P.N (p + 1) ^ 4)
  (hGeo : CapGeo (recLG a) J p) (hpat : CapPatValid (recLG a) J pat p)
  (hps : (p : ℝ) < s) (hst : s < t) (htp : t < p + 1)
  (σ kSel : Fin (2 * R) → Option ℕ) (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain)
  (Rs : Fin (2 * R) → ℝ) (hRs : ∀ j, P.L ≤ Rs j)
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb1 : 1 ≤ b)
  (hb : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
  (Rf : Fin (2 * R) → Option ℝ) (hRf1 : ∀ j r, Rf j = some r → 1 ≤ r)
  (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) {q : SourcePair a.prime.skeleton}
  (hq : IsCapPair a.prime.skeleton a.prime.prime.1 J q) (K : CapSide a.prime.data a.prime.prime.1 J q)
  (x : Fin P.d → ℤ)


include hD3 hd hη hηγ hL hC1 hδ hC hp hcan hsz hGeo hpat hps hst htp hRs hb1 hb hRf1 hq in
/-- **A root-pinning configuration without selected branch: the kernel is constant above the root pin**, and the
constant obeys the slot mass bound. -/
theorem constN (hSel : CapK.capSelT K (sourceLayer a) (sourceLayer_isLayering a) kSel = ∅)
    (hroot : (CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat).pinsRoot K.X = true) :
    ∃ V : ℂ, ENNReal.ofReal (capKcen P.d) * ‖V‖ₑ ≤
        ENNReal.ofReal (capKg P.d P.η * genSlotMass P C b a J pat t s kSel Rs (.inl q)) ∧
      ∀ ts : Fin 2 → ℝ, rootPinVal (CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat) s t ≤ ts K.j0 →
        genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inl q) ts
          (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))) = V := by
  have hL1 : 1 ≤ P.L := by linarith
  have hb0 : 0 ≤ b := le_trans zero_le_one hb1
  have hprot := CapK.hasProtNative_cap K (sourceLayer a) (sourceLayer_isLayering a) pat t s kSel
  have hmass := genSlotMass_cap P C b a J pat t s kSel Rs q hq hprot
  rw [CapK.selNative_eq_empty K (sourceLayer a) (sourceLayer_isLayering a) hGeo kSel hSel, Finset.prod_empty]
    at hmass
  have hd0 : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
  have h31 : P.L ^ (31 * (P.d : ℝ) + 6) ≤ P.L ^ genLossExp P.d * 1 := by
    rw [mul_one]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by unfold genLossExp; linarith)
  have hm : capMN P a J K (p := p) σ kSel Rs Rf dag =
      capMF (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p)
        (IncTop.topStar (fun _ => (frontierG (Rf K.u.1) : Mom P.d → ℂ)))
        (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel) (fun _ => CapK.capMσ K P.L σ)
        (CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
        (CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs)
        (K.capInd (sourceLayer a) (sourceLayer_isLayering a) dag) := by
    unfold capMN
    rw [hSel]
    exact capMA_empty _ _ _ _ _ _ _ _
  set cfg := CapP.cfgPat K (sourceLayer a) (sourceLayer_isLayering a) pat with hcfgdef
  have hcfg := CapP.objCfg_cases K (sourceLayer a) (sourceLayer_isLayering a) pat
  have hne := cfg_ne_trace cfg hcfg
  set mF := capMF (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p)
        (IncTop.topStar (fun _ => (frontierG (Rf K.u.1) : Mom P.d → ℂ)))
        (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel) (fun _ => CapK.capMσ K P.L σ)
        (CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
        (CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs)
        (K.capInd (sourceLayer a) (sourceLayer_isLayering a) dag) with hmF
  set G := capCfgKer P.L P.γ P.δ (K.Dq (sourceLayer a) (sourceLayer_isLayering a)) (H1 P a J K h roots) mF cfg s t
    (latticePoint P.L (roots K.cleaf.1.1)) with hG
  have hconst : ∀ y, rootPinVal cfg s t ≤ y → G y = G t := by
    intro y hy
    rw [hG]
    unfold capCfgKer
    rw [fix_up_indep cfg hne K.X s t y 0, fix_up_indep cfg hne K.X s t t 0]
    obtain ⟨hr1, hr2⟩ := pinsRoot_fix hroot s t 0 hst.le
      (T := (K.Dq (sourceLayer a) (sourceLayer_isLayering a)).T1.garden.tree)
    exact kernelProt_up_const _ _ _ _ _ _ 0 _ _ _ _ (rootPinVal cfg s t)
      (fun b hb => by rw [hr1 b hb]; exact Option.some_ne_none _) hr2 y t hy (rootPinVal_le cfg hst.le)
  have hbound := capF_pointwise hD3 (K.Dq (sourceLayer a) (sourceLayer_isLayering a)) hη.le (by omega) hL1 hp
    (n_le_N a J hsz K) (K.protShape_T1 (sourceLayer a) (sourceLayer_isLayering a) hGeo) (protSize_N a J K) cfg
    (CapP.cfgPat_valid K (sourceLayer a) (sourceLayer_isLayering a) hpat) hcfg hroot
    (K.protAmbient_T1 (sourceLayer a) (sourceLayer_isLayering a) hcan) hps hst htp
    (K.frontS (sourceLayer a) (sourceLayer_isLayering a) p)
    (IncTop.topStar (fun _ => (frontierG (Rf K.u.1) : Mom P.d → ℂ))) (fun _ => frontierConst P.d)
    (hpres_N a J Rf hRf1 K) (CapK.capFT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
    (fun _ => CapK.capMσ K P.L σ) (hM_N hL a J σ kSel K)
    (CapK.capFuT K (sourceLayer a) (sourceLayer_isLayering a) σ kSel)
    (CapK.capMuT K (sourceLayer a) (sourceLayer_isLayering a) P.L σ kSel Rs) (hMu_N hL a J σ kSel Rs hRs K)
    (K.capInd (sourceLayer a) (sourceLayer_isLayering a) dag)
    (K.termChild_capInd (sourceLayer a) (sourceLayer_isLayering a) dag) 1 (norm_capMF_N a J σ kSel Rs Rf dag K)
    (H1 P a J K h roots) (fun _ => b.toNNReal)
    (K.capH1_leafwise (sourceLayer a) (sourceLayer_isLayering a) hGeo h P.L roots b hb0 hb)
    (latticePoint P.L (roots K.cleaf.1.1)) t ⟨le_rfl, htp.le⟩
  set c₀ := K.capC0 P.L P.γ P.δ s (latticePoint P.L (roots K.cleaf.1.1)) dag
  have hc₀ : ‖c₀‖ = 1 := K.norm_capC0 P.L P.γ P.δ s _ dag
  refine ⟨c₀ * G t, ?_, fun ts hts => ?_⟩
  · have h12 : ENNReal.ofReal (1 / 2) * 2 = 1 := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
      exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    rw [← ofReal_norm, norm_mul, hc₀, one_mul, ofReal_norm]
    refine le_trans ?_ (le_trans (massN hηγ hL hC1 hδ C hC a J b hb1 K (p := p) (ENNReal.ofReal (1 / 2))
      ENNReal.ofReal_ne_top (capKg P.d P.η) (by rw [ENNReal.toReal_ofReal (by norm_num)]; exact capKg_half P.d P.η)
      (P.L ^ (31 * (P.d : ℝ) + 6)) (P.L ^ genLossExp P.d) 1 (Real.rpow_nonneg (by linarith) _) h31)
      (by rw [hmass]))
    refine mul_le_mul' le_rfl (hbound.trans (le_of_eq ?_))
    rw [← mul_assoc, h12, one_mul]
  · rw [genSlotKer_capN P a J K hGeo hq pat t s σ kSel Rs h roots Rf dag ts]
    show c₀ * capCfgKer P.L P.γ P.δ (K.Dq (sourceLayer a) (sourceLayer_isLayering a)) (H1 P a J K h roots)
      (capMN P a J K (p := p) σ kSel Rs Rf dag) cfg s t (latticePoint P.L (roots K.cleaf.1.1)) (ts K.j0) = c₀ * G t
    rw [hm]
    exact congrArg (c₀ * ·) (hconst _ hts)

include hplain in
/-- On the STOP configuration there is no selected branch on the paired tree (the pattern is `dParent`). -/
theorem penFree_noSel (hpf : CapK.CapPenFree K (sourceLayer a) (sourceLayer_isLayering a) pat t s) :
    CapK.capSelT K (sourceLayer a) (sourceLayer_isLayering a) kSel = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun v1 hv1 => ?_
  have h1 := CapK.capSel_plain K (sourceLayer a) (sourceLayer_isLayering a) pat kSel hplain v1 hv1
  rw [(CapK.capPenFree_spec K (sourceLayer a) (sourceLayer_isLayering a) pat t s hpf).2.1] at h1
  cases h1

include hD3 hd hη hηγ hL hC1 hδ hC hp hcan hsz hGeo hpat hps hst htp hplain hRs hb1 hb hRf1 hq in
/-- **The STOP configuration on the cut box**: on `genBoxAt ∩ {s ≤ ts j0}` the general slot kernel is a constant
obeying the slot mass bound (so the one-mode family of `slotFam1_of_const` works there, at every moment weight). -/
theorem penFree_const (hpf : CapK.CapPenFree K (sourceLayer a) (sourceLayer_isLayering a) pat t s) :
    ∃ V : ℂ, ENNReal.ofReal (capKcen P.d) * ‖V‖ₑ ≤
        ENNReal.ofReal (capKg P.d P.η * genSlotMass P C b a J pat t s kSel Rs (.inl q)) ∧
      ∀ ts : Fin 2 → ℝ, s ≤ ts K.j0 →
        genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inl q) ts
          (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))) = V := by
  have hspec := CapK.capPenFree_spec K (sourceLayer a) (sourceLayer_isLayering a) pat t s hpf
  obtain ⟨V, hV, hVk⟩ := constN (hD3 := hD3) (hd := hd) (hη := hη) (hηγ := hηγ) (hL := hL) (hC1 := hC1)
    (hδ := hδ) (C := C) (hC := hC) (a := a) (J := J) (pat := pat) (t := t) (s := s) (hp := hp) (hcan := hcan)
    (hsz := hsz) (hGeo := hGeo) (hpat := hpat) (hps := hps) (hst := hst) (htp := htp) (σ := σ) (kSel := kSel)
    (Rs := Rs) (hRs := hRs) (roots := roots) (h := h) (b := b) (hb1 := hb1) (hb := hb) (Rf := Rf) (hRf1 := hRf1)
    (dag := dag) (hq := hq) (K := K)
    (hSel := penFree_noSel (a := a) (J := J) (pat := pat) (t := t) (s := s) (kSel := kSel) (hplain := hplain) (K := K) hpf)
    (hroot := hpf.1)
  refine ⟨V, hV, fun ts hts => hVk ts ?_⟩
  rw [hspec.1]
  unfold rootPinVal
  simpa using hts

end Slot

end CapN

end WaveTurbulence.Flower.MkSlotsO
