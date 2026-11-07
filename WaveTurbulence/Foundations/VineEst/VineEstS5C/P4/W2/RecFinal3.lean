/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecFinal2

/-! # P4-W2 (session 19, step 5): the certificate of one term, `term_rec_exists` -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13
open VineParamContract
open scoped ENNReal


variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

open Classical in
theorem term_rec_exists {Pe : WTParams} (hPe : AmbP 6561 Pe) (hL2 : 2 ≤ Pe.L) (hηγ : Pe.η ≤ Pe.γ)
    (hw : 0 ≤ Pe.gamma1 - Real.sqrt Pe.η)
    {C : ℝ≥0∞} (hC1 : 1 ≤ C) (hCt : C ≠ ⊤) (hbody : TermRecBody (A := 6561) Pe.d Pe.η C)
    {K0 : ℝ≥0∞} (hK0t : K0 ≠ ⊤) (hdisp : DispK01.{0} Pe K0) (hd2 : DispK2.{0} Pe (Pe.D : ℝ) K0)
    (cf Kr Kb Km : ℝ) (hcf : C.toReal ≤ cf) (hKr : cf * 2 * (rowCb Pe * Pe.C₁ ^ 2) ≤ Kr) (hKr1 : 1 ≤ Kr)
    (hKb : (Kall Pe.d (K0 * ENNReal.ofReal (K2.KxX Pe.η))).toReal * (4 * TR Pe.η ^ 2 * trC (6 * Pe.η ^ 6) ^ 2 / rowCb Pe ^ 2) ≤ Kb) (hKb1 : 1 ≤ Kb)
    (hKm1 : 1 ≤ Km) (hKm : 3 * max (tcSq Pe.η) 1 ≤ Km)
    {p : ℕ} (h : ℕ → Mom Pe.d → ℝ) (B₀ : ℝ) (wBar : Mom Pe.d) (hB₀ : 0 < B₀)
    (E : GateEnv Pe (kparOf Pe.L Pe.γ Pe.δ h wBar) p (fun _ => B₀)) (hinc : IncoherentGateH Pe)
    (hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (hcan : CanonicalObject p kind (layeredReconstruction RD hG layer hLayer)) (hlay : ∀ x, layer x ≤ p)
    (hord : (RD.garden hG).order ≤ Pe.N (p + 1) ^ 4) (hl1 : clLocalOrder1 R ≤ Pe.N 1 ^ 4)
    (centre : Fin 4 → Mom Pe.d) (lam : ℝ) (hR : RealityAll)
    (hcoh : RowCoherent hM9 B RD hG layer hLayer
      (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      Pe.L Pe.γ Pe.δ h p) :
    ∀ ψ ∈ Lvl.termsB (p := p) (kind := kind) B RD hG layer hLayer
          (bundleFamOf B RD hG layer hLayer hR (sffOf (hprime := hprime) B RD hG layer hLayer E hord))
          (bundleBotFamOf B RD hG layer hLayer hprime hR
            (WaveTurbulence.VineEstS5C.P4.Final.botSffOf B RD hG layer hLayer hprime E hord))
          (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B),
      ∃ q : ℝ≥0∞, (∀ β', q ≤ β' →
          TermCertW (A := 6561) B hG (kparOf Pe.L Pe.γ Pe.δ h wBar) (Lvl.top B) (modPsi b lam ψ)
            (openTop (WaveTurbulence.VineEstS3.Eng.outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer)
              (qOutOf RD hG layer a b R) centre wBar)) (layer (RD.coreBranch hG a).toNode : ℝ))
            (WaveTurbulence.VineEstS3.Eng.outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer)
              (qOutOf RD hG layer a b R) centre wBar) Pe.L Pe.γ Pe.η) β') ∧
        ‖(coupling Pe.d Pe.L Pe.γ Pe.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R‖ₑ * q ≤
          ENNReal.ofReal ((1 + |lam|) ^ (6 * Pe.η ^ 6) * ((engNs Pe.η Pe.C₁ Km Kr * Real.sqrt Pe.δ) ^ clLocalOrder2 RD hG R *
            (Kb ^ (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card *
            Pe.L ^ (-(Pe.η ^ 8 * ((cohmolIndex B RD hG layer +
              (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
              Pe.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + Pe.η ^ 7)) *
            regionLeafSize RD hG R layer hLayer (fun _ => B₀))) := by
  intro ψ hψ
  have hd1 : 1 ≤ Pe.d := hPe.hd1
  have hL0 : 0 < Pe.L := by linarith
  have hC1' : 1 ≤ Pe.C₁ := E.hC
  have hδ : 0 < Pe.δ := hPe.hδ
  have hη0 : 0 < Pe.η := hPe.hη0
  have hη1 : Pe.η ≤ 1 := by have := hPe.hη1; linarith
  have hcb : 0 < rowCb Pe := by unfold rowCb; have := WaveTurbulence.PL2330.cLeib_nonneg Pe.d (30 * Pe.d); linarith
  set κ := kparOf Pe.L Pe.γ Pe.δ h wBar with hκ
  have Re : RemEnv Pe κ := ⟨hd1, by linarith, hδ, hPe.hθη, rfl, rfl⟩
  have hL : κ.L ≠ 0 := hL0.ne'
  set SFF := sffOf (hprime := hprime) B RD hG layer hLayer E hord with hSFF
  set BSFF := WaveTurbulence.VineEstS5C.P4.Final.botSffOf B RD hG layer hLayer hprime E hord with hBSFF
  have hQ := hfreeAt_holds_fam B RD hG layer hLayer hR SFF hprime BSFF hM9 hL hcan ψ hψ
  obtain ⟨recs, Dm, ⟨hexc, hnp, hnb, hDm', hNE'⟩, hfree⟩ := hQ
  have hreg : ∀ r ∈ recs, r.p0 ∈ clRegionalPairs hG U := fun r hr => (hexc r hr).2.1
  have hbjI : ∀ r ∈ recs, r.bj ∈ clInteriorBranches R := fun r hr => (hexc r hr).2.2
  have hblkinj : ∀ r ∈ recs, ∀ r' ∈ recs, r.blk = r'.blk → r = r' := by
    intro r hr r' hr' hb
    have hp := excOf_block_inj B RD hG layer hLayer _ _ _ _ (hexc r hr).1 (hexc r' hr').1 (hreg r hr) (hreg r' hr') hb
    exact List.inj_on_of_nodup_map hnp hr hr' hp
  have blkOf : ∀ r (hr : r ∈ recs), (assemblyPairBij hG B hM9 ⟨r.p0, hreg r hr⟩).1.val = r.blk := fun r hr =>
    excOf_pairBij_fst B RD hG layer hLayer _ _ _ _ hM9 (hexc r hr).1 (hreg r hr)
  have hbjl : ∀ r ∈ recs, ∀ i : Fin (assemblyShape hM9 B).I, r.blk = i.val →
      r.bj = (assemblyClockAtomEquiv hM9 B (.inl ⟨i, 0⟩)).1 := fun r hr i hi =>
    excOf_bj_lower B RD hG layer hLayer _ _ _ _ hM9 (hexc r hr).1 i hi
  have hnorR : ∀ r ∈ recs, ∀ i : Fin (assemblyShape hM9 B).I, r.blk = i.val → (assemblyShape hM9 B).nor i = false :=
    fun r hr i hi => excOf_nor_false B RD hG layer hLayer _ _ _ _ hM9 (hexc r hr).1 i hi
  set W0 := termW hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar lam with hW0
  set KZ : ℝ := 4 * TR Pe.η ^ 2 * trC (6 * Pe.η ^ 6) ^ 2 / rowCb Pe ^ 2 with hKZ
  set Lw : ℝ := Pe.L ^ (-(Pe.gamma1 - Real.sqrt Pe.η)) with hLw
  let ZB : ↥(clRegionalPairs hG U) → ↥(clInteriorBranches R) → ℝ := fun p0 c0 =>
    rowBoundH hM9 B RD hG layer hLayer Pe (fun _ => B₀) W0 (Sum.inl (assemblyPairBij hG B hM9 p0)) *
      rowBoundH hM9 B RD hG layer hLayer Pe (fun _ => B₀) W0 (Sum.inr (assemblyBranchBij hM9 B c0))
  let srcS : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar),
      StepSrc B RD hG layer hLayer SFF lv pstar hk hop :=
    fun lv pstar hk hop => stepSrcC B RD hG layer hLayer hprime Re E hord hC1' hB₀ lv pstar hk hop
  let srcB : ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      BotSrc B RD hG layer hLayer BSFF lv pstar h0 hop hmax :=
    fun lv pstar h0 hop hmax => botSrcC B RD hG layer hLayer hprime Re E hord hC1' hB₀ lv pstar h0 hop hmax
  have hgS : ∀ lv pstar hk hop, StepGood B RD hG layer hLayer SFF lv pstar hk hop (srcS lv pstar hk hop) :=
    fun lv pstar hk hop b' hb' => hb'
  have hgB : ∀ lv pstar h0 hop hmax, BotGood B RD hG layer hLayer BSFF lv pstar h0 hop hmax (srcB lv pstar h0 hop hmax) :=
    fun lv pstar h0 hop hmax b' hb' => hb'
  have hszS : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (c' : (bundleExpOf B RD hG layer hLayer hR lv pstar hk (zpSurj_of_op B RD hG layer hLayer lv pstar hk hop)
        (zpLayers_of_op B RD hG layer hLayer lv pstar hk hop) (retParent _) (SFF lv pstar hk hop)).Ch)
      (p0 : ↥(clRegionalPairs hG U)) (_ : p0.1 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
        ((lv.state B RD hG layer hLayer).family.placement pstar).retained)
      (c0 : ↥(clInteriorBranches R)) (_ : c0.1 = (lv.split B RD hG layer hLayer pstar hk).sb.b),
      (srcS lv pstar hk hop).sz c' ≤ KZ * ZB p0 c0 * (if recKind c' = 3 then Lw else 1) := by
    intro lv pstar hk hop c' p0 hp0 c0 hc0
    refine stepSrcC_sz_rows B RD hG layer hLayer hM9 W0 hprime Re E hord hC1' hB₀ hη0 hη1 hcb hw lv pstar hk hop c' ?_ p0 hp0 c0 hc0
    intro b' hb'
    rcases hb' with hb' | hb' | hb' | hb' <;>
      first | exact Or.inl hb' | exact Or.inr hb' | (split_ifs at hb' <;> first | exact Or.inl hb' | exact Or.inr hb')
  have hszB : ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
      (c : (bundleBotFamOf B RD hG layer hLayer hprime hR BSFF lv pstar h0 hop hmax).Ch)
      (p0 : ↥(clRegionalPairs hG U)) (_ : p0.1 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
        ((lv.state B RD hG layer hLayer).family.placement pstar).retained)
      (c0 : ↥(clInteriorBranches R)) (_ : c0.1 = lv.c.b),
      (srcB lv pstar h0 hop hmax).sz c ≤ KZ * ZB p0 c0 * (if recKind c = 3 then Lw else 1) := by
    intro lv pstar h0 hop hmax c p0 hp0 c0 hc0
    refine botSrcC_sz_rows B RD hG layer hLayer hM9 W0 hprime Re E hord hC1' hB₀ hη0 hη1 hcb hw lv pstar h0 hop hmax c ?_ p0 hp0 c0 hc0
    intro b' hb'
    rcases hb' with hb' | hb' | hb' | hb' <;>
      first | exact Or.inl hb' | exact Or.inr hb' | (split_ifs at hb' <;> first | exact Or.inl hb' | exact Or.inr hb')
  have hη4 : Pe.η < 1 / 4 := hPe.hη4
  have hKX1 : 1 ≤ K2.KxX Pe.η := (K2.KxX_spec hη0 hη4).1
  let xsS : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar),
      ((zpQ4 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1 ≤ ((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) →
        K2.XCross Pe (srcS lv pstar hk hop) :=
    fun lv pstar hk hop h => stepXC B RD hG layer hLayer hprime Re E hord hC1' hB₀ hη0 hη4 lv pstar hk hop h
  let xsB : ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      ((zpQ4 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1 ≤ ((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) →
        K2.XCross Pe (srcB lv pstar h0 hop hmax) :=
    fun lv pstar h0 hop hmax h => botXC B RD hG layer hLayer hprime Re E hord hC1' hB₀ hη0 hη4 lv pstar h0 hop hmax h
  have hRbq : ∀ (lv : Lvl B) (pstar : lv.ι) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar),
      max (((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) (((zpQ2 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) ≤ (Pe.D : ℝ) := by
    intro lv pstar hop
    have h1 := zpQh_le_p (lv.state B RD hG layer hLayer) hop.some.canonical hop.some.eligible hop.some.treeCoherent hop.some.coupleCoherent
    have h2 := zpQ2_le_zpQ4 (lv.state B RD hG layer hLayer) hop.some.canonical hop.some.eligible hop.some.treeCoherent hop.some.coupleCoherent
    have h3 := zpQ4_le_zpQh (lv.state B RD hG layer hLayer) hop.some.canonical hop.some.eligible hop.some.treeCoherent hop.some.coupleCoherent
    have h4 : p < Pe.D := E.hp
    have h5 : zpQh (lv.state B RD hG layer hLayer) pstar + 1 ≤ Pe.D := by omega
    have h6 : zpQ2 (lv.state B RD hG layer hLayer) pstar + 1 ≤ Pe.D := by omega
    refine max_le ?_ ?_
    · exact_mod_cast h5
    · exact_mod_cast h6
  have hRbS : ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar),
      max (((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) (((zpQ2 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) ≤ (Pe.D : ℝ) :=
    fun lv pstar _ hop => hRbq lv pstar hop
  have hRbB : ∀ (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      max (((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) (((zpQ2 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) ≤ (Pe.D : ℝ) :=
    fun lv pstar _ hop _ => hRbq lv pstar hop
  have hall : ∀ r (hr : r ∈ recs), ∃ (kd : ℕ) (zc : Prop) (addr : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (bnd : ℝ≥0∞),
      RecSpec (P := Pe) (κ0 := κ) B RD hG layer hM9 hL r (hreg r hr) (hbjI r hr) kd zc addr bnd ∧
      bnd ≤ Kall Pe.d (K0 * ENNReal.ofReal (K2.KxX Pe.η)) * ENNReal.ofReal (KZ * ZB ⟨r.p0, hreg r hr⟩ ⟨r.bj, hbjI r hr⟩ * (if kd = 3 then Lw else 1)) :=
    fun r hr => exists_recSpec B RD hG layer hLayer hR SFF hprime BSFF hdisp hd2 hM9 hL srcS hgS srcB hgB KZ Lw ZB hszS hszB xsS xsB (K2.KxX Pe.η) hKX1 (fun _ _ _ _ _ => le_rfl) (fun _ _ _ _ _ _ => le_rfl) hRbS hRbB r
      (hexc r hr).1 (hreg r hr) (hbjI r hr)
  choose! kd zc addr bnd hsp using hall
  have hfreeR : ∀ i : Fin n, (∀ r ∈ recs, r.blk ≠ i.val) → (assemblyPieceAt B i).vineType.IsBad = true → ¬ AClause hM9 B RD hG layer i →
      ∃ v : (assemblyShape hM9 B).VIdx, v.1 = i ∧
        1 ≤ max (rowCoupleG hM9 B RD hG layer hLayer v) (rowTreeG hM9 B RD hG layer hLayer v) := by
    intro i hi hbad hnac
    rcases hfree i hbad hnac with ⟨r, hr, hh, hh2⟩ | hv
    · exact absurd ((blkOf r hr).symm.trans (by rw [hh2])) (hi r hr)
    · exact hv
  set Bx : Set (Fin 3 → ℝ) := openTop (WaveTurbulence.VineEstS3.Eng.outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer)
    (qOutOf RD hG layer a b R) centre wBar)) (layer (RD.coreBranch hG a).toNode : ℝ) with hBxdef
  have hBx : Bx ⊆ WaveTurbulence.VineEstS3Par.Eng.outBox
      (natEng hM9 B RD hG layer hLayer (qOutOf RD hG layer a b R) centre wBar lam) := openTop_subset _ _
  have hext : ∀ tt ∈ Bx, ((layC RD hG layer a : ℕ) : ℝ) < tt 0 ∧ tt 0 < (layC RD hG layer a : ℕ) + 1 := by
    intro tt htt
    obtain ⟨hbx, hne⟩ := htt
    have h0 := (hbx.1 0)
    have hne' : tt 0 ≠ ((layer (RD.coreBranch hG a).toNode : ℕ) : ℝ) ∧ tt 0 ≠ ((layer (RD.coreBranch hG a).toNode : ℕ) : ℝ) + 1 := by
      constructor
      · intro he; exact hne (Or.inl he)
      · intro he; exact hne (Or.inr he)
    exact ⟨lt_of_le_of_ne h0.1 (Ne.symm hne'.1), lt_of_le_of_ne h0.2 hne'.2⟩
  obtain ⟨vpf, vbf, hvpf, hvbf⟩ := exists_row_maps hM9 B hG recs hreg hbjI
  have hspec : ∀ r (hr : r ∈ recs), RecSpec (P := Pe) (κ0 := κ) B RD hG layer hM9 hL r (hreg r hr) (hbjI r hr)
      (kd r) (zc r) (addr r) (bnd r) := fun r hr => (hsp r hr).1
  have hNE : RowFormNE RD hG Pe.L Pe.γ Pe.δ h layer hLayer R wBar ψ Dm (pexOf recs) (bexOf recs) (xqOf recs) := by
    have := hNE'
    rw [top_region_eq B] at this
    exact this
  have hDm : ∀ t u, u a = t 0 → (Dm t u ↔ DomX R (fun v => layer (RD.coreBranch hG v).toNode) (bexOf recs) (t 0) (t 1) (t 2) u) := by
    intro t u hu
    have := hDm' t u hu
    rw [top_region_eq B] at this
    exact this
  obtain ⟨q, hqc, Rb, hqRb, hRbN, hRb1⟩ := hbody Pe rfl rfl hPe (le_refl _) E.hg hinc hC1' (by linarith) hw hηγ E.hp E.hB
    (fun r _ => hB₀) hM9 B RD hG layer hLayer hlay hord hl1 centre wBar lam hcoh ψ Dm recs hNE hDm hnp hnb hreg hbjI hblkinj blkOf hbjl hnorR
    kd zc addr bnd hspec hfreeR Bx _ hBx hext rfl
  refine ⟨q, fun β' hβ' => termCertW_of_G B hG κ (modPsi b lam ψ) _ _ β' (hqc β' hβ'), ?_⟩
  have hM1 : 1 ≤ clLocalOrder1 R := M_pos hM9 B
  have hζ := norm_clLocalZeta R
  have hn2 := (order2_eq' hM9 B RD hG).symm
  set bb := (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card with hbbdef
  have hbb : recs.toFinset.card ≤ bb := by
    refine Finset.card_le_card_of_injOn (fun r => (vpf r).1) ?_ ?_
    · intro r hr
      have hr' := List.mem_toFinset.1 hr
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact hnorR r hr' _ (by rw [hvpf r hr']; exact (blkOf r hr').symm)
    · intro r hr r' hr' he
      have hr1 := List.mem_toFinset.1 hr
      have hr1' := List.mem_toFinset.1 hr'
      refine hblkinj r hr1 r' hr1' ?_
      have this : ((vpf r).1 : ℕ) = (vpf r').1 := congrArg Fin.val he
      rw [hvpf r hr1, hvpf r' hr1'] at this
      rw [← blkOf r hr1, ← blkOf r' hr1']
      exact this
  have hKZ0 : 0 ≤ KZ := by positivity
  have hLw0 : 0 ≤ Lw := Real.rpow_nonneg hL0.le _
  have hrb0 : ∀ ρ, 0 ≤ rowBoundH hM9 B RD hG layer hLayer Pe (fun _ => B₀) W0 ρ :=
    fun ρ => rowBoundH_nonneg E.hB hM9 B RD hG layer hLayer hlay hC1' hδ hL0 W0 ρ
  have hvp : ∀ r ∈ recs, (assemblyPairOf hM9 B hG (vpf r)).1 = r.p0 := fun r hr => by
    rw [hvpf r hr, assemblyPairOf_bij]
  have hinj1 : ∀ r ∈ recs, ∀ r' ∈ recs, vpf r = vpf r' → r = r' := by
    intro r hr r' hr' he
    refine hblkinj r hr r' hr' ?_
    rw [← blkOf r hr, ← blkOf r' hr', ← hvpf r hr, ← hvpf r' hr', he]
  have hinj2 : ∀ r ∈ recs, ∀ r' ∈ recs, vbf r = vbf r' → r = r' := by
    intro r hr r' hr' he
    rw [hvbf r hr, hvbf r' hr'] at he
    have := congrArg (fun z : ↥(clInteriorBranches R) => z.1) ((assemblyBranchBij hM9 B).injective he)
    exact List.inj_on_of_nodup_map hnb hr hr' this
  have hcfnn : 0 ≤ cf := (ENNReal.toReal_nonneg).trans hcf
  have hX0 : 0 ≤ cf * 2 * (rowCb Pe * Pe.C₁ ^ 2) := by positivity
  have hrows := hrows_rec (P := Pe) E.hB hM9 B RD hG layer hLayer hlay recs kd zc addr centre wBar lam (by linarith) hC1' hδ hw hCt cf hcf vpf vbf hvp
    hinj1 hinj2 bnd Rb
    (fun ρ hρ => hRbN ρ (fun r hr => by
      have := hρ r hr
      rwa [hvpf r hr, hvbf r hr] at this))
    (fun r hr => by rw [hvpf r hr]; exact (hRb1 r hr).1)
    (fun r hr => by rw [hvbf r hr]; exact (hRb1 r hr).2)
    ((Kall Pe.d (K0 * ENNReal.ofReal (K2.KxX Pe.η))).toReal * KZ) (by positivity)
    (fun r hr => by
      have hbn := (hsp r hr).2
      have key := rec_bnd_le (K := Kall Pe.d (K0 * ENNReal.ofReal (K2.KxX Pe.η))) (Kall_ne_top Pe.d (ENNReal.mul_ne_top hK0t ENNReal.ofReal_ne_top)) (KZ := KZ) hKZ0
        (hrb0 (Sum.inl (assemblyPairBij hG B hM9 ⟨r.p0, hreg r hr⟩))) (hrb0 (Sum.inr (assemblyBranchBij hM9 B ⟨r.bj, hbjI r hr⟩)))
        hLw0 hC1 (kd r = 3)
      rw [hvpf r hr, hvbf r hr]
      exact hbn.trans key)
    Kr Kb hKr hKb hKb1 hX0 hbb
  have hnum : cohmolIndex B RD hG layer + (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ ≤
      (recEng hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam).M₀ + (recEng hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam).M₁ := by
    have h0 := cohmolIndex_le_M0 hM9 B RD hG layer
      (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) rfl
    have h1 := recM1_ge hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam
    exact Nat.add_le_add h0 h1
  have hmass : tcSq Pe.η * ((3 : ℝ) ^ (clLocalOrder1 R + 1)) ≤ Km ^ (clLocalOrder1 R + 1) := by
    have hT0 : 0 ≤ tcSq Pe.η := ENNReal.toReal_nonneg
    have hm1 : (1 : ℝ) ≤ max (tcSq Pe.η) 1 := le_max_right _ _
    calc tcSq Pe.η * (3 : ℝ) ^ (clLocalOrder1 R + 1) ≤ max (tcSq Pe.η) 1 * (3 : ℝ) ^ (clLocalOrder1 R + 1) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max (tcSq Pe.η) 1 ^ (clLocalOrder1 R + 1) * (3 : ℝ) ^ (clLocalOrder1 R + 1) :=
          mul_le_mul_of_nonneg_right (by
            calc max (tcSq Pe.η) 1 = max (tcSq Pe.η) 1 ^ 1 := (pow_one _).symm
              _ ≤ max (tcSq Pe.η) 1 ^ (clLocalOrder1 R + 1) := pow_le_pow_right₀ hm1 (by omega)) (by positivity)
      _ = (3 * max (tcSq Pe.η) 1) ^ (clLocalOrder1 R + 1) := by rw [← mul_pow]; ring
      _ ≤ Km ^ (clLocalOrder1 R + 1) := pow_le_pow_left₀ (by positivity) hKm _
  have hlf : 0 ≤ Kb ^ bb * regionLeafSize RD hG R layer hLayer (fun _ => B₀) :=
    mul_nonneg (pow_nonneg (by linarith) _) (regionLeafSize_nonneg E.hB hM9 B RD hG layer hLayer hlay W0)
  have hlit := engine_literal (D := recEng hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) q
    ((3 : ℝ) ^ (clLocalOrder1 R + 1)) Rb hqRb (clLocalZeta R) hζ (M := clLocalOrder1 R)
    (Sn := (∑ v : (assemblyShape hM9 B).VIdx, (rowCouple hM9 B RD hG v).size / 2) +
      ∑ v : (assemblyShape hM9 B).VIdx, (rowTree hM9 B RD v).size / 2)
    (n2 := clLocalOrder2 RD hG R) (bb := bb) (M0s := cohmolIndex B RD hG layer)
    (M1s := (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁)
    (Λ := (1 + |lam|) ^ (6 * Pe.η ^ 6)) (Km := Km) (Kr := Kr)
    (lf := Kb ^ bb * regionLeafSize RD hG R layer hLayer (fun _ => B₀))
    (assemblyShape_M hM9 B) hM1 hn2 rfl hnum (by positivity) hmass hKm1
    (maxPar_rec_le hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam Pe.η hη0) hrows hKr1 hlf (by linarith) hδ hC1' hη0 hη1
  refine hlit.trans (le_of_eq ?_)
  congr 1
  ring
