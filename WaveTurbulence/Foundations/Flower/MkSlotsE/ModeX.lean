/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsE.DomX

/-! # B3s-HELPER9 (MkSlotsE) 4: one outer slot mode at one outer centre

`repIntCMKS_modeX`: the twin of δ's `MkSlotsS.repIntCMKS_mode` (EngRepS.lean) for the per-mode outer form whose
decoration weight carries the outer node partition `chiX X` (the centre-indexed outer mode form of
`MkSlotsI.CentreForm`). The chain-slot amplitudes need NOT be localized: the localization at the centred chain slots
is `chiX X`, and the engine keeps only the assembled node centres restricting to `X` (`DomX.value_eqHMDX`). The mass is
`Cchi^{#br} · #(nodeCentreSet cl ∩ {x|centred = X}) · Π_j Mh_j · momS sel (routedFreq)`, with `cl` the leaf-pair
centres of the mode; summed over `X` the middle factor is at most `nodeBallCard^m` (`NodeX.tsum_ncard_ncsX_le`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsS
open WaveTurbulence.Flower.MkSlotsI (CentredSlot chiX)
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsE

variable {w d : ℕ}

/-- The leaf-pair centres of a one-mode family with slot centres `ctr`. -/
def leafCtr {S : Garden w} (hS : S.IsPlain) (ctr : ReplacementSlot S → Fin d → ℤ) : GLeaf S.tree → Fin d → ℤ :=
  fun ℓ => ctr (Sum.inl (pairOfLeaf S hS ℓ))

open scoped Classical in
/-- The restricted node-centre count of a one-mode family. -/
theorem tsum_slotFamMode_ncs {S : Garden w} (hS : S.IsPlain) (amp : ReplacementSlot S → Mom d → ℂ)
    (ctr : ReplacementSlot S → Fin d → ℤ) (fr : ReplacementSlot S → Fin 2 → ℤ) (h1 : ∀ s k, ‖amp s k‖ ≤ 1)
    (h2 : ∀ s, SNorm (30 * d) 0 (amp s) ≤ 1)
    (h3 : ∀ p k, amp (Sum.inl p) k ≠ 0 → ‖k - latPt d (ctr (Sum.inl p))‖ ≤ 1)
    (X : CentredSlot S → (Fin d → ℤ)) :
    ∑' ξ : XiT (slotFamMode amp ctr fr h1 h2 h3), ENNReal.ofReal
        ((∏ s, (slotFamMode amp ctr fr h1 h2 h3).w s (ξ.1 s)) *
          (if ξ.2 ∈ nodeCentreSet ((slotFamMode amp ctr fr h1 h2 h3).leafCentre hS ξ.1) then 1 else 0) *
          (if ResX X ξ.2 then 1 else 0)) =
      (((ncsX (leafCtr hS ctr) X).ncard : ℕ) : ℝ≥0∞) := by
  set fam := slotFamMode amp ctr fr h1 h2 h3 with hfam
  rw [ENNReal.tsum_prod (f := fun (ξ1 : ∀ s, fam.Λ s) (x : GBranch S.tree → Fin d → ℤ) => ENNReal.ofReal
    ((∏ s, fam.w s (ξ1 s)) * (if x ∈ nodeCentreSet (fam.leafCentre hS ξ1) then 1 else 0) *
      (if ResX X x then 1 else 0)))]
  have hin : ∀ ξ1 : ∀ s, fam.Λ s, ∑' x : GBranch S.tree → Fin d → ℤ, ENNReal.ofReal
      ((∏ s, fam.w s (ξ1 s)) * (if x ∈ nodeCentreSet (fam.leafCentre hS ξ1) then 1 else 0) *
        (if ResX X x then 1 else 0)) = (((ncsX (leafCtr hS ctr) X).ncard : ℕ) : ℝ≥0∞) := by
    intro ξ1
    rw [ncard_eq_tsum_of_finite (ncsX_finite _ X)]
    refine tsum_congr fun x => ?_
    have hw : ∏ s, fam.w s (ξ1 s) = 1 := Finset.prod_eq_one fun s _ => rfl
    have hcl : fam.leafCentre hS ξ1 = leafCtr hS ctr := rfl
    rw [hw, hcl, one_mul]
    have hmem : x ∈ ncsX (leafCtr hS ctr) X ↔ x ∈ nodeCentreSet (leafCtr hS ctr) ∧ ResX X x := Iff.rfl
    by_cases hx : x ∈ nodeCentreSet (leafCtr hS ctr)
    · by_cases hr : ResX X x
      · have hm : x ∈ ncsX (leafCtr hS ctr) X := hmem.2 ⟨hx, hr⟩
        simp only [hx, hr, hm, ite_true, mul_one, ENNReal.ofReal_one]
      · have hm : x ∉ ncsX (leafCtr hS ctr) X := fun h => hr (hmem.1 h).2
        simp only [hx, hr, hm, ite_true, ite_false, mul_zero, ENNReal.ofReal_zero]
    · have hm : x ∉ ncsX (leafCtr hS ctr) X := fun h => hx (hmem.1 h).1
      simp only [hx, hm, ite_false, zero_mul, ENNReal.ofReal_zero]
  simp_rw [hin]
  rw [tsum_eq_single (show ∀ s, fam.Λ s from fun _ => ())]
  intro b hb
  exact absurd (funext fun s => rfl) hb

open scoped Classical in
/-- **One outer slot mode at one outer centre** (δ's `repIntCMKS_mode` with the decoration weight `· chiX X`): the
per-mode outer form is a `RepIntCMKS` of mass `Cchi^{#br} · #ncsX · Π_j Mh_j · momS sel (routedFreq frq)`. -/
theorem repIntCMKS_modeX {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL0 : 0 < P.L) (π : Stage1PieceMK P.d R)
    (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    (hsliceD : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ Dom ↔ π.Gsb.extendFix π.fix τ ∈ fixLB π.Gsb π.layer tt π.fix π.lb)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    (amp : ReplacementSlot π.Gsb → Mom P.d → ℂ) (ctr : ReplacementSlot π.Gsb → Fin P.d → ℤ)
    (h1 : ∀ s k, ‖amp s k‖ ≤ 1) (h2 : ∀ s, SNorm (30 * P.d) 0 (amp s) ≤ 1)
    (h3 : ∀ p k, amp (Sum.inl p) k ≠ 0 → ‖k - latPt P.d (ctr (Sum.inl p))‖ ≤ 1)
    (frq : ReplacementSlot π.Gsb → Fin 2 → ℤ) {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ)
    (H : HingeFam J P.d) (Mh : J → ℝ) (hMh : ∀ j c, ∑' l, H.w j c l ≤ Mh j)
    (hHk : HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom (fun j => HkM j (modLam frq route j)) H)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r)
    (sel : Finset (GBranch π.Gsb.tree)) (hselclk : ∀ v ∈ sel, ∀ j i, hclk j i ≠ Sum.inr v)
    (X : CentredSlot π.Gsb → (Fin P.d → ℤ)) :
    RepIntCMKS π sel tt base roots
      (outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
        (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0) *
          chiX P.L base X z) hS
        (fixMeasure π.fix) amp frq route hclk hmom HkM)
      ((Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) * ((ncsX (leafCtr hS ctr) X).ncard : ℝ) *
        ∏ j, Mh j) * momS sel (routedFreq hS route frq)) := by
  obtain ⟨hCge, hCspec⟩ := Cchi_spec hd1
  have hCpos : 0 < Cchi P.d := lt_of_lt_of_le zero_lt_one hCge
  have hdom : ∀ τ ∈ domFix π.Gsb π.layer tt π.fix π.lb, τ ∈ Dom := fun τ hτ =>
    mem_of_mem_domFix π.Gsb π.layer tt π.fix π.lb Dom hsliceD hτ
  let fam := slotFamMode amp ctr (frqR frq route) h1 h2 h3
  let A : AsmCtxH π.Gsb P.d :=
    { hS := hS, hd := hd1, L := P.L, hL := hL0, γ := P.γ, δ := P.δ, η := P.η, base := base, roots := roots,
      tt := tt, layer0 := dummyLayer π.Gsb tt, gs := π.gapSpecification, selSk := selSk, hgs := hgsp,
      fam := fam, Cχ := Cchi P.d, hCpos := hCpos, hC := hCspec,
      Fn := fun s ts k => amp s k * fsPhase (frqR frq route s) ts, Box := fun _ => Set.univ,
      hFn := fun s ts _ k => by
        have := hasSum_fintype (fun _ : Unit => ((1 : ℝ) : ℂ) * amp s k * fsPhase (frqR frq route s) ts)
        simp [fam, slotFamMode],
      hbox := fun _ _ _ => Set.mem_univ _,
      hinges := π.Cs.hinges, J := J, fJ := inferInstance, dJ := inferInstance, H := H,
      hmom := hmom, hclk := hclk, Hk := fun j => HkM j (modLam frq route j), Mh := Mh, hMh := hMh,
      hHk := fun κ hsel τ hτ j c hc =>
        hHk κ hsel τ (hdom τ (splicedTimeDomain_dummyLayer_sub π.Gsb tt π.layer π.fix π.lb hτ)) j c hc,
      src := src, src_dart := src_dart, src_root := src_root }
  have hHkD : HkOn A (domFix π.Gsb π.layer A.tt π.fix π.lb) := fun κ hsel τ hτ j c hc => hHk κ hsel τ (hdom τ hτ) j c hc
  have hM0 : ∀ j, 0 ≤ Mh j := fun j => A.Mh_nonneg j (fun _ _ => 0)
  have hB0 : 0 ≤ Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) * ((ncsX (leafCtr hS ctr) X).ncard : ℝ) *
      ∏ j, Mh j := by
    have hMp : 0 ≤ ∏ j, Mh j := Finset.prod_nonneg fun j _ => hM0 j
    exact mul_nonneg (mul_nonneg (pow_nonneg hCpos.le _) (by positivity)) hMp
  have hval : outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
        (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0) *
          chiX P.L base X z) hS
        (fixMeasure π.fix) amp frq route hclk hmom HkM =
      (coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order * π.Gsb.zeta *
      ∑' κ : GenDecoration π.Gsb P.d A.roots 0, atomWF π.filt π.ind (cosetDecoration π.Gsb A.L A.base κ.1) *
        ((if A.selSk κ then ((splicedEpsilon π.Gsb A.hinges κ.1 : ℝ) : ℂ) else 0) *
          (chiX A.L A.base X κ * ∫ τ, (domFix π.Gsb π.layer A.tt π.fix π.lb).indicator (fun τ =>
            phaseProd A.L A.γ A.δ π.Gsb (cosetDecoration π.Gsb A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
            ∂(fixMeasure π.fix))) := by
    unfold outerValMμD
    congr 1
    refine tsum_congr fun κ => ?_
    have hI0 := integral_indicator_congr_slice π.Gsb π.fix Dom (domFix π.Gsb π.layer tt π.fix π.lb)
      (fun τ => (hsliceD τ).trans (extendFix_mem_domFix_iff π.Gsb π.layer tt π.fix π.lb τ).symm)
      (fun τ => phaseProd P.L P.γ P.δ π.Gsb (cosetDecoration π.Gsb P.L base κ.1) τ *
          (∏ s, amp s (base + latticePoint P.L (κ.1 (slotNode hS s)))) * routedPhase frq route tt τ *
          ∏ j, HkM j (modLam frq route j) (fun c => clockOf π.Gsb tt τ (hclk j c))
            (fun c => base + latticePoint P.L (κ.1 (hmom j c))))
    have hI : ∫ τ, (domFix π.Gsb π.layer tt π.fix π.lb).indicator (fun τ =>
        phaseProd P.L P.γ P.δ π.Gsb (cosetDecoration π.Gsb P.L base κ.1) τ *
          (∏ s, amp s (base + latticePoint P.L (κ.1 (slotNode hS s)))) * routedPhase frq route tt τ *
          ∏ j, HkM j (modLam frq route j) (fun c => clockOf π.Gsb tt τ (hclk j c))
            (fun c => base + latticePoint P.L (κ.1 (hmom j c)))) τ ∂(fixMeasure π.fix) =
        ∫ τ, (domFix π.Gsb π.layer A.tt π.fix π.lb).indicator (fun τ =>
          phaseProd A.L A.γ A.δ π.Gsb (cosetDecoration π.Gsb A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
          ∂(fixMeasure π.fix) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
      by_cases hτ : τ ∈ domFix π.Gsb π.layer tt π.fix π.lb
      · have hτ' : τ ∈ domFix π.Gsb π.layer A.tt π.fix π.lb := hτ
        rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hτ']
        show _ = phaseProd P.L P.γ P.δ π.Gsb (cosetDecoration π.Gsb P.L base κ.1) τ *
          ((∏ s, (amp s (base + latticePoint P.L (κ.1 (slotNode hS s))) *
              fsPhase (frqR frq route s) (slotTs hS tt τ s))) *
            ∏ j, HkM j (modLam frq route j) (fun c => clockOf π.Gsb tt τ (hclk j c))
              (fun c => base + latticePoint P.L (κ.1 (hmom j c))))
        rw [routedPhase_eq hS frq route hroute tt τ, Finset.prod_mul_distrib]
        ring
      · have hτ' : τ ∉ domFix π.Gsb π.layer A.tt π.fix π.lb := hτ
        rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hτ']
    rw [hI0, hI]
    generalize ∫ τ, (domFix π.Gsb π.layer A.tt π.fix π.lb).indicator (fun τ =>
          phaseProd A.L A.γ A.δ π.Gsb (cosetDecoration π.Gsb A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
          ∂(fixMeasure π.fix) = Y
    show ((splicedEpsilon π.Gsb π.Cs.hinges κ.1 : ℝ) : ℂ) *
        (atomWF π.filt π.ind (cosetDecoration π.Gsb P.L base κ.1) * (if selSk κ then 1 else 0) *
          chiX P.L base X κ) * Y =
      atomWF π.filt π.ind (cosetDecoration π.Gsb P.L base κ.1) *
        ((if selSk κ then ((splicedEpsilon π.Gsb π.Cs.hinges κ.1 : ℝ) : ℂ) else 0) * (chiX P.L base X κ * Y))
    by_cases hsel : selSk κ
    · simp only [hsel, ite_true]
      ring
    · simp only [hsel, ite_false, mul_zero, zero_mul]
  -- the frequencies at the selected branches are the routed slot frequencies
  have hM : ∀ ξh : A.Xi, momS sel (A.freqH ξh) ≤ momS sel (routedFreq hS route frq) := by
    intro ξh
    refine le_of_eq (Finset.prod_congr rfl fun v hv => ?_)
    have h0 : (∑ j, ∑ i, if A.hclk j i = Sum.inr v then (A.H.m j _ (ξh.2 j) i : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => if_neg (hselclk v hv j i)
    have hf : A.freqH ξh v = routedFreq hS route frq v := by
      unfold AsmCtxH.freqH
      rw [h0, add_zero]
      rfl
    rw [hf]
  -- the restricted mass
  have hmass : ∑' ξh : A.Xi, ENNReal.ofReal ‖cindX X ξh.1.2 * A.constWH ξh‖ ≤
      ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) * ((ncsX (leafCtr hS ctr) X).ncard : ℝ) *
        ∏ j, Mh j) := by
    refine (tsum_constWHX_le A X).trans ?_
    refine (mul_le_mul_of_nonneg_right (tsum_constWX_le A X) zero_le).trans (le_of_eq ?_)
    have hcnt := tsum_slotFamMode_ncs hS amp ctr (frqR frq route) h1 h2 h3 X
    have hcnt' : ∑' ξ : XiT A.fam, ENNReal.ofReal ((∏ s, A.fam.w s (ξ.1 s)) *
        (if ξ.2 ∈ nodeCentreSet (A.fam.leafCentre A.hS ξ.1) then 1 else 0) * (if ResX X ξ.2 then 1 else 0)) =
        (((ncsX (leafCtr hS ctr) X).ncard : ℕ) : ℝ≥0∞) := hcnt
    rw [hcnt']
    have e : ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
        ((ncsX (leafCtr hS ctr) X).ncard : ℝ) * ∏ j, Mh j) =
        ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree)) *
          (((ncsX (leafCtr hS ctr) X).ncard : ℕ) : ℝ≥0∞) * ∏ j, ENNReal.ofReal (Mh j) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (pow_nonneg hCpos.le _), ENNReal.ofReal_natCast,
        ENNReal.ofReal_prod_of_nonneg (fun j _ => hM0 j)]
    rw [e]
  have hF := repIntCMKF_of_asmHDX π A sel tt base roots rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _ _ _ => Set.mem_univ _) hHkD hfilt hind X _ hB0 hmass _ hM _ hval
  exact hF.toRepIntCMKS (momS_nonneg _ _)

end WaveTurbulence.Flower.MkSlotsE
