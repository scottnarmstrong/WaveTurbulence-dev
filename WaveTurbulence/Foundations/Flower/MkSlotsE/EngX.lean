/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsE.MomX
public import WaveTurbulence.Foundations.Flower.MkSlotsS.EngVNS

/-! # B3s-HELPER9 (MkSlotsE) 6: the centre-indexed selected engine

* `repIntCMKS_centre_one` / `repIntCMKS_centre_modes`: the twin of δ's `MkSlotsS.repIntCMKS_vine_modes` for the
  centre-indexed outer mode form `Σ_i sgn i Σ'_X Σ'_ξ (Π_t w) · outerValMμD … (Zw · chiX X) …` of
  `MkSlotsI.CentreForm`: each mode `⟨X, ξ⟩` is represented by `ModeX.repIntCMKS_modeX` (node centres restricting to
  `X`), the masses are summed by `MomX.centre_modes_mass_le` (the per-centre slot masses `μs` uniform in `X`, the
  outer centres paid by the node-centre count `nodeBallCard^m`);
* `repIntCMKS_of_centreModes`: the numerics of δ's `repIntCMKS_of_vineModesFixD` (copied: the hypotheses on `μs`,
  `lf`, `M0`, … are those of δ's engine, independent of `X`);
* **`representsIntMKSel_of_centreModes`** (the deliverable), **`repMK_of_centreModes`** (the `repMK` companion) and
  **`centreEngine : MkSlotsI.CentreEngine`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.MkSlots
  WaveTurbulence.Flower.MkSlotsS
open WaveTurbulence.Flower.MkSlotsI (CentredSlot chiX famX ChainPiece)
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsE

open scoped Classical in
/-- The centre-indexed per-mode value: `(Π_t w) · outerValMμD … (Zw · chiX X) …` at the mode `⟨X, ξ⟩`. -/
def centreVal {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    {J : Type} [Fintype J] [DecidableEq J] (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (fam₀ : SlotFam π.Gsb P.d) (famC : CentredSlot π.Gsb → (Fin P.d → ℤ) → ChainPiece P.d)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ)
    (p : Σ X : CentredSlot π.Gsb → (Fin P.d → ℤ), ∀ t, (famX fam₀ famC X).Λ t) : ℂ :=
  (((∏ t, (famX fam₀ famC p.1).w t (p.2 t) : ℝ)) : ℂ) *
    outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
      (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0) *
        chiX P.L base p.1 z) hS
      (fixMeasure π.fix)
      (fun t => (famX fam₀ famC p.1).a t (p.2 t)) (fun t => (famX fam₀ famC p.1).m t (p.2 t))
      route hclk hmom HkM

open scoped Classical in
/-- **One class term of the centre-indexed form** (twin of one summand of δ's `repIntCMKS_vine_modes`): the modes
`⟨X, ξ⟩` are summable and their sum is a `RepIntCMKS` of mass `Bi` as soon as
`Cchi^{#br} · nodeBallCard^m · Kh · Π_s (9 selF_s · μ_s) ≤ Bi`, with `μ_s` bounding the slot moments of
`famX fam₀ famC X` for EVERY `X`. -/
theorem repIntCMKS_centre_one {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL0 : 0 < P.L) (π : Stage1PieceMK P.d R)
    (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    (hsliceD : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ Dom ↔ π.Gsb.extendFix π.fix τ ∈ fixLB π.Gsb π.layer tt π.fix π.lb)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r)
    (sel : Finset (GBranch π.Gsb.tree)) (hselclk : ∀ v ∈ sel, ∀ j i, hclk j i ≠ Sum.inr v)
    (fam₀ : SlotFam π.Gsb P.d) (famC : CentredSlot π.Gsb → (Fin P.d → ℤ) → ChainPiece P.d)
    (μs : ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (θs : ReplacementSlot π.Gsb → ℝ) (hcθ : ∀ s, 2 * c + (selE route sel s 0 + selE route sel s 1) ≤ θs s)
    (hμ : ∀ (X : CentredSlot π.Gsb → (Fin P.d → ℤ)) s, ∑' l, maxBracketPow (θs s)
      (half ((famX fam₀ famC X).m s l)) * ENNReal.ofReal ((famX fam₀ famC X).w s l) ≤ μs s)
    (Kh : ℝ) (hKh : 0 ≤ Kh)
    (hhinge : ∀ (X : CentredSlot π.Gsb → (Fin P.d → ℤ)) (ξ : ∀ s, (famX fam₀ famC X).Λ s),
      ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom
        (fun j => HkM j (modLam (fun s => (famX fam₀ famC X).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ Kh * ∏ j, (1 + |((modLam (fun s => (famX fam₀ famC X).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (Bi : ℝ) (hBi : 0 ≤ Bi)
    (hBi' : ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
        ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * Kh) *
        ∏ s, (ENNReal.ofReal (9 * selF route sel s) * μs s) ≤ ENNReal.ofReal Bi) :
    Summable (centreVal π hS tt base roots selSk Dom route hclk hmom fam₀ famC HkM) ∧
    RepIntCMKS π sel tt base roots
      (∑' X : CentredSlot π.Gsb → (Fin P.d → ℤ), ∑' ξ : ∀ t, (famX fam₀ famC X).Λ t,
        centreVal π hS tt base roots selSk Dom route hclk hmom fam₀ famC HkM ⟨X, ξ⟩) Bi := by
  obtain ⟨hCge, -⟩ := Cchi_spec hd1
  have hCpos : 0 < Cchi P.d := lt_of_lt_of_le zero_lt_one hCge
  set C0 : ℝ := Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) with hC0
  have hC00 : 0 ≤ C0 := pow_nonneg hCpos.le _
  set T : (CentredSlot π.Gsb → (Fin P.d → ℤ)) → SlotFam π.Gsb P.d := fun X => famX fam₀ famC X with hT
  have hcnt : ∀ X s, Countable ((T X).Λ s) := fun X => (T X).cnt
  choose H Mh hMh hHk hMhb using hhinge
  have hMh0 : ∀ X ξ j, 0 ≤ Mh X ξ j := fun X ξ j =>
    le_trans (tsum_nonneg fun l => (H X ξ).w_nn j (fun _ _ => 0) l) (hMh X ξ j (fun _ _ => 0))
  -- the count of a mode
  set Nc : (Σ X : CentredSlot π.Gsb → (Fin P.d → ℤ), ∀ t, (T X).Λ t) → ℕ := fun p =>
    (ncsX (leafCtr hS (fun s => (T p.1).n s (p.2 s))) p.1).ncard with hNc
  -- the mass of one mode
  set Bξ : (Σ X : CentredSlot π.Gsb → (Fin P.d → ℤ), ∀ t, (T X).Λ t) → ℝ := fun p =>
    (C0 * (Nc p : ℝ) * ∏ j, Mh p.1 p.2 j) * momS sel (routedFreq hS route (fun s => (T p.1).m s (p.2 s)))
    with hBξ
  have hBξ0 : ∀ p, 0 ≤ Bξ p := fun p =>
    mul_nonneg (mul_nonneg (mul_nonneg hC00 (Nat.cast_nonneg _)) (Finset.prod_nonneg fun j _ => hMh0 p.1 p.2 j))
      (momS_nonneg _ _)
  have hmode : ∀ p : (Σ X : CentredSlot π.Gsb → (Fin P.d → ℤ), ∀ t, (T X).Λ t), RepIntCMKS π sel tt base roots
      (outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
        (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0) *
          chiX P.L base p.1 z) hS
        (fixMeasure π.fix) (fun s => (T p.1).a s (p.2 s)) (fun s => (T p.1).m s (p.2 s)) route hclk hmom HkM)
      (Bξ p) := fun p =>
    repIntCMKS_modeX hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD hfilt hind
      (fun s => (T p.1).a s (p.2 s)) (fun s => (T p.1).n s (p.2 s)) (fun s k => (T p.1).a_one s _ k)
      (fun s => (T p.1).a_snorm s _) (fun q k hk => (T p.1).a_supp q _ k hk) (fun s => (T p.1).m s (p.2 s))
      route hroute hclk hmom HkM (H p.1 p.2) (Mh p.1 p.2) (hMh p.1 p.2) (hHk p.1 p.2) src src_dart src_root sel
      hselclk p.1
  -- the mode sum of the masses
  have hsumE : ∑' p : (Σ X : CentredSlot π.Gsb → (Fin P.d → ℤ), ∀ t, (T X).Λ t),
      ENNReal.ofReal (‖(((∏ s, (T p.1).w s (p.2 s) : ℝ)) : ℂ)‖ * Bξ p) ≤ ENNReal.ofReal Bi := by
    calc _ ≤ ∑' p : (Σ X : CentredSlot π.Gsb → (Fin P.d → ℤ), ∀ t, (T X).Λ t),
          ((Nc p : ℕ) : ℝ≥0∞) * ENNReal.ofReal (‖(((∏ s, (T p.1).w s (p.2 s) : ℝ)) : ℂ)‖ *
          ((C0 * Kh) * ∏ j, (1 + |((modLam (fun s => (T p.1).m s (p.2 s)) route j : ℤ) : ℝ)|) ^ c) *
          ∏ s, ∏ i', (1 + |((T p.1).m s (p.2 s) i' : ℝ)|) ^ selE route sel s i') := by
          refine ENNReal.tsum_le_tsum fun p => ?_
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hmo := momS_routed_le hS route sel hroute (fun s => (T p.1).m s (p.2 s))
          have hpm : 0 ≤ ∏ j, (1 + |((modLam (fun s => (T p.1).m s (p.2 s)) route j : ℤ) : ℝ)|) ^ c :=
            Finset.prod_nonneg fun j _ => by positivity
          have hMp : 0 ≤ ∏ j, Mh p.1 p.2 j := Finset.prod_nonneg fun j _ => hMh0 p.1 p.2 j
          have hN0 : (0 : ℝ) ≤ (Nc p : ℝ) := Nat.cast_nonneg _
          have h1 : C0 * (Nc p : ℝ) * ∏ j, Mh p.1 p.2 j ≤
              C0 * (Nc p : ℝ) * (Kh * ∏ j, (1 + |((modLam (fun s => (T p.1).m s (p.2 s)) route j : ℤ) : ℝ)|) ^ c) :=
            mul_le_mul_of_nonneg_left (hMhb p.1 p.2) (mul_nonneg hC00 hN0)
          have key : Bξ p ≤
              (C0 * (Nc p : ℝ) * (Kh * ∏ j, (1 + |((modLam (fun s => (T p.1).m s (p.2 s)) route j : ℤ) : ℝ)|) ^ c)) *
                ∏ s, ∏ i', (1 + |((T p.1).m s (p.2 s) i' : ℝ)|) ^ selE route sel s i' :=
            mul_le_mul h1 hmo (momS_nonneg _ _) (mul_nonneg (mul_nonneg hC00 hN0) (mul_nonneg hKh hpm))
          calc ‖(((∏ s, (T p.1).w s (p.2 s) : ℝ)) : ℂ)‖ * Bξ p
              ≤ ‖(((∏ s, (T p.1).w s (p.2 s) : ℝ)) : ℂ)‖ *
                ((C0 * (Nc p : ℝ) * (Kh * ∏ j, (1 + |((modLam (fun s => (T p.1).m s (p.2 s)) route j : ℤ) :
                  ℝ)|) ^ c)) * ∏ s, ∏ i', (1 + |((T p.1).m s (p.2 s) i' : ℝ)|) ^ selE route sel s i') :=
                mul_le_mul_of_nonneg_left key (norm_nonneg _)
            _ = _ := by ring
      _ ≤ ENNReal.ofReal (C0 * Kh) * ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ≥0∞) *
            ∏ s, (ENNReal.ofReal (9 * selF route sel s) * μs s) :=
          centre_modes_mass_le hS fam₀ famC route hc (selE route sel) (selE_nonneg route sel) θs hcθ
            (fun s => 9 * selF route sel s) (fun s => three_rpow_le_selF route sel s hc hc1) μs hμ (C0 * Kh)
            (mul_nonneg hC00 hKh)
      _ = ENNReal.ofReal (C0 * ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * Kh) *
            ∏ s, (ENNReal.ofReal (9 * selF route sel s) * μs s) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (mul_nonneg hC00 hKh)]
          congr 2
          ring
      _ ≤ _ := hBi'
  have hne : ∑' p : (Σ X : CentredSlot π.Gsb → (Fin P.d → ℤ), ∀ t, (T X).Λ t),
      ENNReal.ofReal (‖(((∏ s, (T p.1).w s (p.2 s) : ℝ)) : ℂ)‖ * Bξ p) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsumE
  have hs : Summable fun p : (Σ X : CentredSlot π.Gsb → (Fin P.d → ℤ), ∀ t, (T X).Λ t) =>
      ‖(((∏ s, (T p.1).w s (p.2 s) : ℝ)) : ℂ)‖ * Bξ p :=
    (ENNReal.summable_toReal hne).congr fun p =>
      ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg _) (hBξ0 p))
  obtain ⟨hsv, hr⟩ := RepIntCMKS.tsum hS hL0 hfilt hind
    (centreVal π hS tt base roots selSk Dom route hclk hmom fam₀ famC HkM) _ hs (fun p => (hmode p).smul _)
  refine ⟨hsv, ?_⟩
  rw [← hsv.tsum_sigma]
  refine hr.mono ?_
  have h1 : ENNReal.ofReal (∑' p : (Σ X : CentredSlot π.Gsb → (Fin P.d → ℤ), ∀ t, (T X).Λ t),
      ‖(((∏ s, (T p.1).w s (p.2 s) : ℝ)) : ℂ)‖ * Bξ p) =
      ∑' p : (Σ X : CentredSlot π.Gsb → (Fin P.d → ℤ), ∀ t, (T X).Λ t),
        ENNReal.ofReal (‖(((∏ s, (T p.1).w s (p.2 s) : ℝ)) : ℂ)‖ * Bξ p) :=
    ENNReal.ofReal_tsum_of_nonneg (fun p => mul_nonneg (norm_nonneg _) (hBξ0 p)) hs
  exact (ENNReal.ofReal_le_ofReal_iff hBi).1 (h1 ▸ hsumE)

end WaveTurbulence.Flower.MkSlotsE
