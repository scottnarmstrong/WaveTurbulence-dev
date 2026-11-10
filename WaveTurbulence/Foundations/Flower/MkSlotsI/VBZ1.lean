/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PVBRModes

/-! # B3s MK-SLOTS (final assembly, WP1): the pinned VINE-B♯ with a complex skeleton weight — glue

β's `MkSlotsB/PVBR3` + `PVBR4` with the selection indicator `if selSk κ then 1 else 0` of the skeleton summand
replaced by an arbitrary complex weight `Zs κ` that factors through the restriction to `G_sb`
(`Zs κ = Zw (Φ.resDec hS hd κ)`, `Zw` complex, `‖Zw‖ ≤ 1`). Everything that does not involve the selection is reused
from β by import (`modeGWD`, `psiIntGWD`, `GlueDomR`, `modeGWD_glue_ae`, `norm_integral_psiIntGWD_le_fix`,
`fiber_sumGWD_fix`, `outer_term_eqGWD_fix`, …).

* `skelTermWZ`, `skelValWZ`, **`skelValWZRL`** (relaxed core domain with lower bounds), `skelTermWZ_eq_integral`;
* the sanity bridges `skelTermWZ_ind`, `skelValWZ_ind`, **`skelValWZRL_ind`** (the indicator weight gives β's
  `skelTermWD`/`skelValWD`/`skelValWFRL`);
* `skelTerm_glueGWZ_fix`, `norm_skelTerm_glueGWZ_le_fix`, `tsum_skelTermGWZ_fix`, `outer_term_eqGWZ_fix`;
* **`skelVal_modal_eq_outerValMGWZ_fix`**: `skelValWZ (modalFnGW Fs amp frq) A fixS = outerValMμD … Dom … Zw …
  (fixMeasure fixSb) … (unitKernelMGW Fs)`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract

namespace WaveTurbulence.Flower.MkSlotsI
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB
open WaveTurbulence.Flower.MkSlots (fixMeasure measurePreserving_timeSplit_fix outerValMμD)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW RegBoundW topW unitIGW modalFnGW unitKernelMGW)
open WaveTurbulence.Flower.MkUnitsL.UnitGW (resDec_glueDecGW kBoundGW summable_kBoundGW summable_fib_kBoundGW
  const_splitGW)
open WaveTurbulence.Flower.MkSlotsB

/-! ## The skeleton value with a complex weight -/

section Skel

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J]

/-- The summand of the skeleton value on the core domain `A` with the complex skeleton weight `Zs` (β's
`MkSlotsB.skelTermWD` with `Zs κ * ·` in place of `if selSk κ then · else 0`). -/
def skelTermWZ (blk : J → CLBlock S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (Zs : GenDecoration S d roots 0 → ℂ) (Fs : SlotFamW S d)
    (A : Set (GBranch S.tree → ℝ)) (fixS : GBranch S.tree → Option ℝ) (κ : GenDecoration S d roots 0) : ℂ :=
  Zs κ * ((epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
      A.indicator (fun τ => phaseProd L γ δ S (cosetDecoration S L base κ.1) τ *
          ((∏ s, Fs.fs s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) *
            topW blk Fs L base κ.1)) τ ∂(fixMeasure fixS))

/-- The pinned skeleton value on the core domain `A` with the complex skeleton weight `Zs`. -/
def skelValWZ (blk : J → CLBlock S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (Zs : GenDecoration S d roots 0 → ℂ) (Fs : SlotFamW S d)
    (A : Set (GBranch S.tree → ℝ)) (fixS : GBranch S.tree → Option ℝ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
    ∑' κ : GenDecoration S d roots 0, skelTermWZ blk hS L γ δ base roots tt Zs Fs A fixS κ

/-- **The relaxed pinned skeleton value with lower bounds and a complex skeleton weight**: β's
`MkSlotsB.skelValWFRL` with the weight `Zs` in place of the selection; the core domain is
`coreTimeDomainWR … fixS ∩ lbDomR lbS`. -/
def skelValWZRL (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Fs : SlotFamW S d) (fixS lbS : GBranch S.tree → Option ℝ) : ℂ :=
  skelValWZ blk hS L γ δ base roots tt Zs Fs
    (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS) fixS

/-- The weighted summand is the weight times the integral of β's skeleton integrand `modeGWD`. -/
theorem skelTermWZ_eq_integral (blk : J → CLBlock S) (Fs : SlotFamW S d) (hS : S.IsPlain) (L γ δ : ℝ)
    (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (Zs : GenDecoration S d roots 0 → ℂ)
    (A : Set (GBranch S.tree → ℝ)) (fixS : GBranch S.tree → Option ℝ) (κ : GenDecoration S d roots 0) :
    skelTermWZ blk hS L γ δ base roots tt Zs Fs A fixS κ =
      Zs κ * ∫ τ, modeGWD blk Fs hS L γ δ base tt A κ τ ∂(fixMeasure fixS) := by
  unfold skelTermWZ modeGWD
  rw [integral_const_mul]

end Skel

/-! ## The pinned glue with a complex weight -/

section Glue

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)
variable {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

/-- **The pinned glued term with a complex weight** (cf. β's `MkSlotsB.skelTerm_glueGWD_fix`). -/
theorem skelTerm_glueGWZ_fix (hd : Disj blk) (hSb : Gsb.IsPlain) (hL : L ≠ 0)
    (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    skelTermWZ blk hS L γ δ base roots tt Zs (modalFnGW Φ hS hSb Fs amp frq) A fixS
        (Φ.glueDec hS hd hL base z κs) =
    Zw z * ∫ p, psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B p
      ∂((fixMeasure (fun c => fixS (Φ.br c))).prod (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := by
  rw [skelTermWZ_eq_integral, hZ, resDec_glueDecGW Φ hd hL base z κs]
  congr 1
  have hmp := measurePreserving_timeSplit_fix Φ hd fixS hU
  rw [← hmp.integral_comp' (psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B)]
  exact integral_congr_ae (modeGWD_glue_ae Φ hd hSb hL γ δ D layer tt amp frq fixS hG z κs)

/-- The glued term with a weight of norm `≤ 1` obeys β's bound. -/
theorem norm_skelTerm_glueGWZ_le_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ‖skelTermWZ blk hS L γ δ base roots tt Zs (modalFnGW Φ hS hSb Fs amp frq) A fixS
        (Φ.glueDec hS hd hL base z κs)‖ ≤
      ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) := by
  rw [skelTerm_glueGWZ_fix Φ hd hSb hL γ δ D layer tt amp frq Zs Zw hZ fixS hU hG z κs, norm_mul]
  calc _ ≤ 1 * _ := mul_le_mul (hZw z)
        (norm_integral_psiIntGWD_le_fix Φ RB hd D hSb γ δ layer tt amp frq z κs (fun c => fixS (Φ.br c))
          hG.meas hG.mass) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The decoration sum of the weighted skeleton terms, regrouped over `G_sb` decorations (cf. β's
`MkSlotsB.tsum_skelTermGWD_fix`). -/
theorem tsum_skelTermGWZ_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain) (hL : L ≠ 0)
    (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z)
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B) :
    ∑' κ : GenDecoration S d roots 0,
        skelTermWZ blk hS L γ δ base roots tt Zs (modalFnGW Φ hS hSb Fs amp frq) A fixS κ =
    ∑' z : GenDecoration Gsb d roots 0, Zw z *
      ∫ τ' : GBranch Gsb.tree → ℝ, (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
        B.indicator
          (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
            ∏ j, (Φ.recJ L γ δ base z τ' j *
              ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
                unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ)) τ' ∂(fixMeasure (fun c => fixS (Φ.br c))) := by
  have hglue : ∀ p : (Σ z : GenDecoration Gsb d roots 0,
      ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      skelTermWZ blk hS L γ δ base roots tt Zs (modalFnGW Φ hS hSb Fs amp frq) A fixS
        ((Φ.decSplit hS hd hL base roots).symm p) = Zw p.1 *
      ∫ q, psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq p.1 p.2 B q
        ∂((fixMeasure (fun c => fixS (Φ.br c))).prod
          (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) :=
    fun p => skelTerm_glueGWZ_fix Φ hd hSb hL γ δ D layer tt amp frq Zs Zw hZ fixS hU hG p.1 p.2
  have hnorm : ∀ p : (Σ z : GenDecoration Gsb d roots 0,
      ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      ‖skelTermWZ blk hS L γ δ base roots tt Zs (modalFnGW Φ hS hSb Fs amp frq) A fixS
        ((Φ.decSplit hS hd hL base roots).symm p)‖ ≤ kBoundGW Φ RB hSb amp p :=
    fun p => norm_skelTerm_glueGWZ_le_fix Φ RB hd hSb hL γ δ D layer tt amp frq Zs Zw hZw hZ fixS hU hG p.1 p.2
  have hFs : Summable fun p => skelTermWZ blk hS L γ δ base roots tt Zs
      (modalFnGW Φ hS hSb Fs amp frq) A fixS ((Φ.decSplit hS hd hL base roots).symm p) :=
    Summable.of_norm_bounded (summable_kBoundGW Φ RB hSb (roots := roots) amp hsum) hnorm
  have hfib : ∀ z : GenDecoration Gsb d roots 0,
      Summable fun κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
        skelTermWZ blk hS L γ δ base roots tt Zs (modalFnGW Φ hS hSb Fs amp frq) A fixS
          ((Φ.decSplit hS hd hL base roots).symm ⟨z, κs⟩) :=
    fun z => Summable.of_norm_bounded (summable_fib_kBoundGW Φ RB hSb amp z) fun κs => hnorm ⟨z, κs⟩
  have e2 := Summable.tsum_sigma' (f := fun p : (Σ z : GenDecoration Gsb d roots 0,
      ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      skelTermWZ blk hS L γ δ base roots tt Zs (modalFnGW Φ hS hSb Fs amp frq) A fixS
        ((Φ.decSplit hS hd hL base roots).symm p)) hfib hFs
  have e1 := (Φ.decSplit hS hd hL base roots).symm.tsum_eq (skelTermWZ blk hS L γ δ base roots tt Zs
      (modalFnGW Φ hS hSb Fs amp frq) A fixS)
  refine (e1.symm.trans e2).trans (tsum_congr fun z => ?_)
  have hz : ∀ κs, skelTermWZ blk hS L γ δ base roots tt Zs (modalFnGW Φ hS hSb Fs amp frq) A fixS
      ((Φ.decSplit hS hd hL base roots).symm ⟨z, κs⟩) = Zw z *
      ∫ q, psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B q
        ∂((fixMeasure (fun c => fixS (Φ.br c))).prod
          (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := fun κs => hglue ⟨z, κs⟩
  simp_rw [hz]
  rw [tsum_mul_left, fiber_sumGWD_fix Φ RB hd D hSb γ δ layer tt amp frq z (fun c => fixS (Φ.br c)) hG.meas
    hG.mass]

/-- The pinned outer term on a domain `Dom` agreeing a.e. with `B`, with a complex weight (β's
`MkSlotsB.outer_term_eqGWD_fix` at the weight `1`, multiplied by `Zw z`). -/
theorem outer_term_eqGWZ_fix (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (Fs : SlotFamW S d)
    (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (Zw : GenDecoration Gsb d roots 0 → ℂ) (fixSb : GBranch Gsb.tree → Option ℝ)
    (Dom B : Set (GBranch Gsb.tree → ℝ)) (hDB : ∀ᵐ τ' ∂(fixMeasure fixSb), τ' ∈ Dom ↔ τ' ∈ B)
    (z : GenDecoration Gsb d roots 0) :
    (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * Zw z *
      ∫ τ' : GBranch Gsb.tree → ℝ,
        Dom.indicator (fun τ' =>
          phaseProd L γ δ Gsb (cosetDecoration Gsb L base z.1) τ' *
            (∏ s, amp s (base + latticePoint L (z.1 (slotNode hSb s)))) *
              routedPhase frq (Φ.route hS hSb) tt τ' *
            ∏ j, unitKernelMGW blk D hS Fs L γ δ layer base j (modLam frq (Φ.route hS hSb) j)
              (fun c => clockOf Gsb tt τ' (Φ.hclk hd j c))
              (fun c => base + latticePoint L (z.1 (Φ.hmom hd j c)))) τ' ∂(fixMeasure fixSb) =
    (∏ j, unitConst (d := d) blk L γ δ j) * (Zw z * ∫ τ' : GBranch Gsb.tree → ℝ,
      (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
        B.indicator
          (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
            ∏ j, (Φ.recJ L γ δ base z τ' j *
              ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
                unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ)) τ' ∂(fixMeasure fixSb)) := by
  have h := outer_term_eqGWD_fix Φ hd D hS hSb L γ δ base Fs layer tt amp frq (fun _ => (1 : ℝ)) fixSb Dom B hDB z
  simp only [Complex.ofReal_one, mul_one, one_mul] at h
  linear_combination (Zw z) * h

/-- **The pinned per-mode single-state factorization with a complex weight** (cf. β's
`MkSlotsB.skelVal_modal_eq_outerValMGWD_fix`): unit interiors unpinned (`hU`), the domain split `hG`, and the outer
domain `Dom` a.e. equal to `B` (`hDB`); the outer decoration weight is `Zw`. -/
theorem skelVal_modal_eq_outerValMGWZ_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z)
    (fixS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    {A : Set (GBranch S.tree → ℝ)} {B : Set (GBranch Gsb.tree → ℝ)} (hG : GlueDomR Φ hd D hS layer fixS A B)
    (Dom : Set (GBranch Gsb.tree → ℝ))
    (hDB : ∀ᵐ τ' ∂(fixMeasure (fun c => fixS (Φ.br c))), τ' ∈ Dom ↔ τ' ∈ B) :
    skelValWZ blk hS L γ δ base roots tt Zs (modalFnGW Φ hS hSb Fs amp frq) A fixS =
    outerValMμD Gsb L γ δ base roots tt Dom (Φ.hinges hd) Zw hSb
      (fixMeasure (fun c => fixS (Φ.br c))) amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
      (unitKernelMGW blk D hS Fs L γ δ layer base) := by
  have hs := tsum_skelTermGWZ_fix Φ RB hd hSb hL γ δ D layer tt amp frq Zs Zw hZw hZ hsum fixS hU hG
  have hC := const_splitGW (d := d) Φ hd L γ δ
  rw [skelValWZ, hs, hC]
  unfold outerValMμD
  simp_rw [outer_term_eqGWZ_fix Φ hd D hS hSb L γ δ base Fs layer tt amp frq Zw (fun c => fixS (Φ.br c)) Dom B hDB]
  rw [tsum_mul_left]
  ring

end Glue

end WaveTurbulence.Flower.MkSlotsI
