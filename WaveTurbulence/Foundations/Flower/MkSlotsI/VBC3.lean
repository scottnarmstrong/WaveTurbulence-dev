/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.VBC2

/-! # B3s-HELPER7 (WP10): the centre-indexed relaxed pinned VINE-B♯

Setting of `hasSum_skelValWZRL_outerValMμD` (VBZ2); the outer slot superpositions are the centre-indexed data
`fam₀` (non-centred slots, at the consumed momenta `Cons`, `hcons`, `hexp₀`) and `famC c y` (centred slots, on the node
ball of `y`, `hexpC`), with a uniform mass bound `∑' l, (famC c y).w l ≤ MC` of the chain pieces (`hMC`, see VBC2:
without it the decoration sum need not converge absolutely and the statement fails in general).

* `hasSum_partition_tsum` (abstract: an absolutely summable series is the sum over a partition of unity);
* `hasSum_skelValWZRL_partition`: `skelValWZRL … Zs Fs … = Σ_X skelValWZRL … (Zs · chiX X ∘ resDec) Fs …`;
* **`hasSum_skelValWZRL_centred`** (main theorem): `HasSum (X ↦ Σ'_ξ modeWt · outerValMμD … (Zw · chiX X) …
  (famX fam₀ famC X modes) … (unitKernelMGW … Fs …)) (skelValWZRL … Zs Fs fixS lbS)`; the per-`X` ξ-sums are
  `hasSum_modes_centred` / `summable_modes_centred` (VBC1);
* `norm_modes_outer_le`, `summable_sigma_modeBound`;
* **`summable_sigma_centred`**: the absolute summability of the joint family over `Σ X, ∀ s, (famX … X).Λ s`;
* **`hasSum_sigma_centred`**: the joint family sums to `skelValWZRL … Zs Fs fixS lbS`. -/

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
  WaveTurbulence.VineB WaveTurbulence.RepAnalytic
open WaveTurbulence.Flower.MkSlots (fixMeasure outerValMμD)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW RegBoundW unitKernelMGW kerConstGW kerConstG_nonnegW)
open WaveTurbulence.Flower.MkSlotsB

variable {w d : ℕ}

/-! ## The partition of an absolutely summable series -/

/-- **An absolutely summable series is the sum of its parts over a partition of unity** `r X κ ≥ 0`,
`Σ_X r X κ = 1`. -/
theorem hasSum_partition_tsum {Ξ K : Type*} (r : Ξ → K → ℝ) (hr0 : ∀ X κ, 0 ≤ r X κ)
    (hr1 : ∀ κ, HasSum (fun X => r X κ) 1) (g : K → ℂ) (hg : Summable fun κ => ‖g κ‖) :
    HasSum (fun X => ∑' κ, (r X κ : ℂ) * g κ) (∑' κ, g κ) := by
  let F : K × Ξ → ℂ := fun p => (r p.2 p.1 : ℂ) * g p.1
  have hFn : Summable fun p => ‖F p‖ := by
    have e : (fun p => ‖F p‖) = fun p : K × Ξ => r p.2 p.1 * ‖g p.1‖ := by
      funext p
      show ‖(r p.2 p.1 : ℂ) * g p.1‖ = _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hr0 _ _)]
    rw [e]
    refine (summable_prod_of_nonneg (f := fun p : K × Ξ => r p.2 p.1 * ‖g p.1‖)
      fun p => mul_nonneg (hr0 _ _) (norm_nonneg _)).2 ⟨fun κ => ?_, hg.congr fun κ => ?_⟩
    · show Summable fun X => r X κ * ‖g κ‖
      exact (hr1 κ).summable.mul_right _
    · show ‖g κ‖ = ∑' X, r X κ * ‖g κ‖
      rw [tsum_mul_right, (hr1 κ).tsum_eq, one_mul]
  have hFs : Summable F := hFn.of_norm
  have H1 : HasSum g (∑' p, F p) := hFs.hasSum.prod_fiberwise fun κ => by
    have := (Complex.hasSum_ofReal.mpr (hr1 κ)).mul_right (g κ)
    rw [Complex.ofReal_one, one_mul] at this
    exact this
  have hG : Summable (F ∘ Equiv.prodComm Ξ K) := (Equiv.summable_iff _).mpr hFs
  have H2 := hG.hasSum.prod_fiberwise fun X => (hG.prod_factor X).hasSum
  have e3 : ∑' p, (F ∘ Equiv.prodComm Ξ K) p = ∑' κ, g κ :=
    ((Equiv.prodComm Ξ K).tsum_eq F).trans H1.tsum_eq.symm
  rw [e3] at H2
  exact H2

/-! ## The main theorem -/

section Main
variable {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb) {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

/-- **The partition over the centre assignments**: for an absolutely summable decoration sum,
`skelValWZRL … Zs Fs … = Σ_X skelValWZRL … (Zs · chiX X ∘ resDec) Fs …`. -/
theorem hasSum_skelValWZRL_partition (hd : Disj blk) (γ δ : ℝ) (D : ReconstructionData S)
    (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (fixS lbS : GBranch S.tree → Option ℝ)
    (hsum : Summable fun κ : GenDecoration S d roots 0 => ‖skelTermWZ blk hS L γ δ base roots tt Zs Fs
      (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS) fixS κ‖) :
    HasSum (fun X : CentredSlot Gsb → (Fin d → ℤ) =>
        skelValWZRL blk D hS L γ δ base roots tt layer (fun κ => Zs κ * chiX L base X (Φ.resDec hS hd κ)) Fs fixS
          lbS)
      (skelValWZRL blk D hS L γ δ base roots tt layer Zs Fs fixS lbS) := by
  have e : ∀ (X : CentredSlot Gsb → (Fin d → ℤ)) (κ : GenDecoration S d roots 0),
      skelTermWZ blk hS L γ δ base roots tt (fun κ => Zs κ * chiX L base X (Φ.resDec hS hd κ)) Fs
        (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS) fixS κ =
      (chiXR L base X (Φ.resDec hS hd κ) : ℂ) * skelTermWZ blk hS L γ δ base roots tt Zs Fs
        (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS) fixS κ := by
    intro X κ
    simp only [skelTermWZ, chiX_eq]
    ring
  have h := (hasSum_partition_tsum (fun (X : CentredSlot Gsb → (Fin d → ℤ)) κ => chiXR L base X (Φ.resDec hS hd κ))
    (fun X κ => chiXR_nonneg L base X _) (fun κ => hasSum_chiXR L base _) _ hsum).mul_left
    ((coupling d L γ δ : ℂ) ^ S.order * S.zeta)
  unfold skelValWZRL skelValWZ
  simp only [e]
  exact h

/-- The centre-indexed relaxed pinned VINE-B♯ under the agreement hypothesis (at every centre assignment). -/
theorem hasSum_skelValWZRL_centred_agree (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (MC : ℝ) (hMC : ∀ (c : CentredSlot Gsb) (y : Fin d → ℤ), ∑' l, (famC c y).w l ≤ MC)
    (fixS lbS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ →
      τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS →
        ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (hA : ∀ X, CentreAgree Φ hS hSb hd L base roots Fs fam₀ famC Box X) :
    HasSum (fun X : CentredSlot Gsb → (Fin d → ℤ) => ∑' ξ : ∀ s, (famX fam₀ famC X).Λ s,
      ((modeWt (famX fam₀ famC X) ξ : ℝ) : ℂ) *
        outerValMμD Gsb L γ δ base roots tt
          (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
            lbDomR (fun c => lbS (Φ.br c)))
          (Φ.hinges hd) (fun z => Zw z * chiX L base X z) hSb (fixMeasure (fun c => fixS (Φ.br c)))
          (fun s' => (famX fam₀ famC X).a s' (ξ s')) (fun s' => (famX fam₀ famC X).m s' (ξ s'))
          (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValWZRL blk D hS L γ δ base roots tt layer Zs Fs fixS lbS) := by
  have hpart := hasSum_skelValWZRL_partition Φ hd γ δ D layer tt Zs fixS lbS
    (summable_norm_skelTermWZ_centred_agree Φ RB hd hSb hL0 γ δ D layer tt Zs Zw hZw hZ fam₀ famC Box
      (le_max_right MC 0) (fun c y => (hMC c y).trans (le_max_left MC 0)) fixS lbS hU hlbU hP hbox hA)
  refine hpart.congr_fun fun X => ?_
  exact (hasSum_modes_centred_agree Φ RB hd hSb hL0 γ δ D layer tt Zs Zw hZw hZ fam₀ famC Box fixS lbS hU hlbU hP
    hbox X (hA X)).tsum_eq

/-- **The centre-indexed relaxed pinned VINE-B♯** (WP10). Setting of `hasSum_skelValWZRL_outerValMμD` (VBZ2), with the
outer slot superpositions given by `fam₀` on the non-centred slots at the consumed momenta (`hcons`, `hexp₀`) and by
the centre-indexed chain pieces `famC c y` on the centred slots on the node ball of `y` (`hexpC`), and a uniform mass
bound `MC` of the chain pieces (`hMC`): the relaxed pinned skeleton value is the sum over the centre assignments `X`
of the mode sums of the pinned outer values of `G_sb` with the slot family `famX fam₀ famC X`, the decoration weight
`Zw · chiX X`, and the ORIGINAL unit kernels `unitKernelMGW … Fs …`. -/
theorem hasSum_skelValWZRL_centred (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ)) (Cons : ReplacementSlot Gsb → Mom d → Prop)
    (hcons : ∀ κ : GenDecoration S d roots 0, ∀ s', ¬ IsCentred s' →
      Cons s' (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb s')))))
    (hexp₀ : ∀ s', ¬ IsCentred s' → ∀ ts ∈ Box s', ∀ x, Cons s' x →
      HasSum (fun l => (fam₀.w s' l : ℂ) * fam₀.a s' l x * fsPhase (fam₀.m s' l) ts) (Fs.fs (Φ.iota hS hSb s') ts x))
    (hexpC : ∀ (c : CentredSlot Gsb) (y : Fin d → ℤ), ∀ ts ∈ Box (.inr c.1), ∀ x, ‖x - latPt d y‖ ≤ 1 →
      HasSum (fun l => ((famC c y).w l : ℂ) * (famC c y).a l x * fsPhase ((famC c y).m l) ts)
        (Fs.fs (Φ.iota hS hSb (.inr c.1)) ts x))
    (MC : ℝ) (hMC : ∀ (c : CentredSlot Gsb) (y : Fin d → ℤ), ∑' l, (famC c y).w l ≤ MC)
    (fixS lbS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ →
      τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS →
        ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun X : CentredSlot Gsb → (Fin d → ℤ) => ∑' ξ : ∀ s, (famX fam₀ famC X).Λ s,
      ((modeWt (famX fam₀ famC X) ξ : ℝ) : ℂ) *
        outerValMμD Gsb L γ δ base roots tt
          (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
            lbDomR (fun c => lbS (Φ.br c)))
          (Φ.hinges hd) (fun z => Zw z * chiX L base X z) hSb (fixMeasure (fun c => fixS (Φ.br c)))
          (fun s' => (famX fam₀ famC X).a s' (ξ s')) (fun s' => (famX fam₀ famC X).m s' (ξ s'))
          (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValWZRL blk D hS L γ δ base roots tt layer Zs Fs fixS lbS) :=
  hasSum_skelValWZRL_centred_agree Φ RB hd hSb hL0 γ δ D layer tt Zs Zw hZw hZ fam₀ famC Box MC hMC fixS lbS hU hlbU
    hP hbox (centreAgree_of Φ hd hSb fam₀ famC Box Cons hcons hexp₀ hexpC)

end Main

/-! ## The joint family over centre assignments and modes -/

section ModeSum
variable {G : Garden w}

/-- The joint majorant `modeWt · Σ_z chiX X z · ampBound` is summable over `Σ X, modes of famX X`. -/
theorem summable_sigma_modeBound (hG : G.IsPlain) {L : ℝ} (hL0 : 0 < L) (base : Mom d) (roots : Fin w → Fin d → ℤ)
    (fam₀ : SlotFam G d) (famC : CentredSlot G → (Fin d → ℤ) → ChainPiece d) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ c y, ∑' l, (famC c y).w l ≤ M) :
    Summable (fun p : (Σ X : CentredSlot G → (Fin d → ℤ), ∀ s, (famX fam₀ famC X).Λ s) =>
      modeWt (famX fam₀ famC p.1) p.2 * ∑' z : GenDecoration G d roots 0,
        chiXR L base p.1 z * ampBound hG L base (fun s' => (famX fam₀ famC p.1).a s' (p.2 s')) z) := by
  have hQ := summable_ampBound_ampQ fam₀ hG hL0 base roots hM0
  have hQ0 : ∀ z : GenDecoration G d roots 0, 0 ≤ ampBound hG L base (ampQ fam₀ M) z :=
    fun z => ampBound_nonneg _ _ _ _ _
  -- the fibre over a centre assignment
  have hfib : ∀ X : CentredSlot G → (Fin d → ℤ),
      Summable (fun ξ : ∀ s, (famX fam₀ famC X).Λ s => modeWt (famX fam₀ famC X) ξ *
        ∑' z : GenDecoration G d roots 0,
          chiXR L base X z * ampBound hG L base (fun s' => (famX fam₀ famC X).a s' (ξ s')) z) ∧
      ∑' ξ : ∀ s, (famX fam₀ famC X).Λ s, modeWt (famX fam₀ famC X) ξ * ∑' z : GenDecoration G d roots 0,
          chiXR L base X z * ampBound hG L base (fun s' => (famX fam₀ famC X).a s' (ξ s')) z ≤
        ∑' z : GenDecoration G d roots 0, chiXR L base X z * ampBound hG L base (ampQ fam₀ M) z := by
    intro X
    have hA := fun ξ : ∀ s, (famX fam₀ famC X).Λ s => tsum_ampBound_mode_le (famX fam₀ famC X) hG L hL0 base roots ξ
    have hwt : Summable (modeWt (famX fam₀ famC X)) :=
      (hasSum_prod_real (fun s l => (famX fam₀ famC X).w s l) (fun s l => (famX fam₀ famC X).w_nn s l)
        (fun s => (famX fam₀ famC X).w_sum s)).summable
    set C₀ : ℝ := ((((⌊2 * L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair G) : ℕ) : ℝ)
    let f : (∀ s, (famX fam₀ famC X).Λ s) → GenDecoration G d roots 0 → ℝ := fun ξ z =>
      modeWt (famX fam₀ famC X) ξ * (chiXR L base X z * ampBound hG L base (fun s' => (famX fam₀ famC X).a s' (ξ s')) z)
    have hf0 : ∀ ξ z, 0 ≤ f ξ z := fun ξ z => mul_nonneg (modeWt_nonneg _ ξ)
      (mul_nonneg (chiXR_nonneg L base X z) (ampBound_nonneg _ _ _ _ _))
    have hfle : ∀ ξ z, f ξ z ≤ modeWt (famX fam₀ famC X) ξ *
        ampBound hG L base (fun s' => (famX fam₀ famC X).a s' (ξ s')) z := fun ξ z =>
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (ampBound_nonneg _ _ _ _ _) (chiXR_le_one L base X z))
        (modeWt_nonneg _ ξ)
    have h1 : ∀ ξ, Summable (f ξ) := fun ξ =>
      Summable.of_nonneg_of_le (hf0 ξ) (hfle ξ) ((hA ξ).1.mul_left _)
    have h1le : ∀ ξ, ∑' z, f ξ z ≤ modeWt (famX fam₀ famC X) ξ * C₀ := fun ξ => by
      refine (Summable.tsum_le_tsum (hfle ξ) (h1 ξ) ((hA ξ).1.mul_left _)).trans ?_
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (hA ξ).2 (modeWt_nonneg _ ξ)
    have hsξ : Summable fun ξ => ∑' z, f ξ z :=
      Summable.of_nonneg_of_le (fun ξ => tsum_nonneg (hf0 ξ)) h1le (hwt.mul_right C₀)
    have huc : Summable (Function.uncurry f) :=
      (summable_prod_of_nonneg (f := Function.uncurry f) fun p => hf0 p.1 p.2).2 ⟨h1, hsξ⟩
    have h2 : ∀ z, HasSum (fun ξ => f ξ z) (chiXR L base X z * ∏ s, ∑' l, (famX fam₀ famC X).w s l *
        ‖(famX fam₀ famC X).a s l (base + latticePoint L (z.1 (slotNode hG s)))‖) := fun z => by
      have := (hasSum_modeWt_ampBound_famX fam₀ famC X hG L base z).mul_left (chiXR L base X z)
      refine this.congr_fun fun ξ => ?_
      show modeWt (famX fam₀ famC X) ξ * (chiXR L base X z *
        ampBound hG L base (fun s' => (famX fam₀ famC X).a s' (ξ s')) z) = _
      ring
    have hle2 : ∀ z, ∑' ξ, f ξ z ≤ chiXR L base X z * ampBound hG L base (ampQ fam₀ M) z := fun z => by
      rw [(h2 z).tsum_eq]
      exact mul_le_mul_of_nonneg_left (prod_famX_le_ampQ fam₀ famC X hG L base hM0 hM z) (chiXR_nonneg L base X z)
    have hR : Summable fun z => chiXR L base X z * ampBound hG L base (ampQ fam₀ M) z :=
      Summable.of_nonneg_of_le (fun z => mul_nonneg (chiXR_nonneg L base X z) (hQ0 z))
        (fun z => mul_le_of_le_one_left (hQ0 z) (chiXR_le_one L base X z)) hQ
    have hcomm := huc.tsum_comm' h1 (fun z => (h2 z).summable)
    refine ⟨hsξ.congr fun ξ => ?_, ?_⟩
    · show ∑' z, f ξ z = _
      rw [tsum_mul_left]
    · have e : ∀ ξ : ∀ s, (famX fam₀ famC X).Λ s, modeWt (famX fam₀ famC X) ξ * ∑' z : GenDecoration G d roots 0,
          chiXR L base X z * ampBound hG L base (fun s' => (famX fam₀ famC X).a s' (ξ s')) z = ∑' z, f ξ z :=
        fun ξ => by rw [tsum_mul_left]
      simp only [e]
      rw [← hcomm]
      exact Summable.tsum_le_tsum hle2
        (Summable.of_nonneg_of_le (fun z => tsum_nonneg fun ξ => hf0 ξ z) hle2 hR) hR
  -- the sum over the centre assignments
  have hXs : Summable fun X : CentredSlot G → (Fin d → ℤ) =>
      ∑' z : GenDecoration G d roots 0, chiXR L base X z * ampBound hG L base (ampQ fam₀ M) z := by
    let g : GenDecoration G d roots 0 × (CentredSlot G → (Fin d → ℤ)) → ℝ := fun p =>
      chiXR L base p.2 p.1 * ampBound hG L base (ampQ fam₀ M) p.1
    have hg0 : 0 ≤ g := fun p => mul_nonneg (chiXR_nonneg L base p.2 p.1) (hQ0 p.1)
    have hgs : Summable g := by
      refine (summable_prod_of_nonneg hg0).2 ⟨fun z => ?_, hQ.congr fun z => ?_⟩
      · show Summable fun X => chiXR L base X z * ampBound hG L base (ampQ fam₀ M) z
        exact (hasSum_chiXR L base z).summable.mul_right _
      · show ampBound hG L base (ampQ fam₀ M) z = ∑' X, chiXR L base X z * ampBound hG L base (ampQ fam₀ M) z
        rw [tsum_mul_right, (hasSum_chiXR L base z).tsum_eq, one_mul]
    have hgs' : Summable (g ∘ Equiv.prodComm _ _) := (Equiv.summable_iff _).mpr hgs
    exact ((summable_prod_of_nonneg (f := g ∘ Equiv.prodComm _ _) fun p => hg0 _).1 hgs').2
  refine (summable_sigma_of_nonneg fun p => ?_).2 ⟨fun X => (hfib X).1, Summable.of_nonneg_of_le (fun X =>
    tsum_nonneg fun ξ => mul_nonneg (modeWt_nonneg _ ξ) (tsum_nonneg fun z => mul_nonneg (chiXR_nonneg L base X z)
      (ampBound_nonneg _ _ _ _ _))) (fun X => (hfib X).2) hXs⟩
  exact mul_nonneg (modeWt_nonneg _ p.2)
    (tsum_nonneg fun z => mul_nonneg (chiXR_nonneg L base p.1 z) (ampBound_nonneg _ _ _ _ _))

end ModeSum

section Sigma
variable {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb) {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

/-- The norm of a per-mode outer value at the weight `Zw · chiX X` against the decoration majorant. -/
theorem norm_modes_outer_le (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (hL0 : 0 < L) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (fixS lbS : GBranch S.tree → Option ℝ) (X : CentredSlot Gsb → (Fin d → ℤ))
    (ξ : ∀ s, (famX fam₀ famC X).Λ s) :
    ‖((modeWt (famX fam₀ famC X) ξ : ℝ) : ℂ) *
        outerValMμD Gsb L γ δ base roots tt
          (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
            lbDomR (fun c => lbS (Φ.br c)))
          (Φ.hinges hd) (fun z => Zw z * chiX L base X z) hSb (fixMeasure (fun c => fixS (Φ.br c)))
          (fun s' => (famX fam₀ famC X).a s' (ξ s')) (fun s' => (famX fam₀ famC X).m s' (ξ s'))
          (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base)‖ ≤
      ‖(coupling d L γ δ : ℂ) ^ Gsb.order * Gsb.zeta‖ * kerConstGW blk RB γ δ *
        (modeWt (famX fam₀ famC X) ξ * ∑' z : GenDecoration Gsb d roots 0,
          chiXR L base X z * ampBound hSb L base (fun s' => (famX fam₀ famC X).a s' (ξ s')) z) := by
  have hDom := measurableSet_splicedTimeDomainFix_lb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
    (fun c => fixS (Φ.br c)) (fun c => lbS (Φ.br c))
  have hμ := fixMeasure_splicedTimeDomainFix_lb_le Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
    (fun c => fixS (Φ.br c)) (fun c => lbS (Φ.br c))
  have hK0 := kerConstG_nonnegW RB γ δ (fun _ => base)
  have hw0 := modeWt_nonneg (famX fam₀ famC X) ξ
  have hterm : ∀ z : GenDecoration Gsb d roots 0, ‖(splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
      (Zw z * chiX L base X z) * ∫ τ, outerIntegrandMD Gsb L γ δ base roots tt
        (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
          lbDomR (fun c => lbS (Φ.br c))) hSb
        (fun s' => (famX fam₀ famC X).a s' (ξ s')) (fun s' => (famX fam₀ famC X).m s' (ξ s'))
        (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base) z τ
          ∂(fixMeasure (fun c => fixS (Φ.br c)))‖ ≤
      chiXR L base X z * ampBound hSb L base (fun s' => (famX fam₀ famC X).a s' (ξ s')) z *
        kerConstGW blk RB γ δ := by
    intro z
    have hint := integral_norm_outerIntegrandMDGW_le Φ RB hd D hSb γ δ layer tt
      (fun s' => (famX fam₀ famC X).a s' (ξ s')) (fun s' => (famX fam₀ famC X).m s' (ξ s')) z hDom _ hμ
    have he : ‖(splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_splicedEpsilon_le _ _ _
    have hw : ‖Zw z * chiX L base X z‖ ≤ chiXR L base X z := by
      rw [norm_mul, norm_chiX]
      exact mul_le_of_le_one_left (chiXR_nonneg L base X z) (hZw z)
    have hc0 := chiXR_nonneg L base X z
    rw [norm_mul, norm_mul]
    calc _ ≤ 1 * chiXR L base X z * ∫ τ, ‖outerIntegrandMD Gsb L γ δ base roots tt
          (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
            (fun c => fixS (Φ.br c)) ∩ lbDomR (fun c => lbS (Φ.br c))) hSb
          (fun s' => (famX fam₀ famC X).a s' (ξ s')) (fun s' => (famX fam₀ famC X).m s' (ξ s'))
          (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base) z τ‖
            ∂(fixMeasure (fun c => fixS (Φ.br c))) :=
          mul_le_mul (mul_le_mul he hw (norm_nonneg _) zero_le_one) (norm_integral_le_integral_norm _)
            (norm_nonneg _) (mul_nonneg zero_le_one hc0)
      _ ≤ 1 * chiXR L base X z * (ampBound hSb L base (fun s' => (famX fam₀ famC X).a s' (ξ s')) z *
            kerConstGW blk RB γ δ) := mul_le_mul_of_nonneg_left hint (mul_nonneg zero_le_one hc0)
      _ = _ := by ring
  have hA := (tsum_ampBound_mode_le (famX fam₀ famC X) hSb L hL0 base roots ξ).1
  have hsumB : Summable fun z : GenDecoration Gsb d roots 0 => chiXR L base X z *
      ampBound hSb L base (fun s' => (famX fam₀ famC X).a s' (ξ s')) z * kerConstGW blk RB γ δ :=
    Summable.of_nonneg_of_le (fun z => mul_nonneg (mul_nonneg (chiXR_nonneg L base X z) (ampBound_nonneg _ _ _ _ _))
      hK0) (fun z => mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (ampBound_nonneg _ _ _ _ _)
        (chiXR_le_one L base X z)) hK0) (hA.mul_right _)
  have h3 := tsum_of_norm_bounded hsumB.hasSum hterm
  rw [outerValMμD_eq_outerIntegrandMD, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
  calc _ ≤ modeWt (famX fam₀ famC X) ξ * (‖(coupling d L γ δ : ℂ) ^ Gsb.order * Gsb.zeta‖ *
        ∑' z : GenDecoration Gsb d roots 0, chiXR L base X z *
          ampBound hSb L base (fun s' => (famX fam₀ famC X).a s' (ξ s')) z * kerConstGW blk RB γ δ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) hw0
    _ = _ := by
        rw [tsum_mul_right]
        ring

/-- **Absolute summability of the joint family** over the centre assignments and the modes of `famX fam₀ famC X`
(only the regional bound, `‖Zw‖ ≤ 1` and the uniform chain-piece mass bound `hMC` are needed). -/
theorem summable_sigma_centred (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (hL0 : 0 < L) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (MC : ℝ) (hMC : ∀ (c : CentredSlot Gsb) (y : Fin d → ℤ), ∑' l, (famC c y).w l ≤ MC)
    (fixS lbS : GBranch S.tree → Option ℝ) :
    Summable (fun p : (Σ X : CentredSlot Gsb → (Fin d → ℤ), ∀ s, (famX fam₀ famC X).Λ s) =>
      ‖((modeWt (famX fam₀ famC p.1) p.2 : ℝ) : ℂ) *
        outerValMμD Gsb L γ δ base roots tt
          (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
            lbDomR (fun c => lbS (Φ.br c)))
          (Φ.hinges hd) (fun z => Zw z * chiX L base p.1 z) hSb (fixMeasure (fun c => fixS (Φ.br c)))
          (fun s' => (famX fam₀ famC p.1).a s' (p.2 s')) (fun s' => (famX fam₀ famC p.1).m s' (p.2 s'))
          (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => norm_modes_outer_le Φ RB hd D hSb hL0 γ δ layer tt Zw hZw fam₀ famC fixS lbS p.1 p.2)
    ((summable_sigma_modeBound hSb hL0 base roots fam₀ famC (le_max_right MC 0)
      (fun c y => (hMC c y).trans (le_max_left MC 0))).mul_left _)

/-- The joint family under the agreement hypothesis (at every centre assignment). -/
theorem hasSum_sigma_centred_agree (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (MC : ℝ) (hMC : ∀ (c : CentredSlot Gsb) (y : Fin d → ℤ), ∑' l, (famC c y).w l ≤ MC)
    (fixS lbS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ →
      τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS →
        ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s')
    (hA : ∀ X, CentreAgree Φ hS hSb hd L base roots Fs fam₀ famC Box X) :
    HasSum (fun p : (Σ X : CentredSlot Gsb → (Fin d → ℤ), ∀ s, (famX fam₀ famC X).Λ s) =>
      ((modeWt (famX fam₀ famC p.1) p.2 : ℝ) : ℂ) *
        outerValMμD Gsb L γ δ base roots tt
          (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
            lbDomR (fun c => lbS (Φ.br c)))
          (Φ.hinges hd) (fun z => Zw z * chiX L base p.1 z) hSb (fixMeasure (fun c => fixS (Φ.br c)))
          (fun s' => (famX fam₀ famC p.1).a s' (p.2 s')) (fun s' => (famX fam₀ famC p.1).m s' (p.2 s'))
          (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValWZRL blk D hS L γ δ base roots tt layer Zs Fs fixS lbS) := by
  have hs := (summable_sigma_centred Φ RB hd D hSb hL0 γ δ layer tt Zw hZw fam₀ famC MC hMC fixS lbS).of_norm
  have h1 := hs.hasSum.sigma fun X => hasSum_modes_centred_agree Φ RB hd hSb hL0 γ δ D layer tt Zs Zw hZw hZ fam₀
    famC Box fixS lbS hU hlbU hP hbox X (hA X)
  have h2 := hasSum_skelValWZRL_centred_agree Φ RB hd hSb hL0 γ δ D layer tt Zs Zw hZw hZ fam₀ famC Box MC hMC fixS
    lbS hU hlbU hP hbox hA
  have h3 := h2.congr_fun fun X => (hasSum_modes_centred_agree Φ RB hd hSb hL0 γ δ D layer tt Zs Zw hZw hZ fam₀ famC
    Box fixS lbS hU hlbU hP hbox X (hA X)).tsum_eq.symm
  rw [← h1.unique h3]
  exact hs.hasSum

/-- **The joint family sums to the relaxed pinned skeleton value** (corollary of `summable_sigma_centred`,
`hasSum_modes_centred` and `hasSum_skelValWZRL_centred`). -/
theorem hasSum_sigma_centred (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL0 : 0 < L) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (Zs : GenDecoration S d roots 0 → ℂ) (Zw : GenDecoration Gsb d roots 0 → ℂ) (hZw : ∀ z, ‖Zw z‖ ≤ 1)
    (hZ : ∀ κ : GenDecoration S d roots 0, Zs κ = Zw (Φ.resDec hS hd κ))
    (fam₀ : SlotFam Gsb d) (famC : CentredSlot Gsb → (Fin d → ℤ) → ChainPiece d)
    (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ)) (Cons : ReplacementSlot Gsb → Mom d → Prop)
    (hcons : ∀ κ : GenDecoration S d roots 0, ∀ s', ¬ IsCentred s' →
      Cons s' (base + latticePoint L (κ.1 (slotNode hS (Φ.iota hS hSb s')))))
    (hexp₀ : ∀ s', ¬ IsCentred s' → ∀ ts ∈ Box s', ∀ x, Cons s' x →
      HasSum (fun l => (fam₀.w s' l : ℂ) * fam₀.a s' l x * fsPhase (fam₀.m s' l) ts) (Fs.fs (Φ.iota hS hSb s') ts x))
    (hexpC : ∀ (c : CentredSlot Gsb) (y : Fin d → ℤ), ∀ ts ∈ Box (.inr c.1), ∀ x, ‖x - latPt d y‖ ≤ 1 →
      HasSum (fun l => ((famC c y).w l : ℂ) * (famC c y).a l x * fsPhase ((famC c y).m l) ts)
        (Fs.fs (Φ.iota hS hSb (.inr c.1)) ts x))
    (MC : ℝ) (hMC : ∀ (c : CentredSlot Gsb) (y : Fin d → ℤ), ∑' l, (famC c y).w l ≤ MC)
    (fixS lbS : GBranch S.tree → Option ℝ) (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none)
    (hlbU : ∀ j, ∀ a ∈ inter blk j, lbS a = none)
    (hP : RelaxPinsS (fun b => layer (D.coreBranch hS b).toNode) tt fixS)
    (hbox : ∀ τ, PinnedAt fixS τ →
      τ ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt fixS ∩ lbDomR lbS →
        ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun p : (Σ X : CentredSlot Gsb → (Fin d → ℤ), ∀ s, (famX fam₀ famC X).Λ s) =>
      ((modeWt (famX fam₀ famC p.1) p.2 : ℝ) : ℂ) *
        outerValMμD Gsb L γ δ base roots tt
          (splicedTimeDomainFix Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt (fun c => fixS (Φ.br c)) ∩
            lbDomR (fun c => lbS (Φ.br c)))
          (Φ.hinges hd) (fun z => Zw z * chiX L base p.1 z) hSb (fixMeasure (fun c => fixS (Φ.br c)))
          (fun s' => (famX fam₀ famC p.1).a s' (p.2 s')) (fun s' => (famX fam₀ famC p.1).m s' (p.2 s'))
          (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base))
      (skelValWZRL blk D hS L γ δ base roots tt layer Zs Fs fixS lbS) :=
  hasSum_sigma_centred_agree Φ RB hd hSb hL0 γ δ D layer tt Zs Zw hZw hZ fam₀ famC Box MC hMC fixS lbS hU hlbU hP hbox
    (centreAgree_of Φ hd hSb fam₀ famC Box Cons hcons hexp₀ hexpC)

end Sigma

end WaveTurbulence.Flower.MkSlotsI
