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

end Main

/-! ## The joint family over centre assignments and modes -/

section ModeSum
variable {G : Garden w}

end ModeSum

section Sigma
variable {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb) {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

end Sigma

end WaveTurbulence.Flower.MkSlotsI
