/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnitsL.GenW3
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB8

/-! # MK-UNITS-L (B3-2), generic VINE-B♯ with per-unit top weights: the mode expansion of the outer slots for an arbitrary slot family

Copy-generalization of `Represents/RepVB2–RepVB8` (VINE-B♯ integration) from `slotFn` to an arbitrary slot family
`Fs`: if the outer slots of `Fs` have superpositions `Σ_l w_l a_l(k) e^{πi m_l·ts}` on boxes containing the slot
times of the core domain, then `skelVal(Fs) = Σ'_ξ w_ξ · outerValM(amp ξ, frq ξ, …, unitKernelMGW Fs)`
(`hasSum_skelVal_outerValMGW`).

Stage1WVine's `GenModes` with the slot family `Fs` a `SlotFamW` (slot kernels and per-unit top weights, `GenW1`); the
proofs are verbatim, every declaration renamed with the suffix `W`.  Adapted from `Flower/Stage1WVine/GenModes.lean`
(see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnitsL
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.RepAnalytic WaveTurbulence.Flower.MkUnitsL.UnitGW

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)

theorem hasSum_modal_prodGW (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (Fs : SlotFamW S d) (fam : SlotFam Gsb d) (tt : Fin w → ℝ)
    (τ : GBranch S.tree → ℝ) (k : GNode S.tree → Mom d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x *
      fsPhase (fam.m s' l) ts) (Fs.fs (Φ.iota hS hSb s') ts x))
    (hbox : ∀ s', slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      ∏ s, (modalFnGW Φ hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))).fs s
        (slotTs hS tt τ s) (k (slotNode hS s)))
      (∏ s, Fs.fs s (slotTs hS tt τ s) (k (slotNode hS s))) := by
  have hmain := hasSum_outer_modes fam (fun s' => slotTs hS tt τ (Φ.iota hS hSb s'))
    (fun s' => k (slotNode hS (Φ.iota hS hSb s')))
    (fun s' => Fs.fs (Φ.iota hS hSb s') (slotTs hS tt τ (Φ.iota hS hSb s')) (k (slotNode hS (Φ.iota hS hSb s'))))
    (fun s' => hexp s' _ (hbox s') _)
  set R : ℂ := ∏ j, ∏ s ∈ regSlots blk hS j, Fs.fs s (slotTs hS tt τ s) (k (slotNode hS s)) with hR
  have h1 := hmain.mul_right R
  have e2 : ∏ s, Fs.fs s (slotTs hS tt τ s) (k (slotNode hS s)) =
      (∏ s', Fs.fs (Φ.iota hS hSb s') (slotTs hS tt τ (Φ.iota hS hSb s')) (k (slotNode hS (Φ.iota hS hSb s')))) * R := by
    rw [prod_slots hS hd (fun s => Fs.fs s (slotTs hS tt τ s) (k (slotNode hS s))),
      Φ.prod_outer_iota hS hSb (fun s => Fs.fs s (slotTs hS tt τ s) (k (slotNode hS s)))]
  rw [e2]
  refine h1.congr_fun fun ξ => ?_
  rw [prod_modalFnGW Φ hd hS hSb Fs (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s')) tt τ k]
  ring

variable {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

theorem tsum_kBoundG_leW (RB : RegBoundW blk hS Fs L base) (hSb : Gsb.IsPlain) {roots : Fin w → (Fin d → ℤ)}
    (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (hsm : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z) (N : ℝ)
    (hN : ∑' z : GenDecoration Gsb d roots 0, ampBound hSb L base amp z ≤ N) :
    ∑' p, kBoundGW Φ RB hSb (roots := roots) amp p ≤ N * ∏ j, RB.lbC j := by
  have hkbs := summable_kBoundGW Φ RB hSb (roots := roots) amp hsm
  have hfib := fun z => summable_fib_kBoundGW Φ RB hSb (roots := roots) amp z
  have hΛ0 : 0 ≤ ∏ j, RB.lbC j := Finset.prod_nonneg fun j _ => lbC_nonnegW RB j 0
  rw [hkbs.tsum_sigma' hfib]
  calc _ ≤ ∑' z : GenDecoration Gsb d roots 0, ampBound hSb L base amp z * ∏ j, RB.lbC j :=
        Summable.tsum_le_tsum (fun z => tsum_fib_kBoundG_leW Φ RB hSb amp z) hkbs.sigma (hsm.mul_right _)
    _ = (∑' z, ampBound hSb L base amp z) * ∏ j, RB.lbC j := tsum_mul_right
    _ ≤ N * _ := mul_le_mul_of_nonneg_right hN hΛ0

end WaveTurbulence.Flower.MkUnitsL
