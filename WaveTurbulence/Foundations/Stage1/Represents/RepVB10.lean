/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB9
public import WaveTurbulence.Foundations.Stage1.Represents.RepGateA
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: the value of a member garden as a mode series (engine form)

`valueSel_modes`: for a member garden `layeredReconstruction D hS layer hLayer` of a prime skeleton `S` with a splice shape `Φ`
onto `G_sb`, the family value `U.toLF.valueSel` is `Σ_i sign_i Σ'_ξ w_ξ · outerValM(…, unitKernelM)`: the per-member
hypothesis `hV` of VINE-C's `sum_tauClass_vineD_api` and the `hval` shape of `representsIntA_of_vineModes`
(up to VINE-C's `unitKernelM = unitRecenteredW` identification).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineB
  WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineEstS4 WaveTurbulence.RegRedLeaf
  WaveTurbulence.VineEstS3.FS

open scoped Classical in
theorem valueSel_modes {P : WTParams} {R : ℕ} (U : TypeFamily P (2 * R)) {S : Garden (2 * R)} {J : Type}
    [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden (2 * R)} (Φ : SpliceShape blk Gsb)
    (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (hctrl : U.toLF.Controlled (layeredReconstruction D hS layer hLayer)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration S P.d roots 0 → Prop) (Zw : GenDecoration Gsb P.d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S P.d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (hF : ∀ i j, HF D hS P.L (unitProfile blk (U.h i) j) layer base)
    (fam : U.ι → SlotFam Gsb P.d) (Box : U.ι → ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ i s', ∀ ts ∈ Box i s', ∀ x, HasSum
      (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
      (slotFn D hS P.L P.γ P.δ (typeProfiles (layeredReconstruction D hS layer hLayer) (U.h i)) layer hLayer
        (Φ.iota hS hSb s') ts x))
    (hbox : ∀ i, ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box i s') :
    U.toLF.valueSel tt base roots (layeredReconstruction D hS layer hLayer)
        (fun κ => selSk (collapseGenDecoration D hS κ)) =
      @Finset.sum U.ι ℂ _ (@Finset.univ _ U.fin) fun i =>
        ((U.sign i : ℝ) : ℂ) * ∑' ξ : (∀ s, (fam i).Λ s), ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM Gsb P.L P.γ P.δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
            (Φ.hinges hd) Zw hSb (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelM blk D hS P.L P.γ P.δ (U.h i) layer hLayer base) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  rw [LeafFamily.valueSel_skeleton_reduction U.toLF D hS layer hLayer hctrl hd1 hL1 tt base roots selSk]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have := (hasSum_skelVal_outerValM Φ hd hS hSb hL0 P.γ P.δ base D layer hLayer (U.h i) tt selSk Zw hZ (hF i)
    (fam i) (Box i) (hexp i) (hbox i)).tsum_eq
  rw [this, ← skelVal_slotFn D hS P.L P.γ P.δ base roots tt layer hLayer selSk]
  rfl

end WaveTurbulence.Represents
