/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntWeight
public import WaveTurbulence.Foundations.Flower.MkSlotsB.RLeaves

/-! # B3s-HELPER7 (general assembly, W): a general class summand is β's relaxed pinned weighted leaf kernel

For every pattern `pat`, depth selection `kSel`, stem scales `σ`, selection scales `Rs` and dagger datum `dag`, the
frozen class summand of B4's hypothesis (`kernelKgenSel` with the intrinsic pins `fixCap … pat`, the removed phases
`offCap` and the marked weight `markedWt`) on a plain capped garden is β's relaxed pinned leaf kernel
`MkSlotsB.kernelLeavesSelNWFMR` (main's relaxed `kDomainFix`, coset base `0`, upper time `t`) with the anchored
profiles `MkSlots.anchProfiles`, the node-product weight `∏_z capNodeW` (frontier × node-local dagger weight) and the
decoration multiplier `selOK · stemFilterCap · selWeightCap` (`classSummand_eq_genKernel`). α's
`MkSlots.classSummand_eq_capKernel` is the case `pat ≡ plain`, `σ ≡ kSel ≡ none` (there through α's unpinned form).

* `offFactor_congr`, `offFactor_fixCap`: the removed-phase factor only reads the pins at the removed branches (the
  capped flower parents, pinned at `s` for every pattern);
* `dag_prod_pat`: α's `dag_prod` for every pattern;
* `genWeight_eq`: the marked weight times the removed-phase factor is `selOK · stem · sel · ∏_z capNodeW`;
* **`classSummand_eq_genKernel`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1MKGate WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntWeight

namespace WaveTurbulence.Flower.MkSlotsI

variable {w d : ℕ}

/-- The removed-phase factor only reads the pins of the removed branches. -/
theorem offFactor_congr (L γ δ : ℝ) (G : Garden w) (off : Finset (GBranch G.tree))
    (fix fix' : GBranch G.tree → Option ℝ) (h : ∀ b ∈ off, fix b = fix' b) (K : GNode G.tree → Mom d) :
    offFactor L γ δ G off fix K = offFactor L γ δ G off fix' K := by
  unfold offFactor
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [h b hb]

/-- At the capped flower parents every pattern pins at `s`: the removed-phase factor does not see the pattern. -/
theorem offFactor_fixCap (L γ δ : ℝ) (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)
    (dag : Bool) (K : GNode LG.garden.tree → Mom d) :
    offFactor L γ δ LG.garden (offCap LG J dag) (fixCap LG J pat t s) K =
      offFactor L γ δ LG.garden (offCap LG J dag) (fixCap LG J (fun _ => FixPat.plain) t s) K := by
  refine offFactor_congr L γ δ LG.garden _ _ _ (fun b hb => ?_) K
  have hcfp : IsCapFlowerParent LG J b := by
    unfold offCap at hb
    split_ifs at hb with hd
    · exact (Finset.mem_filter.1 hb).2
    · exact absurd hb (Finset.notMem_empty b)
  simp [fixCap, hcfp]

/-- **α's `dag_prod` for every pattern.** -/
theorem dag_prod_pat (L γ δ s t : ℝ) (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat)
    (dag : Option (Fin w → Fin 3 → Mom d)) (k : GNode LG.garden.tree → Mom d) :
    ((dag.elim 1 fun c => sibWeightCap LG J c k : ℝ) : ℂ) *
      offFactor L γ δ LG.garden (offCap LG J dag.isSome) (fixCap LG J pat t s) k =
    ∏ z, dagNodeW L γ δ s LG J dag z (k z) := by
  rw [offFactor_fixCap]
  exact dag_prod L γ δ s t LG J dag k

/-- **The general marked weight times the removed-phase factor**: `selOK · stem · sel · ∏_z capNodeW`. -/
theorem genWeight_eq (L γ δ : ℝ) (J : Finset (Fin w)) (p : ℕ) (pat : Fin w → FixPat) (t s : ℝ)
    (LG : LayeredGarden w) (hplain : LG.garden.IsPlain) (Rf : Fin w → Option ℝ) (σ kSel : Fin w → Option ℕ)
    (Rs : Fin w → ℝ) (dag : Option (Fin w → Fin 3 → Mom d)) (k : GNode LG.garden.tree → Mom d) :
    ((selOK LG J kSel * (Typed.frontierW LG p Rf k * stemFilterCap LG J L σ k *
        selWeightCap LG J (selCap LG J kSel) Rs k * dag.elim 1 (fun c => sibWeightCap LG J c k)) : ℝ) :
        ℂ) * offFactor L γ δ LG.garden (offCap LG J dag.isSome) (fixCap LG J pat t s) k =
      ((selOK LG J kSel * (stemFilterCap LG J L σ k * selWeightCap LG J (selCap LG J kSel) Rs k) : ℝ) : ℂ) *
        ∏ z, capNodeW L γ δ p s LG J Rf dag z (k z) := by
  have hd := dag_prod_pat L γ δ s t LG J pat dag k
  have hf := frontierW_eq_prod_fwNode LG hplain p Rf k
  unfold capNodeW
  rw [Finset.prod_mul_distrib, ← hd, ← hf]
  push_cast
  ring

/-- **A general class summand is β's relaxed pinned weighted leaf kernel.** -/
theorem classSummand_eq_genKernel (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (p : ℕ)
    (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ) (t s : ℝ)
    (LG : LayeredGarden (2 * R)) (hG : CapGeo LG J p) (hplain : LG.garden.IsPlain)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (sel : GenDecoration LG.garden P.d roots 0 → Prop) :
    kernelKgenSel P.L P.γ P.δ LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
      (markedWt P J p kSel h Rf σ Rs dag LG) (fun _ => t) 0 roots sel =
    MkSlotsB.kernelLeavesSelNWFMR P.L P.γ P.δ LG (anchProfiles J LG h P.L roots) (fun _ => t) 0 roots 0 sel
      (fun k => ∏ z, capNodeW P.L P.γ P.δ p s LG J Rf dag z (k z))
      (fun κ => ((selOK LG J kSel * (stemFilterCap LG J P.L σ (cosetDecoration LG.garden P.L 0 κ.1) *
        selWeightCap LG J (selCap LG J kSel) Rs (cosetDecoration LG.garden P.L 0 κ.1)) : ℝ) : ℂ))
      (fixCap LG J pat t s) := by
  rw [markedWt_eq, kernelKgenSel_eq_fixW P.L P.γ P.δ LG J _ _ (offCap_pinned LG J pat t s dag.isSome) h,
    MkSlotsB.kernelLeavesSelNWFMR_eq]
  unfold kernelLeavesFixSelW
  congr 1
  refine tsum_congr fun κ => ?_
  split_ifs with hsel
  · beta_reduce
    rw [genWeight_eq P.L P.γ P.δ J p pat t s LG hplain Rf σ kSel Rs dag]
    unfold FlowerP1.kernelLeavesFixTerm
    have hprof : ∏ ℓ ∈ inputLeaves LG.garden,
        (S2ST.typeProfilesAnchB J LG h ℓ.1 (cosetDecoration LG.garden P.L 0 κ.1 ℓ.toNode) : ℂ) =
        ∏ ℓ ∈ inputLeaves LG.garden, (anchProfiles J LG h P.L roots ℓ.1 (cosetDecoration LG.garden P.L 0 κ.1 ℓ.toNode) : ℂ) :=
      Finset.prod_congr rfl fun ℓ _ => by rw [typeProfilesAnchB_eq_anchProfiles LG J hG.cap_leaf h P.L κ ℓ]
    rw [hprof]
  · rfl

end WaveTurbulence.Flower.MkSlotsI
