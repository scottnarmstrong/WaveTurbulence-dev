/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelSpec
public import WaveTurbulence.Foundations.Flower.MkSlotsT.Weight

/-! # B3s-HELPER4 (δ) S4: the selection weight in the chain's interface

The selection part of the marked weight (`MkDefs.selWeightCap`, `selOK`) of a layered garden `LG`:
`selWeightCap LG J (selCap LG J kSel) Rs k = ∏_j [v_j exists] Rs_j⁻¹ · chiD(|Ω_{v_j}|/Rs_j) ·
∏_{b ∈ stemSetCap j, b ≠ v_j} χ₀(|Ω_b|/Rs_j)`.

* **`selWeightCap_eq`**: it is the constant `∏_j [v_j exists] Rs_j⁻¹` times the product over the capped-stem
  branches of the node weight `selBW` = (selected filter `chiD(|Ω_b|/Rs)` at the selected vertices) ×
  (δ's shells, helper γ's generic stem filters `MkSlotsT.stemFiltG` with the radii `selShellRad`: `[Rs j]` on the stem of
  a selected tree off its selected vertex), i.e. `∏_z brExt selBW z` over all nodes;
* **`selWeight_split`** (on the reconstruction of a skeleton with a splice shape and γ's retention `StemRet`): this
  node product is γ's partition `MkSlotsT.stem_split`: ATOM part `∏_{c ∉ hinges} selBW(core c)` (filters `filt` of the
  outer non-hinge atoms of `G_sb`), TOP part `∏_j selBW(core u_j)` (unit top filters: only shells, `selBW_shell`, since a
  selected vertex is never a unit top, `coreBranch_unit_not_sel`), SLOT part `∏_s slotFac selBW s` (the per-slot factors `Θs` of the β reduction:
  the selected filter of an absorbed selection and the shells inside native objects);
* `chiD_eq_chiDNorm_mul` / `selBW_core_sel`: at a residual selected atom `chiD = chiDNorm · chiDN` (ruling R179: the
  piece's filter is `(Rs j, chiDN)`, the constant `chiDNorm^{#selR}` goes into the weight `w`).

**The gain `Rs j ^ (-1)` of `selMassMK`** is the explicit prefactor `(Rs j)⁻¹` of `selWeightCap` at every selected
tree (`selWeightCap_eq`): a decoration-independent constant of the member weight, hence a factor of the representation's
weight `w`. The `Rs j ^ (-1/18)` of an absorbed selection comes from D6 inside its slot (S3); a residual selection has
no `Rs^{-1/18}` here (D7 produces it from the moments of `RepresentsIntMKSel`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Flower.MkDefs
open WaveTurbulence.VineB
open WaveTurbulence.Flower.MkSlotsT (stemFiltG radProd brExt prod_brExt stem_split slotFac StemRet OnStemAddr
  onStemAddr_of_mem_stemSetCap)

namespace WaveTurbulence.Flower.MkSlotsS

variable {w d : ℕ}

section Weight

variable (LG : LayeredGarden w) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)

/-- At a residual selection (`chiD = chiDNorm · chiDN`, ruling R179). -/
theorem chiD_eq_chiDNorm_mul (u : ℝ) : chiD u = chiDNorm * chiDN u := by
  unfold chiDN
  field_simp [chiDNorm_pos.ne']

end Weight

/-! ## The partition over the kinds (γ's `stem_split`) -/

section Split

variable {S Gsb : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) {ι : Type} [Fintype ι] [DecidableEq ι] {blk : ι → RedSplice.CLBlock S}
  (Φ : SpliceShape blk Gsb) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)

end Split

end WaveTurbulence.Flower.MkSlotsS
