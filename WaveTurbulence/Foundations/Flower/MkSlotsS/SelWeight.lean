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

/-- δ's shell radii (an instance of γ's generic stem filters): `[Rs j]` at a branch of a tree `j` whose selected vertex
exists, unless the branch is a selected vertex. -/
def selShellRad (b : GBranch LG.garden.tree) : List ℝ :=
  if (selCap LG J kSel b.1.1).isSome ∧ b ∉ selSetCap LG J kSel then [Rs b.1.1] else []

/-- The selection node weight on a branch: the selected filter at a selected vertex, the shells on the stem. -/
def selBW {d : ℕ} (k : GNode LG.garden.tree → Mom d) (b : GBranch LG.garden.tree) : ℂ :=
  if ∃ j, b ∈ stemSetCap LG J j then
    (if b ∈ selSetCap LG J kSel then ((chiD (|omegaNode LG.garden k b| / Rs b.1.1) : ℝ) : ℂ) else 1) *
      (radProd (selShellRad LG J kSel Rs b) (omegaNode LG.garden k b) : ℂ)
  else 1

/-- The selection constant `∏_j [v_j exists] Rs_j⁻¹`. -/
def selConst : ℝ := ∏ j, (selCap LG J kSel j).elim 1 fun _ => (Rs j)⁻¹

theorem radProd_singleton (r x : ℝ) : radProd [r] x = chi0 (|x| / r) := by
  simp [radProd]

/-- One tree of `selWeightCap`. -/
theorem selWeightCap_tree {d : ℕ} (k : GNode LG.garden.tree → Mom d) (j : Fin w) :
    (((selCap LG J kSel j).elim 1 fun vj =>
        (Rs j)⁻¹ * chiD (|omegaNode LG.garden k vj| / Rs j) *
          ∏ b ∈ (stemSetCap LG J j).erase vj, chi0 (|omegaNode LG.garden k b| / Rs j) : ℝ) : ℂ) =
      (((selCap LG J kSel j).elim 1 fun _ => (Rs j)⁻¹ : ℝ) : ℂ) *
        ∏ b ∈ stemSetCap LG J j, selBW LG J kSel Rs k b := by
  have hstem : ∀ b ∈ stemSetCap LG J j, ∃ j', b ∈ stemSetCap LG J j' := fun b hb => ⟨j, hb⟩
  have hfst : ∀ b ∈ stemSetCap LG J j, b.1.1 = j := fun b hb => (mem_stemSetCap_iff'.1 hb).1
  have hsel : ∀ b ∈ stemSetCap LG J j, b ∈ selSetCap LG J kSel → selCap LG J kSel j = some b := fun b hb hs => by
    have := selCap_of_mem_selSetCap hs
    rwa [hfst b hb] at this
  rcases hj : selCap LG J kSel j with _ | vj
  · simp only [Option.elim, Complex.ofReal_one, one_mul]
    symm
    refine Finset.prod_eq_one fun b hb => ?_
    have hns : b ∉ selSetCap LG J kSel := fun hs => by rw [hsel b hb hs] at hj; exact absurd hj (by simp)
    have hrad : selShellRad LG J kSel Rs b = [] := by
      unfold selShellRad
      rw [if_neg]
      rintro ⟨h1, -⟩
      rw [hfst b hb, hj] at h1
      exact absurd h1 (by simp)
    simp [selBW, hstem b hb, hns, hrad, radProd]
  · simp only [Option.elim]
    have hvj : vj ∈ stemSetCap LG J j := (selCap_spec hj).2
    have hvsel : vj ∈ selSetCap LG J kSel := Finset.mem_filter.2 ⟨Finset.mem_univ _, j, hj⟩
    have hiff : ∀ b ∈ stemSetCap LG J j, b ∈ selSetCap LG J kSel ↔ b = vj := fun b hb =>
      ⟨fun hs => Option.some.inj ((hsel b hb hs).symm.trans hj), fun h => h ▸ hvsel⟩
    have hrad : ∀ b ∈ stemSetCap LG J j, b ≠ vj → selShellRad LG J kSel Rs b = [Rs j] := fun b hb hne => by
      unfold selShellRad
      rw [if_pos ⟨by rw [hfst b hb, hj]; rfl, fun hs => hne ((hiff b hb).1 hs)⟩, hfst b hb]
    have hradv : selShellRad LG J kSel Rs vj = [] := by
      unfold selShellRad
      rw [if_neg]
      exact fun h => h.2 hvsel
    rw [← Finset.mul_prod_erase _ _ hvj]
    have hv : selBW LG J kSel Rs k vj = ((chiD (|omegaNode LG.garden k vj| / Rs j) : ℝ) : ℂ) := by
      simp [selBW, hstem vj hvj, hvsel, hradv, radProd, hfst vj hvj]
    have hrest : ∏ b ∈ (stemSetCap LG J j).erase vj, selBW LG J kSel Rs k b =
        ∏ b ∈ (stemSetCap LG J j).erase vj, ((chi0 (|omegaNode LG.garden k b| / Rs j) : ℝ) : ℂ) := by
      refine Finset.prod_congr rfl fun b hb => ?_
      obtain ⟨hne, hb'⟩ := Finset.mem_erase.1 hb
      have hns : b ∉ selSetCap LG J kSel := fun hs => hne ((hiff b hb').1 hs)
      simp [selBW, hstem b hb', hns, hrad b hb' hne, radProd_singleton]
    rw [hv, hrest]
    push_cast
    ring

/-- **S4 (constant × node product)**: the selection weight is the selection constant times the product of the
selection node weights over the capped-stem branches. -/
theorem selWeightCap_eq {d : ℕ} (k : GNode LG.garden.tree → Mom d) :
    ((selWeightCap LG J (selCap LG J kSel) Rs k : ℝ) : ℂ) =
      (selConst LG J kSel Rs : ℂ) * ∏ j, ∏ b ∈ stemSetCap LG J j, selBW LG J kSel Rs k b := by
  unfold selWeightCap selConst
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have := selWeightCap_tree LG J kSel Rs k j
  push_cast at this
  exact this

/-- The selection node weight vanishes off the capped stem. -/
theorem selBW_of_not_stem {d : ℕ} (k : GNode LG.garden.tree → Mom d) (b : GBranch LG.garden.tree)
    (hb : ∀ j, b ∉ stemSetCap LG J j) : selBW LG J kSel Rs k b = 1 := by
  simp [selBW, hb]

/-- The stem product as a product over all nodes (γ's `brExt`). -/
theorem prod_stem_selBW {d : ℕ} (k : GNode LG.garden.tree → Mom d) :
    ∏ j, ∏ b ∈ stemSetCap LG J j, selBW LG J kSel Rs k b = ∏ z, brExt (selBW LG J kSel Rs k) z := by
  rw [prod_brExt]
  have hdisj : ((univ : Finset (Fin w)) : Set (Fin w)).PairwiseDisjoint (fun j => stemSetCap LG J j) := by
    intro j _ j' _ hne
    refine Finset.disjoint_left.mpr fun b hb hb' => hne ?_
    exact (Finset.mem_filter.mp hb).2.1.symm.trans (Finset.mem_filter.mp hb').2.1
  rw [← Finset.prod_biUnion hdisj]
  symm
  rw [← Finset.prod_subset (Finset.subset_univ _) fun b _ hb => ?_]
  refine selBW_of_not_stem LG J kSel Rs k b fun j hj => hb ?_
  exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hj⟩

/-- At a residual selection (`chiD = chiDNorm · chiDN`, ruling R179). -/
theorem chiD_eq_chiDNorm_mul (u : ℝ) : chiD u = chiDNorm * chiDN u := by
  unfold chiDN
  field_simp [chiDNorm_pos.ne']

/-- The node weight at a selected vertex: `chiDNorm · chiDN(|Ω|/Rs)` (no shell). -/
theorem selBW_sel {d : ℕ} (k : GNode LG.garden.tree → Mom d) {b : GBranch LG.garden.tree}
    (hb : b ∈ selSetCap LG J kSel) :
    selBW LG J kSel Rs k b = (chiDNorm : ℂ) * chiDNS (|omegaNode LG.garden k b| / Rs b.1.1) := by
  have hst := (selCap_spec (selCap_of_mem_selSetCap hb)).2
  have hrad : selShellRad LG J kSel Rs b = [] := by
    unfold selShellRad; rw [if_neg]; exact fun h => h.2 hb
  simp only [selBW, if_pos (⟨b.1.1, hst⟩ : ∃ j, b ∈ stemSetCap LG J j), if_pos hb, hrad, radProd, List.map_nil,
    List.prod_nil, Complex.ofReal_one, mul_one, chiDNS_apply]
  rw [chiD_eq_chiDNorm_mul]
  push_cast
  ring

/-- The node weight at a stem branch that is not selected: the shells only. -/
theorem selBW_shell {d : ℕ} (k : GNode LG.garden.tree → Mom d) {b : GBranch LG.garden.tree}
    (hb : b ∉ selSetCap LG J kSel) :
    selBW LG J kSel Rs k b = MkSlotsT.stemBW LG J (selShellRad LG J kSel Rs) k b := by
  simp [selBW, MkSlotsT.stemBW, hb]

end Weight

/-! ## The partition over the kinds (γ's `stem_split`) -/

section Split

variable {S Gsb : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) {ι : Type} [Fintype ι] [DecidableEq ι] {blk : ι → RedSplice.CLBlock S}
  (Φ : SpliceShape blk Gsb) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)

/-- **S4 (the partition)**: on the reconstruction `LG = layeredReconstruction D hS layer hLayer` of a skeleton with a
splice shape `Φ` and γ's retention `StemRet` (the stem meets no unit interior), the selection weight is
`selConst · (ATOM part) · (TOP part) · (SLOT part)`. -/
theorem selWeight_split (hd : Disj blk)
    (hR : StemRet S D.tree blk (layeredReconstruction D hS layer hLayer) J)
    (k : GNode (layeredReconstruction D hS layer hLayer).garden.tree → Mom d) :
    ((selWeightCap (layeredReconstruction D hS layer hLayer) J
        (selCap (layeredReconstruction D hS layer hLayer) J kSel) Rs k : ℝ) : ℂ) =
      (selConst (layeredReconstruction D hS layer hLayer) J kSel Rs : ℂ) *
        ((∏ c ∈ univ.filter (fun c => c ∉ Φ.hinges hd),
            brExt (selBW (layeredReconstruction D hS layer hLayer) J kSel Rs k) (D.coreBranch hS (Φ.br c)).toNode) *
          (∏ j, brExt (selBW (layeredReconstruction D hS layer hLayer) J kSel Rs k)
            (D.coreBranch hS (blk j).upper).toNode) *
          ∏ s, slotFac D hS (brExt (selBW (layeredReconstruction D hS layer hLayer) J kSel Rs k)) s) := by
  rw [selWeightCap_eq, prod_stem_selBW]
  congr 1
  refine stem_split D hS Φ hd hR _ fun z hz => ?_
  unfold brExt
  split_ifs with hb
  · refine selBW_of_not_stem _ J kSel Rs k _ fun j hj => hz ?_
    exact onStemAddr_of_mem_stemSetCap hj
  · rfl

end Split

end WaveTurbulence.Flower.MkSlotsS
