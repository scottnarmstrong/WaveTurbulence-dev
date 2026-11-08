/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsG.Piece

/-! # B3s-HELPER6: the radii `radRaw` reproduce the stem part of the class weight

On every layered garden `LG` (in particular on every member of a class), the stem part of the intrinsic marked weight
`markedWeight` — σ's capped stem filters `stemFilterCap` times the selected-face weights `selWeightCap` at the
intrinsic selected vertices `selCap` — is γ's generic stem filter weight `MkSlotsT.stemFiltG` with the radii
`radRaw` of G1 (σ's `2^{σ j} L` and the selection shell `Rs j` off the selected vertex), times the factors
`(Rs j)⁻¹ chiD(|Ω_{v_j}|/Rs j)` of the selected vertices (**`stemFilterCap_mul_selWeightCap`**). This is the
identity the analytic integration splits with γ's `stemFiltG_factor` (atom part = `filtGen`, top part = unit top
filters, slot part = slot factors), the selected-vertex factor going to `filtGen = (Rs, chiDN)` (residual) or into
its slot (absorbed), and σ's filter at a residual selected vertex to `indGen`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkSlotsG

variable {w d : ℕ}

/-- The selection shells of `selWeightCap` as a generic stem filter family. -/
theorem stemFiltG_shellRad (LG : LayeredGarden w) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ)
    (Rs : Fin w → ℝ) (k : GNode LG.garden.tree → Mom d) :
    MkSlotsT.stemFiltG LG J (shellRad LG J kSel Rs) k =
      ∏ j : Fin w, (selCap LG J kSel j).elim 1 fun vj =>
        ∏ b ∈ (stemSetCap LG J j).erase vj, chi0 (|omegaNode LG.garden k b| / Rs j) := by
  unfold MkSlotsT.stemFiltG
  refine Finset.prod_congr rfl fun j _ => ?_
  rcases hv : selCap LG J kSel j with _ | vj
  · simp only [Option.elim]
    refine Finset.prod_eq_one fun b hb => ?_
    have hbj : b.1.1 = j := (Finset.mem_filter.mp hb).2.1
    have hs : shellRad LG J kSel Rs b = [] := by
      unfold shellRad
      refine ite_eq_right_of_eq_false _ _ (eq_false ?_)
      rintro ⟨v, hv', -⟩
      rw [hbj, hv] at hv'
      cases hv'
    rw [hs]
    rfl
  · simp only [Option.elim]
    have hvj : MkSlotsT.radProd (shellRad LG J kSel Rs vj) (omegaNode LG.garden k vj) = 1 := by
      have hs : shellRad LG J kSel Rs vj = [] := by
        unfold shellRad
        refine ite_eq_right_of_eq_false _ _ (eq_false ?_)
        rintro ⟨v, hv', hne⟩
        have hvj1 : vj.1.1 = j := MkSlotsS.selCap_fst hv
        rw [hvj1, hv] at hv'
        exact hne (Option.some.inj hv').symm
      rw [hs]
      rfl
    rw [← Finset.prod_erase (f := fun b => MkSlotsT.radProd (shellRad LG J kSel Rs b) (omegaNode LG.garden k b))
      _ hvj]
    refine Finset.prod_congr rfl fun b hb => ?_
    have hne : b ≠ vj := Finset.ne_of_mem_erase hb
    have hbj : b.1.1 = j := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hb)).2.1
    have hs : shellRad LG J kSel Rs b = [Rs j] := by
      unfold shellRad
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨vj, by rw [hbj, hv], fun h => hne h.symm⟩), hbj]
    rw [hs]
    simp [MkSlotsT.radProd]

/-- σ's filters and the selection shells together: the generic stem filter family with the radii `radRaw`. -/
theorem stemFiltG_radRaw (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ)
    (Rs : Fin w → ℝ) (k : GNode LG.garden.tree → Mom d) :
    MkSlotsT.stemFiltG LG J (radRaw LG J L σ kSel Rs) k =
      stemFilterCap LG J L σ k * ∏ j : Fin w, (selCap LG J kSel j).elim 1 fun vj =>
        ∏ b ∈ (stemSetCap LG J j).erase vj, chi0 (|omegaNode LG.garden k b| / Rs j) := by
  unfold radRaw
  rw [MkSlotsT.stemFiltG_append, ← MkSlotsT.stemFilterCap_eq, stemFiltG_shellRad]

/-- **The stem part of the class weight** is the generic stem filter weight with the radii `radRaw`, times the
factors of the selected vertices. -/
theorem stemFilterCap_mul_selWeightCap (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ)
    (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ) (k : GNode LG.garden.tree → Mom d) :
    stemFilterCap LG J L σ k * selWeightCap LG J (selCap LG J kSel) Rs k =
      MkSlotsT.stemFiltG LG J (radRaw LG J L σ kSel Rs) k *
        ∏ j : Fin w, (selCap LG J kSel j).elim 1 fun vj =>
          (Rs j)⁻¹ * chiD (|omegaNode LG.garden k vj| / Rs j) := by
  rw [stemFiltG_radRaw]
  have hsel : selWeightCap LG J (selCap LG J kSel) Rs k =
      (∏ j : Fin w, (selCap LG J kSel j).elim 1 fun vj => (Rs j)⁻¹ * chiD (|omegaNode LG.garden k vj| / Rs j)) *
        ∏ j : Fin w, (selCap LG J kSel j).elim 1 fun vj =>
          ∏ b ∈ (stemSetCap LG J j).erase vj, chi0 (|omegaNode LG.garden k b| / Rs j) := by
    unfold selWeightCap
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rcases selCap LG J kSel j with _ | vj
    · simp
    · rfl
  rw [hsel]
  ring

end WaveTurbulence.Flower.MkSlotsG
