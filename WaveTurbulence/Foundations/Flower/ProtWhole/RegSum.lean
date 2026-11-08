/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtWhole.RegBound
public import WaveTurbulence.Foundations.Spine.RegularLayeringCount
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Trunc
public import WaveTurbulence.Foundations.Molecule.GardenNodeCounts
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.NodeCounts
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxLeaf
public import WaveTurbulence.Foundations.RegStruct.CodeOrders

/-! # D6b: counting wholly regular components

* `CapG.protIncoh_eq`: the protected incoherency of the paired tree is the incoherency of the couple code (general
  index version of D2c's `protIncoh_cap`);
* `card_gnode`, `CapG.card_frontS_le`, `CapG.card_inputLeaves_le`: node and input-leaf counts;
* `sum_le_geom`: a sum over a family split by incoherency, with geometric counts, is at most twice its base;
* `CapG.norm_compValue_le`: the real per-garden bound of a wholly regular component (all cases of `kSel`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtWhole

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtGeo
open WaveTurbulence.Flower.MkDefs

/-- The node count of a garden: `3 n + w`. -/
theorem card_gnode {w : ℕ} (tree : Fin w → TTree) :
    Fintype.card (GNode tree) = ∑ j, (3 * (tree j).order + 1) := by
  have hc : Fintype.card (GNode tree) = (forestSet tree TTree.nodes).card :=
    @Fintype.card_of_subtype (Fin w × Path) (fun a => a.2 ∈ (tree a.1).nodes)
    (forestSet tree TTree.nodes) (fun a => Mole.mem_forestSet tree TTree.nodes a)
    (inferInstanceAs (Fintype (GNode tree)))
  rw [hc, Mole.card_forestSet]
  exact Finset.sum_congr rfl fun j _ => Comb.card_nodes _

/-- **Geometric counting.** -/
theorem sum_le_geom {α : Type*} (A : Finset α) (gf : α → ℕ) (v : α → ℝ) (C0 K ρ M : ℝ) (hC0 : 0 ≤ C0)
    (hK : 0 ≤ K) (hρ : 0 ≤ ρ) (hM : 0 ≤ M) (hKρ : K * ρ ≤ 1 / 2)
    (hcard : ∀ g, ((A.filter fun x => gf x = g).card : ℝ) ≤ C0 * K ^ g) (hv : ∀ x ∈ A, v x ≤ M * ρ ^ gf x) :
    ∑ x ∈ A, v x ≤ 2 * C0 * M := by
  have hmaps : ∀ x ∈ A, gf x ∈ Finset.range (A.sup gf + 1) :=
    fun x hx => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup hx))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hKρ0 : 0 ≤ K * ρ := mul_nonneg hK hρ
  calc ∑ g ∈ Finset.range (A.sup gf + 1), ∑ x ∈ A with gf x = g, v x
      ≤ ∑ g ∈ Finset.range (A.sup gf + 1), (C0 * K ^ g) * (M * ρ ^ g) := by
        refine Finset.sum_le_sum fun g _ => ?_
        calc ∑ x ∈ A with gf x = g, v x ≤ ∑ x ∈ A with gf x = g, M * ρ ^ g :=
              Finset.sum_le_sum fun x hx => by
                rw [← (Finset.mem_filter.1 hx).2]; exact hv x (Finset.mem_filter.1 hx).1
          _ = ((A.filter fun x => gf x = g).card : ℝ) * (M * ρ ^ g) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (C0 * K ^ g) * (M * ρ ^ g) :=
              mul_le_mul_of_nonneg_right (hcard g) (mul_nonneg hM (pow_nonneg hρ _))
    _ = C0 * M * ∑ g ∈ Finset.range (A.sup gf + 1), (K * ρ) ^ g := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [mul_pow]; ring
    _ ≤ C0 * M * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 hM)
        calc ∑ g ∈ Finset.range (A.sup gf + 1), (K * ρ) ^ g
            ≤ ∑ g ∈ Finset.range (A.sup gf + 1), (1 / 2 : ℝ) ^ g :=
              Finset.sum_le_sum fun g _ => pow_le_pow_left₀ hKρ0 hKρ g
          _ ≤ 2 := sum_geometric_two_le _
    _ = 2 * C0 * M := by ring

theorem norm_le_of_enorm_le {z : ℂ} {y : ℝ} (hy : 0 ≤ y) (h : ‖z‖ₑ ≤ ENNReal.ofReal y) : ‖z‖ ≤ y := by
  rwa [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_ofReal_iff hy] at h

namespace CapG

variable {LG : LayeredGarden 2} {j0 c : Fin 2} {X : RegChain} {ζ : ℤˣ} (D : CapG LG j0 c X ζ)
include D

theorem layerAt1 (x : Fin 1 × Path) : layerAt D.T1 x = layerAt LG (j0, x.2) := by
  obtain ⟨j, p⟩ := x
  rw [D.fin1 j]
  by_cases h : p ∈ (D.T1.garden.tree 0).nodes
  · rw [layerAt_node D.T1 ⟨((0 : Fin 1), p), h⟩]
    rfl
  · have h' : p ∈ (LG.garden.tree j0).nodes → False := by rw [← D.tree_eq]; exact h
    unfold layerAt
    rw [dif_neg h, dif_neg h']

theorem protIncoh_eq {Q : RegCpl} (hQ : Q.Decodes LG.garden) (hl : Q.links = X.linksAt ζ (j0, [])) :
    protIncoh X D.T1 = LG.incoherency Q.links := by
  show D.T1.incoherency (X.treeLinks (D.T1.garden.sig 0)) = _
  have hs : D.T1.garden.sig 0 = ζ := rfl
  rw [incoherency_eq_count hQ, tree_incoherency_eq_count (decodedTree_decodes X ζ), hl, RegChain.treeLinks, hs]
  let φ : Fin 1 × Path → Fin 2 × Path := fun z => (j0, z.2)
  have hφ : ∀ z q, φ (addrExt z q) = addrExt (φ z) q := by intro z q; simp [φ, addrExt]
  rw [show ((j0, ([] : Path)) : Fin 2 × Path) = φ ((0 : Fin 1), []) from rfl,
    chain_linksAt_map X φ hφ ζ ((0 : Fin 1), []), List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun l _ => ?_
  simp only [Function.comp_apply, φ, D.layerAt1]

theorem card_frontS_le' (p : ℕ) : (D.frontS p).card ≤ 3 * LG.garden.order + 1 := by
  refine (D.card_frontS_le p).trans (le_of_eq ?_)
  rw [card_gnode, Fin.sum_univ_one, D.order_eq]
  rfl

theorem card_inputLeaves_le : (inputLeaves D.T1.garden).card ≤ LG.garden.order := by
  have h := VineEstS5C.P4.W2.card_inputLeaves_add_marked D.T1.garden
  rw [D.order_eq]
  omega

end CapG

end WaveTurbulence.Flower.ProtWhole
