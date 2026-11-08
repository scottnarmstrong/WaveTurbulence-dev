/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeo
public import WaveTurbulence.Foundations.Flower.MkSlots.RedFix
public import WaveTurbulence.Foundations.Flower.MkSlots.PVB1
public import WaveTurbulence.Foundations.Flower.MkSlots.IntCapHyp

/-! # B3s-HELPER3 B4 (3/4): unit interiors are unpinned for every pattern (`hU`), at the representative

`Geo.fixCap_coreBranch_unit` (all patterns) at an arbitrary marked set `Mk` of the representative `a` containing the
marked vines of `𝒱₀(σ)` (`hMk`; at `Mk = classMk mkF a` this is `FineMarking.sub`):

* `fixCap_decoded_eq`: the pins of a decoded garden at a decoded core branch are those of the reconstruction;
* **`hU_rep_pat`**: no core branch of an atom of a unit of `a` at `Mk` is pinned (`a.layered`, decoded core branch);
* **`hU_rep_pat_recon`**: the same on the reconstruction `recLG a` (the form of B3s's `hrepU` in `IntCore2/3`);
* **`hU_pat_inter`**: the hypothesis `hU` of `MkSlots.hasSum_skelValF_outerValMμ` for the skeleton pins
  `fixCore a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s)` and the units `unitBlkMk … Mk`.

For a member `y` of the run class (`hU` of the member's VINE-B♯) see `PatGeoCore` (`member_fix_unit_pat`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.ProtGeo
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.RedSplice (Prescription stSt vinesV0 unitBlocks)

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ}

/-- The pins of a decoded garden at a decoded core branch are those of the reconstruction. -/
theorem fixCap_decoded_eq {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (LG : LayeredGarden w)
    (hspec : layeredReconstruction D hS layer hLayer = LG) (hd : D.Decodes hS LG.garden) (J : Finset (Fin w))
    (pat : Fin w → FixPat) (t s : ℝ) (b : GBranch S.tree) :
    fixCap LG J pat t s (D.decodedCoreBranch hS hd b) =
      fixCap (layeredReconstruction D hS layer hLayer) J pat t s (D.coreBranch hS b) := by
  subst hspec
  rfl

section Rep

variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
  (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton))
  (hMk : ∀ c ∈ markI J pat t s kSel a.prime, c ∈ vinesV0 a.prime.skeleton a.totalSigma → c ∈ Mk)

include hMk in
/-- **No core branch of an atom of a unit of the representative is pinned** (every pattern, any marked set `Mk`
containing the marked vines of `𝒱₀(σ)`). -/
theorem hU_rep_pat (j : Fin (unitBlocks a.prime.skeleton a.totalSigma Mk).length) (y : GBranch a.prime.skeleton.tree)
    (hy : y ∈ (VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk j).atoms) :
    fixCap a.layered J pat t s (a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes y) = none := by
  have hu : VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk j ∈
      unitBlocks a.prime.skeleton a.totalSigma Mk := List.get_mem _ _
  obtain ⟨c, hc, hyc, -⟩ := RedSplice.unitBlocks_soundMk hu y hy
  rw [RedSplice.mem_vinesV0] at hc
  obtain ⟨hc0, hcMk⟩ := hc
  by_contra hpin
  have hpin' := Option.ne_none_iff_isSome.1 hpin
  have hm : c ∈ markI J pat t s kSel a.prime :=
    marked_of_fix_atom a.prime pat t s kSel c (RedSplice.vinesV0_subset _ _ hc0) y hyc hpin' rfl
  exact hcMk (hMk c hm hc0)

include hMk in
/-- `hU_rep_pat` on the reconstruction `recLG a` (core branches `a.prime.data.coreBranch`). -/
theorem hU_rep_pat_recon (j : Fin (unitBlocks a.prime.skeleton a.totalSigma Mk).length)
    (y : GBranch a.prime.skeleton.tree)
    (hy : y ∈ (VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk j).atoms) :
    fixCap (recLG a) J pat t s (a.prime.data.coreBranch a.prime.prime.1 y) = none := by
  rw [← fixCap_decoded_eq a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
    (sourceLayer_reconstructs a) a.prime.decodes]
  exact hU_rep_pat J pat t s kSel a Mk hMk j y hy

include hMk in
/-- **`hU` of `MkSlots.hasSum_skelValF_outerValMμ`** at the representative, for every pattern: the unit interiors
of `unitBlkMk … Mk` carry no skeleton pin `fixCore (fixCap (recLG a) J pat t s)`. -/
theorem hU_pat_inter : ∀ j, ∀ x ∈ VineB.inter (VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk) j,
    fixCore a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) x = none :=
  fixU_of_atoms _ fun j x hx => hU_rep_pat_recon J pat t s kSel a Mk hMk j x hx

/-- The marked set of the class piece satisfies `hMk` (`FineMarking.sub`). -/
theorem classMk_hMk (mkF : Stage1Mk.MarkFn w)
    (hsub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B) :
    ∀ c ∈ markI J pat t s kSel a.prime, c ∈ vinesV0 a.prime.skeleton a.totalSigma →
      c ∈ Stage1MKGate.classMk mkF a :=
  fun _ hc h0 => ⟨hsub a.prime hc, h0⟩

end Rep

end WaveTurbulence.Flower.MkSlotsB
