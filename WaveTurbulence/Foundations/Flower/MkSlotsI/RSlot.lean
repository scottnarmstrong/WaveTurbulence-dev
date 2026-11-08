/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.RSlotEx

/-! # B3s-HELPER7 WP6 (R-slot): the general slot kernels of a member of the run class are the representative's

**`member_genSlot`**: for a member `y` of the run class of a prescribed point `a` at a marking `mk` (B3's
`sourceClass a p kind mk`, shape `memShape a mk y hy` onto `G_sb = (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G`)
and every slot `s'` of `G_sb`, the general slot kernel of `y` (β's relaxed pinned weighted kernel `slotFnGWFRL` on the
member's reconstruction `layeredReconstruction y.1.data y.1.plain (stateLayer y.1) _ = y.1.layered`, with the anchored
profiles, `MkSlots.chainW`, `genΘs` and the pattern pins `fixCap … pat`) at `Φ_y.iota s'` is the representative's
`genSlotKer` at `Φ_a.iota s'`, as functions of `(ts, k)`.

Hypotheses: the capped geometry `CapGeo … J p` of both reconstructions (it gives the single-leaf cap trees and one
capped flower per tree), the representative's pattern `hU` (`hrepUP`: no core of a unit atom of `a` is pinned by
`fixCap … pat`, β's `PatGeoU.hU_rep_pat_recon`; it implies B3s's `hrepU`), and, when the weight is stem dependent,
`CleanPt J a`.

Route (`RSlotKer` … `RSlotEx`): both kernels are `kerC`/`kerT` of the common native object (α's `memShape_nativeCouple`,
β's `memShape_nativeChain`) with node data read on the native object and on the root data of the slot (tree index,
root test, `rcOf`, weight layer, depth, lone path, core tests, clock pin), which are common to the run class. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.MkSlots

namespace WaveTurbulence.Flower.MkSlotsI

section Class

variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (J : Finset (Fin (2 * R)))
  (hGeoA : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J p)
  (hGeoY : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p)
  (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (hrepUP : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
      (a.prime.data.coreBranch a.prime.prime.1 b) = none)

include hy hG hGeoA hGeoY hrepUP in
/-- **R-slot: the general slot kernels of a member of the run class are the representative's.** For every slot `s'`
of `G_sb`, the member's general kernel at `Φ_y.iota s'` is `genSlotKer … (Φ_a.iota s')`. -/
theorem member_genSlot {d : ℕ} (L γ δ : ℝ) (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (roots : Fin (2 * R) → (Fin d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom d))
    (hstem : Stage1MKGate.StemDep σ kSel → Stage1MKGate.CleanPt J a)
    (s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) :
    MkSlotsB.slotFnGWFRL y.1.data y.1.plain L γ δ
        (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) h L
          roots)
        (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ p s J Rf dag)
        (genΘs y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J L σ kSel Rs)
        (stateLayer y.1) (stateLayer_isLayering y.1)
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)
        ((memShape a mk y hy).iota y.1.plain hG s') =
      genSlotKer L γ δ p a J pat t s σ kSel Rs h roots Rf dag
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s') := by
  have hex : Stage1MKGate.StemDep σ kSel → ∀ j,
      (selCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J kSel j).isSome =
        (selCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J kSel
          j).isSome := fun hsd j =>
    member_selEx a mk y hy hG J hGeoA hGeoY (MkSlotsB.hrepU_of_pat a mk J pat t s hrepUP) (hstem hsd) kSel j
  funext ts k
  cases s' with
  | inl q =>
    exact member_genSlot_inl a mk y hy hG J hGeoA hGeoY pat t s hrepUP L γ δ σ kSel Rs h roots Rf dag hstem
      hex q ts k
  | inr c =>
    exact member_genSlot_inr a mk y hy hG J hGeoA hGeoY pat t s hrepUP L γ δ σ kSel Rs h roots Rf dag hstem
      hex c ts k

end Class

end WaveTurbulence.Flower.MkSlotsI
