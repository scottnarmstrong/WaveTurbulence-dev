/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.SourcePlacedFold
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceAddressFactors

/-! # Source PV convergence after partial blocks at actual child placements -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Links Reg TTree Function Filter Topology

/-- The original norm supplies actual local cutoff convergence after any
nodup child block, at every independent placement and initial environment. -/
theorem tendsto_pvTrunc_placed_source_block {d w : ℕ} (hd : 3 ≤ d)
    {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) (hn : 0 < Q.links.length)
    {K M : ℕ} {H : Fin w × Path → Mom d → ℝ} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ z, Fourier.spatialNorm K M (addrFam H z) ≤ ENNReal.ofReal B))
    (Z : Finset (Fin w × Path)) (L : List (Fin Q.links.length))
    (hL : L.Nodup) (j : Fin Q.links.length) (hj : j ∉ L)
    (a b : Fin w × Path) (hab : Indep a b) (k : Mom d)
    (θ : Fin w × Path → Mom d × Mom d) :
    Tendsto (fun s : ℝ => pvTrunc s (fun x y =>
      addressAppAlong Z ((L.map (chosenNode Q)).map (rootPlacement a b))
        (fun θ => cplLeafProduct (addrFam H) θ Q a b k)
        (update θ (rootPlacement a b (chosenNode Q j)) (x,y)))) atTop
      (𝓝 (pvOp (fun x y =>
        addressAppAlong Z ((L.map (chosenNode Q)).map (rootPlacement a b))
          (fun θ => cplLeafProduct (addrFam H) θ Q a b k)
          (update θ (rootPlacement a b (chosenNode Q j)) (x,y))))) := by
  have hkernel : (fun θ => cplLeafProduct (addrFam H) θ Q a b k) =
      (fun θ => cplLeafProduct (addrFam (fun z => H (rootPlacement a b z))) (fun z => θ (rootPlacement a b z)) Q (0,[]) (1,[]) k) := by
    funext θ
    exact cplLeafProduct_rootPlacement (addrFam H) θ Q a b k hab
  have he : (fun x y =>
      addressAppAlong Z ((L.map (chosenNode Q)).map (rootPlacement a b))
        (fun θ => cplLeafProduct (addrFam H) θ Q a b k)
        (update θ (rootPlacement a b (chosenNode Q j)) (x,y))) =
      (fun x y =>
        addressAppAlong (Z.preimage (rootPlacement a b) (rootPlacement_injective hab).injOn)
          (L.map (chosenNode Q))
          (fun θ => cplLeafProduct (addrFam (fun z => H (rootPlacement a b z))) θ Q (0,[]) (1,[]) k)
          (update (fun z => θ (rootPlacement a b z)) (chosenNode Q j) (x,y))) := by
    funext x y
    rw [hkernel,addressAppAlong_pullback (rootPlacement a b) (rootPlacement_injective hab) Z _
      (fun _ => Finset.mem_preimage.symm) (L.map (chosenNode Q))
      (fun θ => cplLeafProduct (addrFam (fun z => H (rootPlacement a b z))) θ Q (0,[]) (1,[]) k),
      address_update_comp _ (rootPlacement_injective hab)]
  rw [he]
  exact tendsto_pvTrunc_address_source_block_at (H := fun z => H (rootPlacement a b z)) hd hQ hG hn hK hM hB (fun _ => hF _) _ L hL j hj k _

end WaveTurbulence.RA1Leafwise
