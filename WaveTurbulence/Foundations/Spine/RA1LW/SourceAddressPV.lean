/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceAddressLeading

/-! # Actual cutoff convergence at chosen addresses after source integration blocks -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Links Function Filter Topology

/-- The original finite-coordinate source PV convergence is the exact
chosen-address PV convergence, with every other parameter fixed. -/
theorem tendsto_pvTrunc_address_source_block {d : ℕ} (hd : 3 ≤ d)
    {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) (hn : 0 < Q.links.length)
    {K M : ℕ} {H : LGSpine.LeafProfiles 2 d} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ a, Fourier.spatialNorm K M (leafFam hQ hG H a) ≤ ENNReal.ofReal B))
    (Z : Finset (Fin 2 × TTree.Path)) (L : List (Fin Q.links.length))
    (hL : L.Nodup) (j : Fin Q.links.length) (hj : j ∉ L) (k : Mom d)
    (x y : Fin Q.links.length → Mom d) :
    Tendsto (fun s : ℝ => pvTrunc s (fun a b =>
      addressAppAlong Z (L.map (chosenNode Q))
        (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k)
        (update (paramFun Q (fun i => (x i,y i))) (chosenNode Q j) (a,b)))) atTop
      (𝓝 (pvOp (fun a b =>
        addressAppAlong Z (L.map (chosenNode Q))
          (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k)
          (update (paramFun Q (fun i => (x i,y i))) (chosenNode Q j) (a,b))))) := by
  have hkernel : (fun (x y : Fin Q.links.length → Mom d) =>
      cplLeafProduct (addrFam H) (paramFun Q (fun i => (x i,y i))) Q (0,[]) (1,[]) k) =
      (fun x y => ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a)) := by
    funext x y
    exact (prod_source_input_eq_cplLeafProduct hQ hG (addrFam H) k
      (fun j i => if i=0 then x j else y j)).symm
  have he : (fun a b => addressAppAlong Z (L.map (chosenNode Q))
      (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k)
      (update (paramFun Q (fun i => (x i,y i))) (chosenNode Q j) (a,b))) =
      (fun a b => appAlong (markedLinkIndices Q Z) L
        (fun x y => ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
          (fun j i => if i=0 then x j else y j) a)) (update x j a) (update y j b)) := by
    funext a b
    rw [← paramFun_update,← pairArray_update,addressAppAlong_map_chosenNode,hkernel]
  rw [he]
  exact tendsto_pvTrunc_source_block hd hQ hG hn hK hM hB hF
    (markedLinkIndices Q Z) L hL j hj k x y

/-- Cutoff convergence is independent of the values assigned away from
chosen source nodes. This form applies inside recursive source blocks. -/
theorem tendsto_pvTrunc_address_source_block_at {d : ℕ} (hd : 3 ≤ d)
    {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) (hn : 0 < Q.links.length)
    {K M : ℕ} {H : LGSpine.LeafProfiles 2 d} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ a, Fourier.spatialNorm K M (leafFam hQ hG H a) ≤ ENNReal.ofReal B))
    (Z : Finset (Fin 2 × TTree.Path)) (L : List (Fin Q.links.length))
    (hL : L.Nodup) (j : Fin Q.links.length) (hj : j ∉ L) (k : Mom d)
    (θ : Fin 2 × TTree.Path → Mom d × Mom d) :
    Tendsto (fun s : ℝ => pvTrunc s (fun a b =>
      addressAppAlong Z (L.map (chosenNode Q))
        (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k)
        (update θ (chosenNode Q j) (a,b)))) atTop
      (𝓝 (pvOp (fun a b =>
        addressAppAlong Z (L.map (chosenNode Q))
          (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k)
          (update θ (chosenNode Q j) (a,b))))) := by
  let x : Fin Q.links.length → Mom d := fun i => (θ (chosenNode Q i)).1
  let y : Fin Q.links.length → Mom d := fun i => (θ (chosenNode Q i)).2
  have he : (fun a b => addressAppAlong Z (L.map (chosenNode Q))
      (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k)
      (update θ (chosenNode Q j) (a,b))) =
      (fun a b => addressAppAlong Z (L.map (chosenNode Q))
        (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k)
        (update (paramFun Q (fun i => (x i,y i))) (chosenNode Q j) (a,b))) := by
    funext a b
    apply addressAppAlong_cplLeafProduct_congr_params Z _ (addrFam H) Q _ _ k indep_roots
    intro l hl
    by_cases he : l.1 = chosenNode Q j
    · simp only [he,update_self]
    · simp only [update_of_ne he]
      obtain ⟨i,hi⟩ := (show l.1 ∈ Set.range (chosenNode Q) from by
        rw [range_chosenNode]
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨l,hl,rfl⟩))
      rw [← hi,paramFun_chosen]
  rw [he]
  exact tendsto_pvTrunc_address_source_block hd hQ hG hn hK hM hB hF Z L hL j hj k x y

end WaveTurbulence.RA1Leafwise
