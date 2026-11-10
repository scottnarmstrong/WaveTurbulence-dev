/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceAddressSingular
public import WaveTurbulence.Foundations.Spine.RA1LW.SourcePairEnumeration
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceSingularBlocks

/-! # Original source leading singular integral as an actual chosen-address fold -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Links Reg

/-- The original finite link enumeration gives exactly the original
ordered list of chosen-node addresses. -/
theorem map_finRange_chosenNode (Q : RegCpl) :
    (List.finRange Q.links.length).map (chosenNode Q) = Q.links.map Prod.fst := by
  rw [← List.ofFn_eq_map]
  change List.ofFn (fun j : Fin Q.links.length => (Q.links.get j).1) = Q.links.map Prod.fst
  rw [List.ofFn_comp' Q.links.get Prod.fst,List.ofFn_get]

/-- The literal source singular leaf integral is the actual ordered fold
at its original chosen-node addresses. All analytic input is supplied by
the finite source spatial norm; there is no alternate coordinate model. -/
theorem addressAppAlong_source_eq_singInt {d : ℕ} (hd : 3 ≤ d)
    {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) (hn : 0 < Q.links.length)
    {K M : ℕ} {H : LGSpine.LeafProfiles 2 d} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ a, Fourier.spatialNorm K M (leafFam hQ hG H a) ≤ ENNReal.ofReal B))
    (Z : Finset (Fin 2 × TTree.Path)) (k : Mom d) :
    addressAppAlong Z (Q.links.map Prod.fst)
      (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k) 0 =
    singInt (markedLinkIndices Q Z) (fun x y =>
      ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a)) := by
  have he := addressAppAlong_map_chosenNode Q Z (List.finRange Q.links.length)
    (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k)
    (0:Fin Q.links.length → Mom d) (0:Fin Q.links.length → Mom d)
  have hz : paramFun Q (fun _ : Fin Q.links.length => ((0:Mom d),(0:Mom d))) = 0 := paramFun_zero Q
  rw [map_finRange_chosenNode] at he
  simp only [Pi.zero_apply] at he
  rw [hz] at he
  have hkernel : (fun (x y : Fin Q.links.length → Mom d) =>
      cplLeafProduct (addrFam H) (paramFun Q (fun i => (x i,y i))) Q (0,[]) (1,[]) k) =
      (fun x y => ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a)) := by
    funext x y
    exact (prod_source_input_eq_cplLeafProduct hQ hG (addrFam H) k
      (fun j i => if i=0 then x j else y j)).symm
  rw [hkernel] at he
  exact he.trans (appAlong_source_eq_singInt hd hQ hG hn hK hM hB hF
    (markedLinkIndices Q Z) (List.finRange Q.links.length) (List.nodup_finRange _)
    (fun j => by simp) k 0 0)

end WaveTurbulence.RA1Leafwise
