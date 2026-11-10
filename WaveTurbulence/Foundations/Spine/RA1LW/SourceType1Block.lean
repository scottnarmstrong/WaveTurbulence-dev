/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceTripleBlocks

/-! # Exact child-block factorization at an original type1 source node -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Reg TTree Function

/-- Chosen nodes remain distinct at every independent placement. -/
theorem source_chosen_nodup {w : ℕ} (Q : RegCpl) (a b : Fin w × Path) (hab : Indep a b) :
    ((Q.linksAt a b).map Prod.fst).Nodup := by
  have he : (Q.linksAt a b).map Prod.fst = (Q.links.map Prod.fst).map (rootPlacement a b) := by
    rw [cpl_links_rootPlacement,List.map_map,List.map_map]
    rfl
  rw [he]
  exact List.Nodup.map (rootPlacement_injective hab) (chosen_nodup Q)

/-- The three actual child blocks at a type1 source node factor at their
original child momenta. The root parameter is frozen only while its
children's internal parameters are integrated. -/
theorem addressAppAlong_type1_children {d w : ℕ} (hd : 3 ≤ d)
    (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl)
    {K M : ℕ} {H : Fin w × TTree.Path → Mom d → ℝ} {B : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ z, Fourier.spatialNorm K M (addrFam H z) ≤ ENNReal.ofReal B))
    (Z : Finset (Fin w × Path)) (a b : Fin w × Path) (hab : Indep a b) (r : Mom d)
    (θ : Fin w × Path → Mom d × Mom d) :
    addressAppAlong Z
      (((Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0])).map Prod.fst)++
       ((Q₂.linksAt (addrExt b [1]) (addrExt a [1])).map Prod.fst)++
       ((Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2])).map Prod.fst))
      (fun θ => cplLeafProduct (addrFam H) θ (.type1 c Q₁ Q₂ Q₃) a b r) θ =
    addressAppAlong Z ((Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0])).map Prod.fst)
      (fun θ' => cplLeafProduct (addrFam H) θ' Q₁ (addrExt a [0]) (addrExt b [c.partner 0])
        (childVals r (θ a) 0)) θ *
    addressAppAlong Z ((Q₂.linksAt (addrExt b [1]) (addrExt a [1])).map Prod.fst)
      (fun θ' => cplLeafProduct (addrFam H) θ' Q₂ (addrExt b [1]) (addrExt a [1])
        (childVals r (θ a) 1)) θ *
    addressAppAlong Z ((Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2])).map Prod.fst)
      (fun θ' => cplLeafProduct (addrFam H) θ' Q₃ (addrExt a [2]) (addrExt b [c.partner 2])
        (childVals r (θ a) 2)) θ := by
  let L₁ := (Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0])).map Prod.fst
  let L₂ := (Q₂.linksAt (addrExt b [1]) (addrExt a [1])).map Prod.fst
  let L₃ := (Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2])).map Prod.fst
  have hnd : (a::(L₁++L₂++L₃)).Nodup := by
    have hh := source_chosen_nodup (.type1 c Q₁ Q₂ Q₃) a b hab
    simpa only [RegCpl.linksAt,List.map_cons,List.map_append] using hh
  have hroot := (List.nodup_cons.mp hnd).1
  have htail := (List.nodup_cons.mp hnd).2
  have h₁₂₃ := (List.nodup_append'.mp htail).2.2
  have h₁₂ := (List.nodup_append'.mp (List.nodup_append'.mp htail).1).2.2
  have h₁₃ : List.Disjoint L₁ L₃ := by
    apply List.disjoint_left.mpr
    intro z hz₁ hz₃
    exact List.disjoint_left.mp h₁₂₃ (List.mem_append_left _ hz₁) hz₃
  have h₂₃ : List.Disjoint L₂ L₃ := by
    apply List.disjoint_left.mpr
    intro z hz₂ hz₃
    exact List.disjoint_left.mp h₁₂₃ (List.mem_append_right _ hz₂) hz₃
  let Hk := fun (v : Mom d × Mom d) (θ : Fin w × Path → Mom d × Mom d) =>
    cplLeafProduct (addrFam H) θ Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) (childVals r v 0)*
    cplLeafProduct (addrFam H) θ Q₂ (addrExt b [1]) (addrExt a [1]) (childVals r v 1)*
    cplLeafProduct (addrFam H) θ Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) (childVals r v 2)
  have hkernel : (fun θ => cplLeafProduct (addrFam H) θ (.type1 c Q₁ Q₂ Q₃) a b r) =
      (fun θ => Hk (θ a) θ) := by
    funext θ
    exact cplLeafProduct_type1 (addrFam H) θ c Q₁ Q₂ Q₃ a b r hab
  have hfreeze := addressAppAlong_freeze Z (L₁++L₂++L₃) (fun θ => θ a)
    (fun z hz θ x y => by
      apply update_of_ne
      intro he
      exact hroot (he.symm ▸ hz)) Hk θ
  rw [hkernel,hfreeze]
  exact addressAppAlong_three_source_blocks hd Q₁ Q₂ Q₃ hK hM hB hF Z _ _ _ _ _ _
    (hab.ext _ _) (hab.symm.ext _ _) (hab.ext _ _)
    (childVals r (θ a) 0) (childVals r (θ a) 1) (childVals r (θ a) 2) h₁₂ h₁₃ h₂₃ θ

end WaveTurbulence.RA1Leafwise
