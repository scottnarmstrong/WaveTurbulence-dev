/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceType1Block

/-! # Actual type1 source recursion after its child singular blocks -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Reg TTree Function

/-- A type1 root cannot be special: its partner is the independent
opposite root, and all other chosen nodes are distinct from it. -/
theorem type1_root_not_mem_special {w : ℕ} (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl)
    (a b : Fin w × Path) (hab : Indep a b) (Z : Finset (Fin w × Path))
    (hZ : IsSpecialSet ((RegCpl.type1 c Q₁ Q₂ Q₃).linksAt a b) Z) : a ∉ Z := by
  intro ha
  obtain ⟨i,hi⟩ := hZ a ha
  have hnd := source_chosen_nodup (.type1 c Q₁ Q₂ Q₃) a b hab
  simp only [RegCpl.linksAt,List.map_cons,List.map_append] at hnd
  have hroot := (List.nodup_cons.mp hnd).1
  simp only [RegCpl.linksAt,List.mem_cons] at hi
  rcases hi with he | ht
  · have hb : addrExt a [i] = b := congrArg Prod.snd he
    exact hab.1 (hb ▸ under_ext a [i])
  · apply hroot
    simpa only [List.map_append] using
      (List.mem_map.mpr ⟨(a,addrExt a [i]),ht,rfl⟩ :
        a ∈ (Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0]) ++
          Q₂.linksAt (addrExt b [1]) (addrExt a [1]) ++
          Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2])).map Prod.fst)

/-- The exact type1 root calculation needs only that this root is
unmarked; marks outside the sub-code remain arbitrary. -/
theorem addressAppAlong_type1_root_unmarked {d w : ℕ} (hd : 3 ≤ d)
    (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl)
    {K M : ℕ} {H : Fin w × TTree.Path → Mom d → ℝ} {B : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ z, Fourier.spatialNorm K M (addrFam H z) ≤ ENNReal.ofReal B))
    (Z : Finset (Fin w × Path)) (a b : Fin w × Path) (hab : Indep a b) (r : Mom d)
    (hroot : a ∉ Z)
    (θ : Fin w × Path → Mom d × Mom d) :
    addressAppAlong Z (((RegCpl.type1 c Q₁ Q₂ Q₃).linksAt a b).map Prod.fst)
      (fun θ => cplLeafProduct (addrFam H) θ (.type1 c Q₁ Q₂ Q₃) a b r) θ =
    NTSP.deltaInner (fun x y =>
      addressAppAlong Z ((Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0])).map Prod.fst)
        (fun θ' => cplLeafProduct (addrFam H) θ' Q₁ (addrExt a [0]) (addrExt b [c.partner 0])
          (childVals r (x,y) 0)) 0 *
      addressAppAlong Z ((Q₂.linksAt (addrExt b [1]) (addrExt a [1])).map Prod.fst)
        (fun θ' => cplLeafProduct (addrFam H) θ' Q₂ (addrExt b [1]) (addrExt a [1])
          (childVals r (x,y) 1)) 0 *
      addressAppAlong Z ((Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2])).map Prod.fst)
        (fun θ' => cplLeafProduct (addrFam H) θ' Q₃ (addrExt a [2]) (addrExt b [c.partner 2])
          (childVals r (x,y) 2)) 0) := by
  simp only [RegCpl.linksAt,List.map_cons,List.map_append,addressAppAlong,addressAppStep,
    ite_eq_right hroot]
  apply congrArg NTSP.deltaInner
  funext x y
  rw [addressAppAlong_type1_children hd c Q₁ Q₂ Q₃ hK hM hB hF Z a b hab r]
  simp only [update_self]
  rw [addressAppAlong_cplLeafProduct_initial_independent Z (addrFam H) Q₁ _ _ _ (hab.ext _ _)
      (update θ a (x,y)) 0,
    addressAppAlong_cplLeafProduct_initial_independent Z (addrFam H) Q₂ _ _ _ (hab.symm.ext _ _)
      (update θ a (x,y)) 0,
    addressAppAlong_cplLeafProduct_initial_independent Z (addrFam H) Q₃ _ _ _ (hab.ext _ _)
      (update θ a (x,y)) 0]

end WaveTurbulence.RA1Leafwise
