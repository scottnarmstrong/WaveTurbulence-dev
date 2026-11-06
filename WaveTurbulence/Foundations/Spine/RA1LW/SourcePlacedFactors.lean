/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.SourcePlacedPV

/-! # Independent factors through source blocks at actual child placements -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Links Function

/-- A factor unchanged by the integrated source parameters can be
extracted from their actual singular block. The PV convergence used here
is proved from the original input norm at every remaining source node. -/
theorem addressAppAlong_mul_placed_source_block {d w : ℕ} (hd : 3 ≤ d)
    {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) (hn : 0 < Q.links.length)
    {K M : ℕ} {H : Fin w × TTree.Path → Mom d → ℝ} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ z, Fourier.spatialNorm K M (addrFam H z) ≤ ENNReal.ofReal B))
    (Z : Finset (Fin w × TTree.Path)) (L : List (Fin Q.links.length))
    (hL : L.Nodup) (a b : Fin w × TTree.Path) (hab : Indep a b) (k : Mom d)
    (g : (Fin w × TTree.Path → Mom d × Mom d) → ℂ)
    (hg : ∀ j ∈ L, ∀ θ x y, g (update θ (rootPlacement a b (chosenNode Q j)) (x,y)) = g θ)
    (θ : Fin w × TTree.Path → Mom d × Mom d) :
    addressAppAlong Z ((L.map (chosenNode Q)).map (rootPlacement a b))
      (fun θ => g θ*cplLeafProduct (addrFam H) θ Q a b k) θ =
    g θ*addressAppAlong Z ((L.map (chosenNode Q)).map (rootPlacement a b))
      (fun θ => cplLeafProduct (addrFam H) θ Q a b k) θ := by
  classical
  induction L generalizing θ with
  | nil => rfl
  | cons j L ih =>
    obtain ⟨hj,hL⟩ := List.nodup_cons.mp hL
    have htail : ∀ θ, addressAppAlong Z ((L.map (chosenNode Q)).map (rootPlacement a b))
        (fun θ => g θ*cplLeafProduct (addrFam H) θ Q a b k) θ =
        g θ*addressAppAlong Z ((L.map (chosenNode Q)).map (rootPlacement a b))
          (fun θ => cplLeafProduct (addrFam H) θ Q a b k) θ := by
      intro θ
      exact ih hL (fun i hi => hg i (List.mem_cons_of_mem _ hi)) θ
    simp only [List.map_cons,addressAppAlong,addressAppStep]
    have he : (fun x y => addressAppAlong Z ((L.map (chosenNode Q)).map (rootPlacement a b))
        (fun θ => g θ*cplLeafProduct (addrFam H) θ Q a b k)
        (update θ (rootPlacement a b (chosenNode Q j)) (x,y))) =
        (fun x y => g θ*addressAppAlong Z ((L.map (chosenNode Q)).map (rootPlacement a b))
          (fun θ => cplLeafProduct (addrFam H) θ Q a b k)
          (update θ (rootPlacement a b (chosenNode Q j)) (x,y))) := by
      funext x y
      rw [htail,hg j List.mem_cons_self θ x y]
    rw [he]
    split_ifs
    · exact pvOp_const_mul_of_tendsto (g θ)
        (tendsto_pvTrunc_placed_source_block hd hQ hG hn hK hM hB hF Z L hL j hj a b hab k θ)
    · exact deltaInner_const_mul (g θ) _

/-- Complete child-block factor extraction for every literal couple code.
The canonical decoded garden supplies the source typing data internally. -/
theorem addressAppAlong_mul_placed_source_all {d w : ℕ} (hd : 3 ≤ d)
    (Q : RegCpl) (hn : 0 < Q.links.length)
    {K M : ℕ} {H : Fin w × TTree.Path → Mom d → ℝ} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ z, Fourier.spatialNorm K M (addrFam H z) ≤ ENNReal.ofReal B))
    (Z : Finset (Fin w × TTree.Path)) (a b : Fin w × TTree.Path) (hab : Indep a b) (k : Mom d)
    (g : (Fin w × TTree.Path → Mom d × Mom d) → ℂ)
    (hg : ∀ z ∈ (Q.linksAt a b).map Prod.fst, ∀ θ x y,
      g (update θ z (x,y)) = g θ)
    (θ : Fin w × TTree.Path → Mom d × Mom d) :
    addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
      (fun θ => g θ*cplLeafProduct (addrFam H) θ Q a b k) θ =
    g θ*addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
      (fun θ => cplLeafProduct (addrFam H) θ Q a b k) θ := by
  have hlist : ((List.finRange Q.links.length).map (chosenNode Q)).map (rootPlacement a b) =
      (Q.linksAt a b).map Prod.fst := by
    rw [map_finRange_chosenNode,cpl_links_rootPlacement,List.map_map,List.map_map]
    rfl
  have hh := addressAppAlong_mul_placed_source_block hd (Reg.decodedCouple_decodes Q)
    (Reg.decodedCouple_decodes Q).1 hn hK hM hB hF Z
    (List.finRange Q.links.length) (List.nodup_finRange _) a b hab k g
    (fun j _ θ x y => hg (rootPlacement a b (chosenNode Q j)) (by
      rw [← hlist]
      exact List.mem_map.mpr ⟨chosenNode Q j,
        List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩,rfl⟩) θ x y) θ
  rw [hlist] at hh
  exact hh

/-- Complete child-block factor extraction also includes empty codes;
there are then no singular operators to apply. -/
theorem addressAppAlong_mul_placed_source {d w : ℕ} (hd : 3 ≤ d)
    (Q : RegCpl)
    {K M : ℕ} {H : Fin w × TTree.Path → Mom d → ℝ} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ z, Fourier.spatialNorm K M (addrFam H z) ≤ ENNReal.ofReal B))
    (Z : Finset (Fin w × TTree.Path)) (a b : Fin w × TTree.Path) (hab : Indep a b) (k : Mom d)
    (g : (Fin w × TTree.Path → Mom d × Mom d) → ℂ)
    (hg : ∀ z ∈ (Q.linksAt a b).map Prod.fst, ∀ θ x y,
      g (update θ z (x,y)) = g θ)
    (θ : Fin w × TTree.Path → Mom d × Mom d) :
    addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
      (fun θ => g θ*cplLeafProduct (addrFam H) θ Q a b k) θ =
    g θ*addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
      (fun θ => cplLeafProduct (addrFam H) θ Q a b k) θ := by
  by_cases hn : 0 < Q.links.length
  · exact addressAppAlong_mul_placed_source_all hd Q hn hK hM hB hF Z a b hab k g hg θ
  · have hn0 : Q.links.length = 0 := by omega
    have hnil : Q.linksAt a b = [] := by
      rw [cpl_links_rootPlacement,List.eq_nil_of_length_eq_zero hn0,List.map_nil]
    rw [hnil,List.map_nil]
    rfl


end WaveTurbulence.RA1Leafwise
