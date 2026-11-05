/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceUniformFoldNorm
public import WaveTurbulence.Foundations.RegAsymp.RealSingularOperators

/-! # Actual source couple folds are real before recursive identification -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Reg TTree ApproxNT

private theorem list_prod_im_zero (L : List ℂ) (hL : ∀ z ∈ L, z.im = 0) : L.prod.im = 0 := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    simp only [List.prod_cons,Complex.mul_im,hL z List.mem_cons_self,
      ih (fun v hv => hL v (List.mem_cons_of_mem _ hv)),mul_zero,zero_mul,add_zero]

/-- Every partial original source fold remains real. The PV branch uses
actual cutoff convergence from the finite input norm at each remaining node. -/
theorem addressAppAlong_placed_source_im_zero {d w : ℕ} (hd : 3 ≤ d)
    (Q : RegCpl) {K M : ℕ} {F : Mom d → ℝ} {B : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M (fun k => (F k:ℂ)) ≤ ENNReal.ofReal B)
    (Z : Finset (Fin w × Path)) (L : List (Fin Q.links.length)) (hL : L.Nodup)
    (a b : Fin w × Path) (hab : Indep a b) (k : Mom d)
    (θ : Fin w × Path → Mom d × Mom d) :
    (addressAppAlong Z ((L.map (chosenNode Q)).map (rootPlacement a b))
      (fun θ => cplLeafProduct (fun k => (F k:ℂ)) θ Q a b k) θ).im = 0 := by
  classical
  induction L generalizing θ with
  | nil =>
    change (cplLeafProduct (fun k => (F k:ℂ)) θ Q a b k).im = 0
    apply list_prod_im_zero
    intro z hz
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hz
    rfl
  | cons j L ih =>
    obtain ⟨hj,hL⟩ := List.nodup_cons.mp hL
    simp only [List.map_cons,addressAppAlong,addressAppStep]
    have hreal (x y : Mom d) := ih hL (Function.update θ
      (rootPlacement a b (chosenNode Q j)) (x,y))
    split_ifs
    · exact pvOp_im_eq_zero_of_tendsto _ hreal
        (tendsto_pvTrunc_placed_source_block hd (Reg.decodedCouple_decodes Q)
          (Reg.decodedCouple_decodes Q).1 (by have hjn := j.isLt; omega)
          hK hM hB hF Z L hL j hj a b hab k θ)
    · exact deltaInner_im_eq_zero _ hreal

/-- A complete actual source fold is real at every initial parameter state. -/
theorem addressAppAlong_source_im_zero {d w : ℕ} (hd : 3 ≤ d)
    (Q : RegCpl) {K M : ℕ} {F : Mom d → ℝ} {B : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M (fun k => (F k:ℂ)) ≤ ENNReal.ofReal B)
    (Z : Finset (Fin w × Path)) (a b : Fin w × Path) (hab : Indep a b) (k : Mom d)
    (θ : Fin w × Path → Mom d × Mom d) :
    (addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
      (fun θ => cplLeafProduct (fun k => (F k:ℂ)) θ Q a b k) θ).im = 0 := by
  have hlist : ((List.finRange Q.links.length).map (chosenNode Q)).map (rootPlacement a b) =
      (Q.linksAt a b).map Prod.fst := by
    rw [map_finRange_chosenNode,cpl_links_rootPlacement,List.map_map,List.map_map]
    rfl
  have hh := addressAppAlong_placed_source_im_zero hd Q hK hM hB hF Z
    (List.finRange Q.links.length) (List.nodup_finRange _) a b hab k θ
  rw [hlist] at hh
  exact hh

end WaveTurbulence.RegAsymp
