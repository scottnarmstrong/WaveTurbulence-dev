/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceChainScalar

/-! # Exact type2 source factorization into two chains and the lone couple -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Reg TTree Function

/-- The original type2 source fold factors into its two complete paired
chain folds and its complete lone-couple fold. All singular operator
orders are preserved, and chain scalar laws use the original input norm. -/
theorem addressAppAlong_type2 {d w : ℕ} (hd : 3 ≤ d)
    {F : Mom d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm (40*d) (40*d) (fun k => (F k:ℂ)) ≤ ENNReal.ofReal B)
    (Xp Xm : RegChain) (hp : Xp.dominant = true) (hm : Xm.dominant = true) (Qlp : RegCpl)
    (Z : Finset (Fin w × Path)) (a b : Fin w × Path) (hab : Indep a b) (r : Mom d)
    (θ : Fin w × Path → Mom d × Mom d) :
    addressAppAlong Z (((RegCpl.type2 Xp Xm Qlp).linksAt a b).map Prod.fst)
      (fun θ => cplLeafProduct (fun k => (F k:ℂ)) θ (.type2 Xp Xm Qlp) a b r) θ =
    addressAppAlong Z ((Xp.linksAt 1 a).map Prod.fst)
      (fun θ => chainLeafProduct (fun k => (F k:ℂ)) θ Xp 1 a r (fun _ => r)) θ *
    addressAppAlong Z ((Xm.linksAt (-1) b).map Prod.fst)
      (fun θ => chainLeafProduct (fun k => (F k:ℂ)) θ Xm (-1) b r (fun _ => r)) θ *
    addressAppAlong Z ((Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)).map Prod.fst)
      (fun θ => cplLeafProduct (fun k => (F k:ℂ)) θ Qlp
        (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r) θ := by
  let LP := (Xp.linksAt 1 a).map Prod.fst
  let LM := (Xm.linksAt (-1) b).map Prod.fst
  let LQ := (Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)).map Prod.fst
  let HP := fun θ => chainLeafProduct (fun k => (F k:ℂ)) θ Xp 1 a r (fun _ => r)
  let HM := fun θ => chainLeafProduct (fun k => (F k:ℂ)) θ Xm (-1) b r (fun _ => r)
  let HQ := fun θ => cplLeafProduct (fun k => (F k:ℂ)) θ Qlp
    (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r
  let RM := addressAppAlong Z LM HM
  let RQ := addressAppAlong Z LQ HQ
  have hnd : (LP++LM++LQ).Nodup := by
    have hh := source_chosen_nodup (.type2 Xp Xm Qlp) a b hab
    simpa only [RegCpl.linksAt,List.map_append] using hh
  have hPMQ := (List.nodup_append'.mp hnd).2.2
  have hPM := (List.nodup_append'.mp (List.nodup_append'.mp hnd).1).2.2
  have hPQ : List.Disjoint LP LQ := List.disjoint_left.mpr
    (fun _ hP hQ => List.disjoint_left.mp hPMQ (List.mem_append_left _ hP) hQ)
  have hMQ : List.Disjoint LM LQ := List.disjoint_left.mpr
    (fun _ hM hQ => List.disjoint_left.mp hPMQ (List.mem_append_right _ hM) hQ)
  have hcP (L : List (Fin w × Path)) (z) (hz : z ∉ LP) (θ) (x y : Mom d) :
      addressAppAlong Z L HP (update θ z (x,y)) = addressAppAlong Z L HP θ :=
    addressAppAlong_chainLeafProduct_update_of_not_mem Z L (fun k => (F k:ℂ)) Xp 1 a r
      (fun _ => r) z hz θ (x,y)
  have hcM (L : List (Fin w × Path)) (z) (hz : z ∉ LM) (θ) (x y : Mom d) :
      addressAppAlong Z L HM (update θ z (x,y)) = addressAppAlong Z L HM θ :=
    addressAppAlong_chainLeafProduct_update_of_not_mem Z L (fun k => (F k:ℂ)) Xm (-1) b r
      (fun _ => r) z hz θ (x,y)
  have hcQ (L : List (Fin w × Path)) (z) (hz : z ∉ LQ) (θ) (x y : Mom d) :
      addressAppAlong Z L HQ (update θ z (x,y)) = addressAppAlong Z L HQ θ :=
    addressAppAlong_cplLeafProduct_update_of_not_mem Z L (fun k => (F k:ℂ)) Qlp _ _ r
      (hab.ext _ _) z hz θ (x,y)
  have hiQ : addressAppAlong Z LQ (fun θ => HP θ*HM θ*HQ θ) =
      (fun θ => HP θ*HM θ*RQ θ) := by
    funext θ
    apply addressAppAlong_mul_placed_source hd Qlp (by omega) (by omega) hB hF Z _ _ (hab.ext _ _) r
    intro z hz θ x y
    rw [show HP (update θ z (x,y)) = HP θ from
      hcP [] z (fun h => List.disjoint_left.mp hPQ h hz) θ x y,
      show HM (update θ z (x,y)) = HM θ from
      hcM [] z (fun h => List.disjoint_left.mp hMQ h hz) θ x y]
  have hiM : addressAppAlong Z LM (fun θ => HP θ*HM θ*RQ θ) =
      (fun θ => (HP θ*RQ θ)*RM θ) := by
    have hs : (fun θ => HP θ*HM θ*RQ θ) = (fun θ => (HP θ*RQ θ)*HM θ) := by
      funext θ
      ring
    rw [hs]
    funext θ
    apply addressAppAlong_mul_chain_source hd hB hF Xm hm Z (-1) b r (fun _ => r)
    intro z hz θ x y
    rw [show HP (update θ z (x,y)) = HP θ from
      hcP [] z (fun h => List.disjoint_left.mp hPM h hz) θ x y,
      show RQ (update θ z (x,y)) = RQ θ from
      hcQ LQ z (List.disjoint_left.mp hMQ hz) θ x y]
  have hkernel : (fun θ => cplLeafProduct (fun k => (F k:ℂ)) θ (.type2 Xp Xm Qlp) a b r) =
      (fun θ => HP θ*HM θ*HQ θ) := by
    funext θ
    exact cplLeafProduct_type2 (fun k => (F k:ℂ)) θ Xp Xm Qlp a b r hab
  rw [hkernel,RegCpl.linksAt,List.map_append,List.map_append]
  change addressAppAlong Z (LP++LM++LQ) (fun θ => HP θ*HM θ*HQ θ) θ =
    addressAppAlong Z LP HP θ*RM θ*RQ θ
  rw [addressAppAlong_append,addressAppAlong_append,hiQ,hiM]
  have hs : (fun θ => HP θ*RQ θ*RM θ) = (fun θ => (RM θ*RQ θ)*HP θ) := by
    funext θ
    ring
  rw [hs]
  have hh := addressAppAlong_mul_chain_source hd hB hF Xp hp Z 1 a r (fun _ => r)
    (fun θ => RM θ*RQ θ) (fun z hz θ x y => by
      rw [show RM (update θ z (x,y)) = RM θ from
        hcM LM z (List.disjoint_left.mp hPM hz) θ x y,
        show RQ (update θ z (x,y)) = RQ θ from
        hcQ LQ z (List.disjoint_left.mp hPQ hz) θ x y]) θ
  exact hh.trans (by ring)

end WaveTurbulence.RegAsymp
