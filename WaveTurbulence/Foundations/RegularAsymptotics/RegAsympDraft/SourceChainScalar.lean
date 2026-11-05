/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceMiniRoots
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceRealFold
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceBinaryRoot
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceTwoBlockScalar

/-! # Lawful scalar extraction through dominant paired chain folds -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Reg TTree Function

/-- The complete dominant chain fold admits scalar extraction. The proof
uses actual finite-norm child folds and their binary cutoff convergence;
it assumes neither recursive Nstar identities nor arbitrary PV linearity. -/
theorem addressAppAlong_chain_const_mul {d w : ℕ} (hd : 3 ≤ d)
    {F : Mom d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm (40*d) (40*d) (fun k => (F k:ℂ)) ≤ ENNReal.ofReal B)
    (X : RegChain) (hdom : X.dominant = true)
    (Z : Finset (Fin w × Path)) (ζ : ℤˣ) (a : Fin w × Path) (r : Mom d)
    (cont : Fin w × Path → Mom d) (c : ℂ)
    (θ : Fin w × Path → Mom d × Mom d) :
    addressAppAlong Z ((X.linksAt ζ a).map Prod.fst)
      (fun θ => c*chainLeafProduct (fun k => (F k:ℂ)) θ X ζ a r cont) θ =
    c*addressAppAlong Z ((X.linksAt ζ a).map Prod.fst)
      (fun θ => chainLeafProduct (fun k => (F k:ℂ)) θ X ζ a r cont) θ := by
  classical
  cases X with
  | nil => rfl
  | pair m Qr Qg inner rest =>
    cases inner with
    | pair mi Qri Qgi ii ri => simp [RegChain.dominant,RegChain.isNil] at hdom
    | nil =>
      have hrest : rest.dominant = true := (Bool.and_eq_true_iff.mp hdom).2
      let ar := (miniRedRoots m ζ a).1
      let br := (miniRedRoots m ζ a).2
      let ag := (miniGreenRoots m ζ a).1
      let bg := (miniGreenRoots m ζ a).2
      let ζs := slotSign (slotSign ζ m.c) m.lone
      let as := addrExt a [m.c,m.lone]
      let LR := (Qr.linksAt ar br).map Prod.fst
      let LG := (Qg.linksAt ag bg).map Prod.fst
      let LS := (rest.linksAt ζs as).map Prod.fst
      let HR := fun (v : Mom d × Mom d) θ => cplLeafProduct (fun k => (F k:ℂ)) θ Qr ar br
        (childVals r v m.red.1)
      let HG := fun (v : Mom d × Mom d) θ => cplLeafProduct (fun k => (F k:ℂ)) θ Qg ag bg
        (childVals r v m.green.1)
      let HS := fun θ => chainLeafProduct (fun k => (F k:ℂ)) θ rest ζs as r cont
      let S := addressAppAlong Z LS HS 0
      let f := realCplFold F Qr Z ar br
      let g := realCplFold F Qg Z ag bg
      have hnd : (a::(LR++LG++LS)).Nodup := by
        have hh := source_chain_chosen_nodup (.pair m Qr Qg .nil rest) ζ a
        simpa only [chain_linksAt_pair_nil_roots,List.map_cons,List.map_append] using hh
      have hroot := (List.nodup_cons.mp hnd).1
      have htail := (List.nodup_cons.mp hnd).2
      have hRGS := (List.nodup_append'.mp htail).2.2
      have hRG := (List.nodup_append'.mp (List.nodup_append'.mp htail).1).2.2
      have hRS : List.Disjoint LR LS := List.disjoint_left.mpr
        (fun _ hR hS => List.disjoint_left.mp hRGS (List.mem_append_left _ hR) hS)
      have hGS : List.Disjoint LG LS := List.disjoint_left.mpr
        (fun _ hG hS => List.disjoint_left.mp hRGS (List.mem_append_right _ hG) hS)
      have habr : Indep ar br := miniRedRoots_indep m ζ a
      have habg : Indep ag bg := miniGreenRoots_indep m ζ a
      obtain ⟨C,hC,hsp⟩ := realCplFold_spatial_bound hd hB
      let D := max (C*C^Qr.links.length) (C*C^Qg.links.length)
      have hD : 0 ≤ D := (mul_nonneg (zero_le_one.trans hC)
        (pow_nonneg (zero_le_one.trans hC) _)).trans (le_max_left _ _)
      have hf : Fourier.spatialNorm (30*d) (30*d) (fun k => (f k:ℂ)) ≤ ENNReal.ofReal D :=
        (hsp Qr F hF w Z ar br habr).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      have hg : Fourier.spatialNorm (30*d) (30*d) (fun k => (g k:ℂ)) ≤ ENNReal.ofReal D :=
        (hsp Qg F hF w Z ag bg habg).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
      have hcompute (c : ℂ) :
          addressAppAlong Z (((RegChain.pair m Qr Qg .nil rest).linksAt ζ a).map Prod.fst)
            (fun θ => c*chainLeafProduct (fun k => (F k:ℂ)) θ (.pair m Qr Qg .nil rest) ζ a r cont) θ =
          (2:ℂ)*(c*S)*((if a∈Z then pvResonantIntegral (binaryMomentumFunction m.c f g) r
            else resIntegral (binaryMomentumFunction m.c f g) r):ℝ) := by
        have hi (v : Mom d × Mom d) :
            addressAppAlong Z LS (fun θ => (c*HR v θ*HG v θ)*HS θ) =
            (fun θ => (c*HR v θ*HG v θ)*S) := by
          funext θ
          have hfree := addressAppAlong_freeze Z LS (fun θ => c*HR v θ*HG v θ)
            (fun z hz θ x y => by
              have hr := addressAppAlong_cplLeafProduct_update_of_not_mem Z []
                (fun k => (F k:ℂ)) Qr ar br (childVals r v m.red.1) habr z
                (fun h => List.disjoint_left.mp hRS h hz) θ (x,y)
              have hg := addressAppAlong_cplLeafProduct_update_of_not_mem Z []
                (fun k => (F k:ℂ)) Qg ag bg (childVals r v m.green.1) habg z
                (fun h => List.disjoint_left.mp hGS h hz) θ (x,y)
              change c*HR v (update θ z (x,y))*HG v (update θ z (x,y)) = c*HR v θ*HG v θ
              rw [show HR v (update θ z (x,y)) = HR v θ from hr,
                show HG v (update θ z (x,y)) = HG v θ from hg])
            (fun t θ => t*HS θ) θ
          rw [hfree]
          rw [addressAppAlong_chain_const_mul hd hB hF rest hrest Z ζs as r cont]
          rw [addressAppAlong_chainLeafProduct_initial_independent Z (fun k => (F k:ℂ))
            rest ζs as r cont θ 0]
        have ht (v : Mom d × Mom d) (θ : Fin w × Path → Mom d × Mom d) :
            addressAppAlong Z (LR++LG++LS) (fun θ => (c*HR v θ*HG v θ)*HS θ) θ =
            (c*S)*(f (childVals r v m.red.1)*g (childVals r v m.green.1):ℝ) := by
          rw [addressAppAlong_append,hi]
          have he : (fun θ => (c*HR v θ*HG v θ)*S) =
              (fun θ => ((c*S)*HR v θ)*HG v θ) := by
            funext θ
            ring
          rw [he]
          have hh := addressAppAlong_scalar_two_source_blocks hd Qr Qg
            (by omega) (by omega) hB hB hF hF Z ar br ag bg habr habg
            (childVals r v m.red.1) (childVals r v m.green.1) hRG (c*S) θ
          rw [hh]
          rw [← ofReal_realCplFold hd Qr (by omega) (by omega) hB hF Z ar br habr _ θ,
            ← ofReal_realCplFold hd Qg (by omega) (by omega) hB hF Z ag bg habg _ θ]
          simp only [Complex.ofReal_mul]
          ring
        have hkernel : (fun θ => c*chainLeafProduct (fun k => (F k:ℂ)) θ
              (.pair m Qr Qg .nil rest) ζ a r cont) =
            (fun θ => (c*HR (θ a) θ*HG (θ a) θ)*HS θ) := by
          funext θ
          rw [chainLeafProduct_pair_nil_roots]
          change c*(HR (θ a) θ*HG (θ a) θ*HS θ) = (c*HR (θ a) θ*HG (θ a) θ)*HS θ
          ring
        have htailfun : addressAppAlong Z (LR++LG++LS)
            (fun θ => c*chainLeafProduct (fun k => (F k:ℂ)) θ
              (.pair m Qr Qg .nil rest) ζ a r cont) =
            (fun θ => (c*S)*(f (childVals r (θ a) m.red.1)*g (childVals r (θ a) m.green.1):ℝ)) := by
          funext θ
          rw [hkernel]
          have hh := addressAppAlong_freeze Z (LR++LG++LS) (fun θ => θ a)
            (fun z hz θ x y => by
              apply update_of_ne
              intro he
              exact hroot (he.symm ▸ hz))
            (fun v θ => (c*HR v θ*HG v θ)*HS θ) θ
          rw [hh]
          exact ht (θ a) θ
        simp only [chain_linksAt_pair_nil_roots,List.map_cons,List.map_append,addressAppAlong]
        change addressAppStep Z a (addressAppAlong Z (LR++LG++LS)
          (fun θ => c*chainLeafProduct (fun k => (F k:ℂ)) θ
            (.pair m Qr Qg .nil rest) ζ a r cont)) θ = _
        rw [htailfun]
        exact addressAppStep_binary_source (by omega) (by omega) (by omega) hD hf hg m Z a r (c*S) θ
      rw [hcompute c]
      have h1 := hcompute 1
      simp only [one_mul] at h1
      rw [h1]
      ring
termination_by structural X

/-- A factor unchanged by the chosen chain parameters may be extracted
from the actual dominant-chain fold. This derives its variable-factor
law from freezing and the proved constant scalar law. -/
theorem addressAppAlong_mul_chain_source {d w : ℕ} (hd : 3 ≤ d)
    {F : Mom d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm (40*d) (40*d) (fun k => (F k:ℂ)) ≤ ENNReal.ofReal B)
    (X : RegChain) (hdom : X.dominant = true)
    (Z : Finset (Fin w × Path)) (ζ : ℤˣ) (a : Fin w × Path) (r : Mom d)
    (cont : Fin w × Path → Mom d)
    (g : (Fin w × Path → Mom d × Mom d) → ℂ)
    (hg : ∀ z ∈ (X.linksAt ζ a).map Prod.fst, ∀ θ x y,
      g (update θ z (x,y)) = g θ)
    (θ : Fin w × Path → Mom d × Mom d) :
    addressAppAlong Z ((X.linksAt ζ a).map Prod.fst)
      (fun θ => g θ*chainLeafProduct (fun k => (F k:ℂ)) θ X ζ a r cont) θ =
    g θ*addressAppAlong Z ((X.linksAt ζ a).map Prod.fst)
      (fun θ => chainLeafProduct (fun k => (F k:ℂ)) θ X ζ a r cont) θ := by
  rw [addressAppAlong_freeze Z _ g hg
    (fun c θ => c*chainLeafProduct (fun k => (F k:ℂ)) θ X ζ a r cont) θ]
  exact addressAppAlong_chain_const_mul hd hB hF X hdom Z ζ a r cont (g θ) θ

end WaveTurbulence.RegAsymp
