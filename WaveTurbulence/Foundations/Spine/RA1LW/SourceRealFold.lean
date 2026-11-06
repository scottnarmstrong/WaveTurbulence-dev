/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceFoldReal

/-! # Real-valued actual source fold and its original geometric spatial bound -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Reg TTree

/-- The real part of the complete original source couple fold at zero
initial parameters. Reality is proved below from actual PV convergence. -/
@[expose] def realCplFold {d w : ℕ} (H : Fin w × TTree.Path → Mom d → ℝ) (Q : RegCpl)
    (Z : Finset (Fin w × Path)) (a b : Fin w × Path) (k : Mom d) : ℝ :=
  (addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
    (fun θ => cplLeafProduct (addrFam H) θ Q a b k) 0).re

/-- Under the original finite input norm, complexification recovers the
complete actual source fold, at every initial parameter state. -/
theorem ofReal_realCplFold {d w : ℕ} (hd : 3 ≤ d)
    (Q : RegCpl) {K M : ℕ} {H : Fin w × TTree.Path → Mom d → ℝ} {B : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ z, Fourier.spatialNorm K M (addrFam H z) ≤ ENNReal.ofReal B))
    (Z : Finset (Fin w × Path)) (a b : Fin w × Path) (hab : Indep a b) (k : Mom d)
    (θ : Fin w × Path → Mom d × Mom d) :
    (realCplFold H Q Z a b k:ℂ) =
    addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
      (fun θ => cplLeafProduct (addrFam H) θ Q a b k) θ := by
  have he : (realCplFold H Q Z a b k:ℂ) =
      addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
        (fun θ => cplLeafProduct (addrFam H) θ Q a b k) 0 := by
    apply Complex.ext
    · rfl
    · exact (addressAppAlong_source_im_zero hd Q hK hM hB hF Z a b hab k 0).symm
  exact he.trans (addressAppAlong_cplLeafProduct_initial_independent Z
    (addrFam H) Q a b k hab 0 θ)

/-- Actual real child folds already satisfy the geometric spatial bound
before being identified with recursive Mstar. Constants precede every code. -/
theorem realCplFold_spatial_bound {d : ℕ} (hd : 3 ≤ d) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : RegCpl, ∀ (w : ℕ) (H : Fin w × TTree.Path → Mom d → ℝ),
      (∀ z, Fourier.spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal B) →
      ∀ (Z : Finset (Fin w × Path)) (a b : Fin w × Path), Indep a b →
      Fourier.spatialNorm (30*d) (30*d) (fun k => (realCplFold H Q Z a b k:ℂ)) ≤
        ENNReal.ofReal (C*C^Q.links.length) := by
  obtain ⟨C,hC,hbound⟩ := source_all_placed_fold_spatial_bound hd hB
  refine ⟨C,hC,?_⟩
  intro Q w H hF Z a b hab
  have he : (fun k => (realCplFold H Q Z a b k:ℂ)) =
      (fun k => addressAppAlong Z ((Q.linksAt a b).map Prod.fst)
        (fun θ => cplLeafProduct (addrFam H) θ Q a b k) 0) := by
    funext k
    exact ofReal_realCplFold hd Q (by omega) (by omega) hB hF Z a b hab k 0
  rw [he]
  exact hbound Q w H hF Z a b hab 0

end WaveTurbulence.RA1Leafwise
