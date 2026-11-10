/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceAddressLeading
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceAddressIndependence
public import WaveTurbulence.Foundations.Spine.RA1LW.ActualSingularSpatialBound

/-! # Geometric spatial control of the actual complete address fold -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links ApproxNT

/-- The exact original source identity holds at every initial address
state, since all chosen parameters are integrated. -/
theorem addressAppAlong_source_at_eq_singInt {d : ℕ} (hd : 3 ≤ d)
    {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) (hn : 0 < Q.links.length)
    {K M : ℕ} {H : LGSpine.LeafProfiles 2 d} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ a, Fourier.spatialNorm K M (leafFam hQ hG H a) ≤ ENNReal.ofReal B))
    (Z : Finset (Fin 2 × TTree.Path)) (k : Mom d)
    (θ : Fin 2 × TTree.Path → Mom d × Mom d) :
    addressAppAlong Z (Q.links.map Prod.fst)
      (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k) θ =
    singInt (markedLinkIndices Q Z) (fun x y =>
      ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a)) := by
  exact (addressAppAlong_cplLeafProduct_initial_independent Z (addrFam H) Q (0,[]) (1,[]) k
    indep_roots θ 0).trans
    (addressAppAlong_source_eq_singInt hd hQ hG hn hK hM hB hF Z k)

/-- The actual complete source address fold has geometric full spatial
control, uniformly in its initial address parameters. This is the
analytic fold estimate before recursive Mstar identification. -/
theorem source_address_fold_spatial_bound {d : ℕ} (hd : 3 ≤ d) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      0 < Q.links.length → ∀ H : LGSpine.LeafProfiles 2 d,
      (∀ a, Fourier.spatialNorm (40*d) (40*d) (leafFam hQ hG H a) ≤ ENNReal.ofReal B) →
      ∀ Z : Finset (Fin 2 × TTree.Path),
      ∀ θ : Fin 2 × TTree.Path → Mom d × Mom d,
      Fourier.spatialNorm (30*d) (30*d) (fun k =>
        addressAppAlong Z (Q.links.map Prod.fst)
          (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k) θ) ≤
        ENNReal.ofReal (C*C^Q.links.length) := by
  obtain ⟨C,hC,hbound⟩ := actual_source_singular_spatial_bound hd hB
  refine ⟨C,hC,?_⟩
  intro G Q hQ hG hn H hF Z θ
  have he : (fun k => addressAppAlong Z (Q.links.map Prod.fst)
      (fun θ => cplLeafProduct (addrFam H) θ Q (0,[]) (1,[]) k) θ) =
      (fun k => singInt (markedLinkIndices Q Z) (fun x y =>
        ∏ a, leafFam hQ hG H a ((coupleMomentumData hQ hG).inputMomentum k
          (fun j i => if i=0 then x j else y j) a))) := by
    funext k
    exact addressAppAlong_source_at_eq_singInt hd hQ hG hn (by omega) (by omega) hB hF Z k θ
  rw [he]
  exact hbound G Q hQ hG hn H hF (markedLinkIndices Q Z)

end WaveTurbulence.RA1Leafwise
