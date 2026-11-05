/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.TreeFam
public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeLeadingSingularExchange
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeLeadingScalarControl
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeOriginalSingular

/-! # Literal Nstar identifies the actual leading spatial mixture at every order -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ApproxNT Finset Reg

/-- The actual leading mixture equals the original source singular integral also at order zero. -/
theorem treeLeadingSpatialProfile_eq_singInt_source_all {d K M : ℕ} {G : Garden 1} {X : RegChain}
    (hd : 3 ≤ d) (hX : X.DecodesTree G)
    (J : Finset (Fin (X.treeLinks (G.sig 0)).length))
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {B C : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^(X.treeLinks (G.sig 0)).length) (k : Mom d) :
    treeLeadingSpatialProfile hX J f S k = singInt J (fun x y =>
      (treeCarrier hX).sourceLeafWeight f k (fun j i => if i=0 then x j else y j)) := by
  by_cases hn : 0 < (X.treeLinks (G.sig 0)).length
  · exact treeLeadingSpatialProfile_eq_singInt_source hd hX hn J f hK hM hB hf S hcover hS k
  · have hn0 : (X.treeLinks (G.sig 0)).length=0 := by omega
    rw [tree_singInt_eq_eval_of_zero hn0]
    unfold treeLeadingSpatialProfile
    have he : treeNormalizedScalar hX (fun _ β γ z => singInt J (halfCellAmplitude z β γ)) S (0,0) =
        treePointScalar hX 0 0 S := by
      funext u
      dsimp only [treePointScalar,treeNormalizedScalar]
      rw [tree_singInt_eq_eval_of_zero hn0]
    rw [he]
    exact tree_point_mixture_eq_source hX 0 0 f hK hM hB hf S hcover hS k

/-- The ACTUAL leading moving-root mixture is2 per original link times literal Nstar,
with only the source dominant/special and original finite input norm premises. -/
theorem treeLeadingSpatialProfile_eq_Nstar {d : ℕ} {G : Garden 1} {X : RegChain}
    (hd : 3 ≤ d) (hX : X.DecodesTree G) (hdom : X.dominant=true)
    {H : LGSpine.LeafProfiles 1 d} {B C : ℝ} (hB : 0 ≤ B)
    (hF : ∀ z, Fourier.spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal B)
    (Z : Finset (Fin 1 × TTree.Path)) (hZ : IsSpecialSet (X.treeLinks (G.sig 0)) Z)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^(X.treeLinks (G.sig 0)).length) (k : Mom d) :
    treeLeadingSpatialProfile hX (univ.filter (fun j => treeChosen X (G.sig 0) j ∈ Z))
      (treeInputFam G H) S k =
      (2:ℂ)^(X.treeLinks (G.sig 0)).length*(LGSpine.LeafApp.chainNstar H Z X (G.sig 0) ((0:Fin 1),[]) k:ℂ) := by
  rw [treeLeadingSpatialProfile_eq_singInt_source_all hd hX _ (treeInputFam G H)
    (by omega) (by omega) hB (fun _ => hF _) S hcover hS k]
  exact tree_original_source_singInt_eq_Nstar hd hX hdom hB hF Z hZ k

end WaveTurbulence.RA1Leafwise
