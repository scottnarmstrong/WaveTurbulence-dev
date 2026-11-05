/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeAddressSingular
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceMstarIdentification

/-! # The original tree continuum singular integral is the literal recursive Nstar -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Reg TTree ApproxNT Finset IncohInst

/-- Two per original link is the exact normalization of the original tree singular
integral and the literal Nstar. Both root signs and order zero are included. -/
theorem tree_original_source_singInt_eq_Nstar {d : ℕ} (hd : 3 ≤ d)
    {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) (hdom : X.dominant = true)
    {F : Mom d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm (40*d) (40*d) (fun k => (F k:ℂ)) ≤ ENNReal.ofReal B)
    (Z : Finset (Fin 1 × Path)) (hZ : IsSpecialSet (X.treeLinks (G.sig 0)) Z) (k : Mom d) :
    singInt (univ.filter (fun j => treeChosen X (G.sig 0) j ∈ Z)) (fun x y =>
      (treeCarrier hX).sourceLeafWeight (fun _ k => (F k:ℂ)) k
        (fun j i => if i=0 then x j else y j)) =
      (2:ℂ)^(X.treeLinks (G.sig 0)).length*(X.Nstar F Z (G.sig 0) ((0:Fin 1),[]) k:ℂ) := by
  rw [← tree_addressAppAlong_source_eq_singInt hX]
  exact addressAppAlong_chain_eq_Nstar hd hB hF X hdom Z (G.sig 0) ((0:Fin 1),[])
    (fun z _ hz => hZ z hz) k (fun _ => k) 0

end WaveTurbulence.RegAsymp
