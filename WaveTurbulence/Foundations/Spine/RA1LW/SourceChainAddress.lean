/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceChainChosen
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceAddressIndependence

/-! # Parameter dependence of the original paired chain singular folds -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Reg TTree Function

/-- An actual folded paired-chain kernel only depends on its own chosen
parameters. No excluded continuation input is inserted. -/
theorem addressAppAlong_chainLeafProduct_congr_params {d w : ℕ}
    (Z : Finset (Fin w × Path)) (L : List (Fin w × Path))
    (H : Fin w × TTree.Path → Mom d → ℝ) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (r : Mom d)
    (cont : Fin w × Path → Mom d) (θ θ' : Fin w × Path → Mom d × Mom d)
    (hθ : ∀ l ∈ X.linksAt ζ a, θ l.1 = θ' l.1) :
    addressAppAlong Z L (fun θ => chainLeafProduct (addrFam H) θ X ζ a r cont) θ =
      addressAppAlong Z L (fun θ => chainLeafProduct (addrFam H) θ X ζ a r cont) θ' := by
  apply addressAppAlong_congr_on Z L (Set.range (fun l : {l // l ∈ X.linksAt ζ a} => l.val.1))
  · intro v v' hv
    apply chainLeafProduct_congr_params (addrFam H) v v' X ζ a r cont cont
    intro l hl
    exact hv l.1 ⟨⟨l,hl⟩,rfl⟩
  · intro z hz
    obtain ⟨l,rfl⟩ := hz
    exact hθ l.val l.property

/-- The complete actual paired-chain fold forgets all initial address
parameters. This does not require a general PV-Fubini theorem. -/
theorem addressAppAlong_chainLeafProduct_initial_independent {d w : ℕ}
    (Z : Finset (Fin w × Path)) (H : Fin w × TTree.Path → Mom d → ℝ) (X : RegChain)
    (ζ : ℤˣ) (a : Fin w × Path) (r : Mom d) (cont : Fin w × Path → Mom d)
    (θ θ' : Fin w × Path → Mom d × Mom d) :
    addressAppAlong Z ((X.linksAt ζ a).map Prod.fst)
      (fun θ => chainLeafProduct (addrFam H) θ X ζ a r cont) θ =
    addressAppAlong Z ((X.linksAt ζ a).map Prod.fst)
      (fun θ => chainLeafProduct (addrFam H) θ X ζ a r cont) θ' := by
  apply addressAppAlong_congr_remaining Z _
    (Set.range (fun l : {l // l ∈ X.linksAt ζ a} => l.val.1))
  · intro v v' hv
    apply chainLeafProduct_congr_params (addrFam H) v v' X ζ a r cont cont
    intro l hl
    exact hv l.1 ⟨⟨l,hl⟩,rfl⟩
  · intro z hz hn
    obtain ⟨l,rfl⟩ := hz
    exact (hn (List.mem_map.mpr ⟨l.val,l.property,rfl⟩)).elim

/-- A parameter outside the original chain links cannot change its
paired leaf kernel, including after any folded source block. -/
theorem addressAppAlong_chainLeafProduct_update_of_not_mem {d w : ℕ}
    (Z : Finset (Fin w × Path)) (L : List (Fin w × Path))
    (H : Fin w × TTree.Path → Mom d → ℝ) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (r : Mom d)
    (cont : Fin w × Path → Mom d) (z : Fin w × Path)
    (hz : z ∉ (X.linksAt ζ a).map Prod.fst)
    (θ : Fin w × Path → Mom d × Mom d) (v : Mom d × Mom d) :
    addressAppAlong Z L (fun θ => chainLeafProduct (addrFam H) θ X ζ a r cont) (update θ z v) =
      addressAppAlong Z L (fun θ => chainLeafProduct (addrFam H) θ X ζ a r cont) θ := by
  classical
  apply addressAppAlong_chainLeafProduct_congr_params Z L H X ζ a r cont
  intro l hl
  apply update_of_ne
  intro he
  exact hz (List.mem_map.mpr ⟨l,hl,he⟩)

end WaveTurbulence.RA1Leafwise
