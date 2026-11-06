/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceSpecialRestriction

/-! # Distinct chosen nodes in arbitrary placed source chains -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Reg TTree

/-- Every chain branching node occurs in just one original link, at any
root sign and placement. This follows from the actual branch count. -/
theorem source_chain_links_flat_nodup {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    (flatPairs (X.linksAt ζ a)).Nodup := by
  classical
  apply nodup_of_card
  have hb := chain_branchAddresses X ζ .leaf a
  simp only [branchAddresses_leaf,Finset.union_empty] at hb
  rw [flatPairs_toFinset,flatPairs_length,← hb,card_branchAddresses,code_plug_order]
  have hn := chain_linksAt_length X ζ a
  change X.size+0 = 2*(X.linksAt ζ a).length
  omega

/-- The chosen-node list of every placed source chain has no repetitions. -/
theorem source_chain_chosen_nodup {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    ((X.linksAt ζ a).map Prod.fst).Nodup := by
  have hnd := source_chain_links_flat_nodup X ζ a
  refine List.Nodup.sublist ?_ hnd
  clear hnd
  induction X.linksAt ζ a with
  | nil => simp only [List.map_nil,flatPairs,List.flatMap_nil,List.Sublist.refl]
  | cons p L ih =>
    simp only [List.map_cons,flatPairs,List.flatMap_cons,List.cons_append] at ih ⊢
    exact List.Sublist.cons_cons _ (List.Sublist.cons _ ih)

end WaveTurbulence.RA1Leafwise
