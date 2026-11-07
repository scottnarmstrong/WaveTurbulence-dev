/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainAssembly
public import WaveTurbulence.Foundations.VineEst.VineEstS2.InternalBondLabels
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLIngredientJunction
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLBoundaryIdentities

/-! # The next vine's anchor is an actual bond label of the lower piece -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

/-- The unique retained lower slot of the prefix is the unique excluded
upper slot of the terminal vine, with the actual child indices identified. -/
theorem clConcat_sharedChild_index (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (RP : CLRegionData G S a b) (RT : CLRegionData G T b c) (hi : S ∩ T = {b}) :
    RT.excluded = RP.kept := by
  have he := cl_ingredient_shared_child hT hS RT RP (by rw [Finset.inter_comm,hi])
  have hp := congrArg (fun x : GNode G.tree => x.1.2) he
  change b.1.2++[RT.excluded] = b.1.2++[RP.kept] at hp
  exact (List.cons.inj (List.append_cancel_left hp)).1

theorem clPrefixChild_internalDart_exists (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (RP : CLRegionData G S a b) (RT : CLRegionData G T b c) (hi : S ∩ T = {b})
    (i : Fin 3) (hiK : i ≠ RP.kept) :
    ∃ d : InternalDart G.molecule T, G.molecule.atom d.1 = b ∧
      Mole.dartPosition G d.1 = i.succ ∧ Mole.dartNode G d.1 = b.child i := by
  have hn : i ≠ RT.excluded := by rw [clConcat_sharedChild_index hS hT RP RT hi]; exact hiK
  obtain ⟨x,hx,hg,hp⟩ := (Mole.mem_internalPositions G).mp ((RT.upper i).mpr hn)
  have he := Mole.slotNode_dart G x
  rw [hx,hp] at he
  exact ⟨⟨x,hg⟩,hx,hp,he.symm⟩

noncomputable def clPrefixChildDart (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (RP : CLRegionData G S a b) (RT : CLRegionData G T b c) (hi : S ∩ T = {b})
    (i : Fin 3) (hiK : i ≠ RP.kept) : InternalDart G.molecule T :=
  Classical.choose (clPrefixChild_internalDart_exists hS hT RP RT hi i hiK)

theorem clPrefixChildDart_spec (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (RP : CLRegionData G S a b) (RT : CLRegionData G T b c) (hi : S ∩ T = {b})
    (i : Fin 3) (hiK : i ≠ RP.kept) :
    G.molecule.atom (clPrefixChildDart hS hT RP RT hi i hiK).1 = b ∧
      Mole.dartPosition G (clPrefixChildDart hS hT RP RT hi i hiK).1 = i.succ ∧
      Mole.dartNode G (clPrefixChildDart hS hT RP RT hi i hiK).1 = b.child i :=
  Classical.choose_spec (clPrefixChild_internalDart_exists hS hT RP RT hi i hiK)

noncomputable def clPrefixChildBond (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (RP : CLRegionData G S a b) (RT : CLRegionData G T b c) (hi : S ∩ T = {b})
    (i : Fin 3) (hiK : i ≠ RP.kept) : Bond G.molecule T :=
  ((internalBondDartEquiv G.molecule T).symm (clPrefixChildDart hS hT RP RT hi i hiK)).1

/-- The anchor is the literal original child momentum, after internal-pair
matching alone. Its representation as an outgoing bond changes no value. -/
theorem clPrefixChildBond_value {E : Type*} (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (RP : CLRegionData G S a b) (RT : CLRegionData G T b c) (hi : S ∩ T = {b})
    (i : Fin 3) (hiK : i ≠ RP.kept) (κ : GNode G.tree → E)
    (hp : ∀ ℓ, Mole.IsInternalLeaf G T ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) :
    κ (b.child i) = Mole.restrictLabels G κ (clPrefixChildBond hS hT RP RT hi i hiK).1 := by
  let d := clPrefixChildDart hS hT RP RT hi i hiK
  have hn := (clPrefixChildDart_spec hS hT RP RT hi i hiK).2.2
  exact (congrArg κ hn).symm.trans (gardenInternalDartValue κ hp d).symm

/-- The two anchor incidences have their actual physical signs. -/
theorem clPrefixChildDart_sign (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (RP : CLRegionData G S a b) (RT : CLRegionData G T b c) (hi : S ∩ T = {b})
    (i : Fin 3) (hiK : i ≠ RP.kept) :
    G.molecule.dartSign (clPrefixChildDart hS hT RP RT hi i hiK).1 =
      -((G.sign (b.child i) : ℤ) : ℝ) := by
  have hs := Mole.slotWeight_dart G (clPrefixChildDart hS hT RP RT hi i hiK).1
  have hd := clPrefixChildDart_spec hS hT RP RT hi i hiK
  rw [hd.1,hd.2.1,slotWeight_child] at hs
  exact hs.symm

theorem clRegionPositive_ne_kept (RP : CLRegionData G S a b) : RP.positive ≠ RP.kept :=
  (RP.lower_excluded RP.positive).mpr (Or.inl rfl)

theorem clRegionNegative_ne_kept (RP : CLRegionData G S a b) : RP.negative ≠ RP.kept :=
  (RP.lower_excluded RP.negative).mpr (Or.inr rfl)

noncomputable def clPrefixAnchorBond (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (RP : CLRegionData G S a b) (RT : CLRegionData G T b c) (hi : S ∩ T = {b}) : Bond G.molecule T :=
  clPrefixChildBond hS hT RP RT hi RP.positive (clRegionPositive_ne_kept RP)

noncomputable def clPrefixCoanchorBond (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (RP : CLRegionData G S a b) (RT : CLRegionData G T b c) (hi : S ∩ T = {b}) : Bond G.molecule T :=
  clPrefixChildBond hS hT RP RT hi RP.negative (clRegionNegative_ne_kept RP)

end WaveTurbulence.VineEstS2
