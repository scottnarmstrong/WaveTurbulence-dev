/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyChart

/-! # Unit free decoder coefficients for the actual triangular chain chart -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

/-- Recursive coefficients on literal bonds. Disjoint piece bonds prevent
addition of two free coefficients in any matrix entry. -/
noncomputable def chainDecodeFree (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) : Bond G.molecule U → chainInputIndex hM9 B → ℤ := by
  induction B with
  | single hV R => exact (chosenVineChart hM9 _ hV).decodeFree
  | append B hT hi hU R ih =>
    let C := chosenVineChart hM9 _ hT
    let split := bondUnionEquiv (Mole.garden_isMolecule G) B.isBlock hT.1 hi hU
    exact fun e => match split.symm e with
      | .inl eS => Sum.elim (C.decodeFree (B.terminalAnchor hT hi hU R)) (ih eS)
      | .inr eT => Sum.elim (C.decodeFree eT) (fun _ => 0)

noncomputable def chainDecodeGap (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) : Bond G.molecule U → ℤ := by
  induction B with
  | single hV R => exact (chosenVineChart hM9 _ hV).decodeGap
  | append B hT hi hU R ih =>
    let C := chosenVineChart hM9 _ hT
    let split := bondUnionEquiv (Mole.garden_isMolecule G) B.isBlock hT.1 hi hU
    exact fun e => match split.symm e with
      | .inl eS => C.decodeGap (B.terminalAnchor hT hi hU R) + ih eS
      | .inr eT => C.decodeGap eT

/-- Every free coefficient is 0 or a sign, uniformly in chain length. -/
theorem chainDecodeFree_unit (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) (e : Bond G.molecule U) (j : chainInputIndex hM9 B) :
    chainDecodeFree hM9 B e j = 0 ∨ chainDecodeFree hM9 B e j = 1 ∨ chainDecodeFree hM9 B e j = -1 := by
  induction B with
  | single hV R => exact (chosenVineChart hM9 _ hV).free_unit e j
  | append B hT hi hU R ih =>
    cases he : (bondUnionEquiv (Mole.garden_isMolecule G) B.isBlock hT.1 hi hU).symm e <;>
      simp only [chainDecodeFree, he]
    · cases j with
      | inl j => exact (chosenVineChart hM9 _ hT).free_unit _ j
      | inr j => exact ih _ j
    · cases j with
      | inl j => exact (chosenVineChart hM9 _ hT).free_unit _ j
      | inr j => exact Or.inl rfl

end WaveTurbulence.VineEstS2
