/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceIter
public import WaveTurbulence.Foundations.Molecule.TwistSplicedGarden
/-! VINE-A4 first bridge: S2a's actual singleton fold is the canonical CL
splice. This enables direct reuse of the universe's literal splice invariance. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.Twist
variable {w : ℕ} {G : Garden w}

/-- Canonical splicing depends on the actual block data, not the proof witnesses. -/
theorem clSplicedGarden_congr {S T : Finset (GBranch G.tree)} {a b c d : GBranch G.tree}
    (hS : S = T) (ha : a = c) (hb : b = d) (hB : G.molecule.IsBlock S a b)
    (hCL : CLParentPattern G S a b) (hB' : G.molecule.IsBlock T c d) (hCL' : CLParentPattern G T c d) :
    clSplicedGarden hB hCL = clSplicedGarden hB' hCL' := by
  subst T
  subst c
  subst d
  rfl

/-- S2a's pullback in the initial state is the original atom set. -/
theorem init_pb (S : Finset (GBranch G.tree)) : (SpState.init G).M.pb S = S := by
  ext v
  rw [SpMap.mem_pb]
  rfl

/-- The actual fold with one unit is exactly the universe canonical splice. -/
theorem spliceFold_singleton_G (u : CLBlock G) :
    (spliceFold G [u]).G = clSplicedGarden u.isBlock u.cl := by
  have hu : ∀ v ∈ u.atoms, (SpState.init G).cls v = none := fun _ _ => rfl
  change (spliceStep (SpState.init G) u).G = _
  rw [spliceStep, dite_eq_left hu]
  let h := SpMap.pb_block (SpState.init G).M (SpState.init G).hcls hu u.isBlock u.cl
  let a' := h.choose
  let h2 := h.choose_spec
  let b' := h2.choose
  let h3 := h2.choose_spec
  change clSplicedGarden h3.2.2.1 h3.2.2.2 = clSplicedGarden u.isBlock u.cl
  exact clSplicedGarden_congr (init_pb u.atoms) h3.1 h3.2.1 _ _ _ _

/-- When the spliced unit is the active core vine, the post-splice garden is literal invariant. -/
theorem singleton_core_twist (u : CLBlock G) (P : CorePlacement G)
    (hl : u.lower = P.lower) (hP : IsPlacementAt G u.atoms P.lower P) :
    let hB : G.molecule.IsBlock u.atoms u.upper P.lower := hl ▸ u.isBlock
    let hCL : CLParentPattern G u.atoms u.upper P.lower := hl ▸ u.cl
    (spliceFold (unitTwistGarden G P)
      [⟨twistedAtoms G P u.atoms, coreBranchEquiv G P u.upper, coreBranchEquiv G P P.lower,
        isBlock_twistedAtoms G P hB, clParentPattern_twistedAtoms G P hB hCL hP⟩]).G =
      (spliceFold G [u]).G := by
  dsimp only
  rw [spliceFold_singleton_G, spliceFold_singleton_G]
  exact (unitTwist_canonicalSplice G P (hl ▸ u.isBlock) (hl ▸ u.cl) hP).trans
    (clSplicedGarden_congr rfl rfl hl.symm _ _ _ _)

end WaveTurbulence.VineA
