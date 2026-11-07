/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBReinsertValidScales
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertAdmissibility
import Mathlib.Tactic

/-! # Both source reinsertion directions consume and preserve physical scale validity -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem reinsertedPost_validLinkScales (a b : ℕ) (i : Fin P.edges.length)
    {d : ℕ} {L c : ℝ} {w : Mom d} {Adm : (D → (Fin d → ℤ)) → Prop}
    {scales : Finset V → ℝ} (h : AppbValidLinkScales M L w Adm c scales) :
    AppbValidLinkScales (r.directedPostWithBond a b i) L w
      (r.reinsertedPostAdmissibility Adm i) c
      (appbReinsertScales M r.removedAtoms (r.vertex a) (r.vertex b) scales) := by
  classical
  have hm : ∀ a b : V,AppbValidLinkScales (addBond r.post a b) L w
      (r.reinsertedPostAdmissibility Adm i) c (appbReinsertScales M r.removedAtoms a b scales) := by
    intro a b
    apply (h.reinsert r.removedAtoms a b (fun κ => κ (r.edge i).val)).mono
    intro ζ hζ
    obtain ⟨κ,hκ,hm,hr⟩ := hζ
    exact ⟨κ,hκ,hr.symm⟩
  unfold directedPostWithBond
  split_ifs
  · exact hm _ _
  · have hs : appbReinsertScales M r.removedAtoms (r.vertex a) (r.vertex b) scales =
        appbReinsertScales M r.removedAtoms (r.vertex b) (r.vertex a) scales := by
      funext S
      simp only [appbReinsertScales]
      rw [show ({r.vertex a,r.vertex b} : Finset V) = {r.vertex b,r.vertex a} from Finset.pair_comm _ _]
    rw [hs]
    exact hm _ _

end AppbRealization
end WaveTurbulence.Mole
