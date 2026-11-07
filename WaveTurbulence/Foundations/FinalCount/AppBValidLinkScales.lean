/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLinkDeletion
public import WaveTurbulence.Foundations.FinalCount.AppBConditionedDeletion
import Mathlib.Tactic

/-! # Physical lower-gap validity of inherited local link scales

Validity tests every actual rail presentation of a selected length-one
ladder, so no later operation relies on a choice of ladder orientation.
The zero scale is permitted, as in the source dyadic convention.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset Set
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The source range and lower-gap comparison on each actual local link.
The comparison constant is fixed independently of the molecule size. -/
def AppbValidLinkScales (M : Molecule V D) {d : ℕ} (L : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : ℝ) (P : Finset V → ℝ) : Prop :=
  (∀ S,AppbLink M S → P S = 0 ∨ P S ∈ Icc L⁻¹ 1) ∧
  ∀ (u v : Fin 2 → V) (h : Degen.SourceLadder (m := 1) M u v),
    ∀ κ,Adm κ → ∀ g : Mom d,M.IsLadderGap L w κ u v (by decide) g →
      0 < P (Molecule.ladderAtoms u v) → c⁻¹*P (Molecule.ladderAtoms u v) ≤ ‖g‖

/-- Literal deletion keeps exactly the same rail gaps on surviving links. -/
theorem AppbValidLinkScales.eraseAtoms {M : Molecule V D} {d : ℕ} {L c : ℝ} {w : Mom d}
    {Adm : (D → (Fin d → ℤ)) → Prop} {P : Finset V → ℝ}
    (h : AppbValidLinkScales M L w Adm c P) (Y : Finset V) :
    AppbValidLinkScales (Degen.eraseAtoms M Y) L w
      (fun ζ => ∃ κ,Adm κ ∧ ζ = fun x => κ x.val) c P := by
  constructor
  · intro S hS
    exact h.1 S ((appb_link_eraseAtoms_iff M Y S).mp hS).1
  · intro u v hL ζ hζ g hgap hp
    obtain ⟨κ,hκ,rfl⟩ := hζ
    have hnot : ∀ j,u j ∉ Y ∧ v j ∉ Y := by
      intro j
      exact ⟨(mem_sdiff.mp (hL.2.2.1 j).1).2,(mem_sdiff.mp (hL.2.2.1 j).2).2⟩
    exact h.2 u v ((Degen.sourceLadder_erase_iff M Y u v hnot).mp hL) κ hκ g
      ((Degen.isLadderGap_erase_iff M Y L w κ u v (by decide) hnot g).mp hgap) hp

/-- Restricting admissibility cannot invalidate a physical scale test. -/
theorem AppbValidLinkScales.mono {M : Molecule V D} {d : ℕ} {L c : ℝ} {w : Mom d}
    {Adm Adm' : (D → (Fin d → ℤ)) → Prop} {P : Finset V → ℝ}
    (h : AppbValidLinkScales M L w Adm c P) (hA : ∀ κ,Adm' κ → Adm κ) :
    AppbValidLinkScales M L w Adm' c P :=
  ⟨h.1,fun u v hL κ hκ g hg hp => h.2 u v hL κ (hA κ hκ) g hg hp⟩

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem conditionedPost_validLinkScales {d : ℕ} {L c : ℝ} {w : Mom d}
    {Adm : (D → (Fin d → ℤ)) → Prop} {scales : Finset V → ℝ}
    (h : AppbValidLinkScales M L w Adm c scales)
    (q : Fin P.edges.length → (Fin d → ℤ)) :
    AppbValidLinkScales r.post L w (r.conditionedPostAdmissibility Adm q) c scales := by
  apply (h.eraseAtoms r.removedAtoms).mono
  intro ζ hζ
  obtain ⟨κ,hκ,hm,hq,hr⟩ := hζ
  exact ⟨κ,hκ,hr.symm⟩

end AppbRealization
end WaveTurbulence.Mole
