/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBValidLinkScales
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertLinkFactors
public import WaveTurbulence.Foundations.FinalCount.AppBAddSafeLadder
import Mathlib.Tactic

/-! # Physical validity of the safe inherited scales after bond reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset Set
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem AppbValidLinkScales.reinsert {M : Molecule V D} {d : ℕ} {L c : ℝ} {w : Mom d}
    {Adm : (D → (Fin d → ℤ)) → Prop} {P : Finset V → ℝ}
    (h : AppbValidLinkScales M L w Adm c P) (Y : Finset V) (a b : V)
    (z : (D → (Fin d → ℤ)) → (Fin d → ℤ)) :
    AppbValidLinkScales (addBond (Degen.eraseAtoms M Y) a b) L w
      (fun ζ => ∃ κ,Adm κ ∧ ζ = Sum.elim (fun x : Degen.RetainedDart M Y => κ x.val)
        (fun _ : Bool => z κ)) c (appbReinsertScales M Y a b P) := by
  classical
  constructor
  · intro S hS
    unfold appbReinsertScales
    split_ifs with hsafe
    · exact h.1 S ((appb_link_eraseAtoms_iff M (Y ∪ {a,b}) S).mp
        ((mem_appbLinks _ _).mp hsafe)).1
    · exact Or.inl rfl
  · intro u v hL ζ hζ g hg hp
    obtain ⟨κ,hκ,rfl⟩ := hζ
    let S := Molecule.ladderAtoms u v
    have hsafe : S ∈ appbLinks (Degen.eraseAtoms M (Y ∪ {a,b})) := by
      by_contra hn
      change 0 < appbReinsertScales M Y a b P S at hp
      simp only [appbReinsertScales,hn,ite_false] at hp
      linarith only [hp]
    have hdis := ((appb_link_eraseAtoms_iff M (Y ∪ {a,b}) S).mp ((mem_appbLinks _ _).mp hsafe)).2
    have hmem (j : Fin 2) : u j ∈ S ∧ v j ∈ S := by
      constructor
      · exact mem_union_left _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
    have hnot : ∀ j,u j ∉ Y ∧ v j ∉ Y := by
      intro j
      exact ⟨fun hx => disjoint_left.mp hdis (hmem j).1 (mem_union_left _ hx),
        fun hx => disjoint_left.mp hdis (hmem j).2 (mem_union_left _ hx)⟩
    have havoid : ∀ j,u j ≠ a ∧ u j ≠ b ∧ v j ≠ a ∧ v j ≠ b := by
      intro j
      have hu := disjoint_left.mp hdis (hmem j).1
      have hv := disjoint_left.mp hdis (hmem j).2
      exact ⟨fun he => hu (he ▸ mem_union_right _ (by simp)),
        fun he => hu (he ▸ mem_union_right _ (by simp)),
        fun he => hv (he ▸ mem_union_right _ (by simp)),
        fun he => hv (he ▸ mem_union_right _ (by simp))⟩
    have hmid := (appb_sourceLadder_addBond_iff (Degen.eraseAtoms M Y) a b u v havoid).mp hL
    have hold := (Degen.sourceLadder_erase_iff M Y u v hnot).mp hmid
    have hgmid := (appb_isLadderGap_addBond_iff (Degen.eraseAtoms M Y) a b L w
      (fun x => κ x.val) (z κ) u v (by decide) g (havoid 0)).mp hg
    have hgold := (Degen.isLadderGap_erase_iff M Y L w κ u v (by decide) hnot g).mp hgmid
    have he : appbReinsertScales M Y a b P S = P S := by
      simp only [appbReinsertScales,hsafe,ite_true]
    change 0 < appbReinsertScales M Y a b P S at hp
    change c⁻¹*appbReinsertScales M Y a b P S ≤ ‖g‖
    rw [he] at hp ⊢
    exact h.2 u v hold κ hκ g hgold hp

end WaveTurbulence.Mole
