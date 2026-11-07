/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBridgeLinkFactors
public import WaveTurbulence.Foundations.FinalCount.AppBBridgeCounting
public import WaveTurbulence.Foundations.FinalCount.AppBValidLinkScales
import Mathlib.Tactic

/-! # Physical validity of the safe inherited scales after bridge removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset Set
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_sourceLadder_eraseBond_iff (M : Molecule V D) (e : D)
    {m : ℕ} (u v : Fin (m+1) → V)
    (havoid : ∀ j,u j ≠ M.atom e ∧ u j ≠ M.atom (M.mate e) ∧
      v j ≠ M.atom e ∧ v j ≠ M.atom (M.mate e)) :
    Degen.SourceLadder (eraseBond M e) u v ↔ Degen.SourceLadder M u v := by
  have hne {p q : V} (hp : p ≠ M.atom e ∧ p ≠ M.atom (M.mate e)) : M.ends e ≠ s(p,q) := by
    intro he
    rcases Sym2.eq_iff.mp he with h | h
    · exact hp.1 h.1.symm
    · exact hp.2 h.2.symm
  unfold Degen.SourceLadder
  simp_rw [appb_eraseBond_bondsBetween_eq M e _ _ (hne ⟨(havoid _).1,(havoid _).2.1⟩),
    appb_eraseBond_bondsBetween_eq M e _ _ (hne ⟨(havoid _).2.2.1,(havoid _).2.2.2⟩),
    appb_eraseBond_directed_iff M e _ _ (hne ⟨(havoid _).1,(havoid _).2.1⟩),
    appb_eraseBond_directed_iff M e _ _ (hne ⟨(havoid _).2.2.1,(havoid _).2.2.2⟩)]
  rfl

theorem AppbValidLinkScales.eraseBond {M : Molecule V D} {d : ℕ} {L c : ℝ} {w : Mom d}
    {Adm : (D → (Fin d → ℤ)) → Prop} {P : Finset V → ℝ}
    (h : AppbValidLinkScales M L w Adm c P) (e : D) (q : Fin d → ℤ) :
    AppbValidLinkScales (eraseBond M e) L w (appbBridgePostAdmissibility M e Adm q) c
      (appbBridgeScales M e P) := by
  classical
  constructor
  · intro S hS
    unfold appbBridgeScales
    split_ifs with hsafe
    · exact h.1 S ((appb_link_eraseAtoms_iff M {M.atom e,M.atom (M.mate e)} S).mp
        ((mem_appbLinks _ _).mp hsafe)).1
    · exact Or.inl rfl
  · intro u v hL ζ hζ g hg hp
    obtain ⟨κ,hκ,hq,hm,rfl⟩ := hζ
    let S := Molecule.ladderAtoms u v
    have hsafe : S ∈ appbLinks (Degen.eraseAtoms M {M.atom e,M.atom (M.mate e)}) := by
      by_contra hn
      change 0 < appbBridgeScales M e P S at hp
      simp only [appbBridgeScales,hn,ite_false] at hp
      linarith only [hp]
    have hdis := ((appb_link_eraseAtoms_iff M {M.atom e,M.atom (M.mate e)} S).mp
      ((mem_appbLinks _ _).mp hsafe)).2
    have hmem (j : Fin 2) : u j ∈ S ∧ v j ∈ S := by
      constructor
      · exact mem_union_left _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
    have havoid : ∀ j,u j ≠ M.atom e ∧ u j ≠ M.atom (M.mate e) ∧
        v j ≠ M.atom e ∧ v j ≠ M.atom (M.mate e) := by
      intro j
      have hu := disjoint_left.mp hdis (hmem j).1
      have hv := disjoint_left.mp hdis (hmem j).2
      exact ⟨fun he => hu (he.symm ▸ (by simp)),fun he => hu (he.symm ▸ (by simp)),
        fun he => hv (he.symm ▸ (by simp)),fun he => hv (he.symm ▸ (by simp))⟩
    have hold := (appb_sourceLadder_eraseBond_iff M e u v havoid).mp hL
    obtain ⟨x,y,hx,hy,hax,hay,hr⟩ := hg
    have hgold : M.IsLadderGap L w κ u v (by decide) g := ⟨x.val,y.val,hx,hy,hax,hay,hr⟩
    have he : appbBridgeScales M e P S = P S := by simp only [appbBridgeScales,hsafe,ite_true]
    change 0 < appbBridgeScales M e P S at hp
    change c⁻¹*appbBridgeScales M e P S ≤ ‖g‖
    rw [he] at hp ⊢
    exact h.2 u v hold κ hκ g hgold hp

end WaveTurbulence.Mole
