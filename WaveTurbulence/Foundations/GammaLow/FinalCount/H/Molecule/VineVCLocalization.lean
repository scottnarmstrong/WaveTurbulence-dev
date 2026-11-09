/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineVCLocalization
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainJointNorm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineVCLocalization`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # An SG VC lies in one ingredient of an LG/ZG outer VC -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- Different conserved gap norms prevent an inner VC from crossing any
outer chain junction. All separator and prefix data are derived from source
containment, without assuming that the inner VC is a single ingredient. -/
theorem VC_in_chain_ingredient_of_flow_norm_ne (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {x y a b : V} {n : ℕ} (hA : Src.IsVC Src.γL M A x y)
    (k : D → Mom d) (hk : ∀ z,k (M.mate z)=k z)
    (hc : ∀ v ∈ M.atoms,M.deg v=4 → ∑ z ∈ M.dartsAt v,M.dartSign z • k z=0)
    (h : Src.Chain Src.γL M U a b n) :
    M.IsBlock U a b → A ⊆ U → ‖groupFlow M A k x‖ ≠ ‖groupFlow M U k a‖ →
      ∃ T p q,ChainIngredient M U a b n T p q ∧ A ⊆ T := by
  induction h with
  | single h =>
    intro _hU hAU _hne
    exact ⟨_,_,_,ChainIngredient.single h,hAU⟩
  | @append S T a b c n hS hT hi hne ih =>
    intro hU hAU hnorm
    have hX := hT
    have hbA : b ∉ A := fun hb => hnorm (VC_at_chain_split_joint_norm M hM hS hX hi hU hA hAU hb k hk hc)
    have hconn : GroupConnected M (A.erase b) := by
      rw [Finset.erase_eq_self.mpr hbA]
      exact isVC_connected hA
    have hside := connected_erase_subset_side M S T A b (chain_joints_mem hS).2 hX.block.2.1 hAU
      (fun v hv hvb u hu huv => terminal_block_adj_mem M hM hX.block hU subset_union_right hv hvb hu huv) hconn
    rcases hside with hAS | hAT
    · have hprefix := chain_prefix_isBlock M hM hS hX hi hU
      have hflow := nested_groupFlow_eq M (show S ⊆ S ∪ T from subset_union_left) a
        ((Mole.block_joint_degrees M hprefix).1.trans (Mole.block_joint_degrees M hU).1.symm) k
      have hneq : ‖groupFlow M A k x‖ ≠ ‖groupFlow M S k a‖ := by rwa [hflow]
      obtain ⟨B,p,q,hB,hAB⟩ := ih hprefix hAS hneq
      exact ⟨B,p,q,ChainIngredient.append_left hB hX hi hne,hAB⟩
    · exact ⟨T,b,c,ChainIngredient.append_last hS hX hi hne,hAT⟩

/-- TARGET Lemma subsetvc, ordinary localization in an outer VC: an SG
inner VC lies in a single actual vine ingredient of an LG/ZG VC. -/
theorem SG_VC_in_VC_ingredient (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {x y a b : V} (hA : Src.IsVC Src.γL M A x y) (hU : Src.IsVC Src.γL M U a b) (hAU : A ⊆ U)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ U a r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) :
    ∃ n T p q,ChainIngredient M U a b n T p q ∧ A ⊆ T := by
  have hk (z : D) : Molecule.kvec L w κ (M.mate z)=Molecule.kvec L w κ z := by
    simp only [Molecule.kvec,hκ.1 z]
  have hcons : ∀ v ∈ M.atoms,M.deg v=4 →
      ∑ z ∈ M.dartsAt v,M.dartSign z • Molecule.kvec L w κ z=0 :=
    fun v hv hd => (hκ.2 v hv).trans (hc v hv hd)
  have hnorm : ‖groupFlow M A (Molecule.kvec L w κ) x‖ ≠ ‖groupFlow M U (Molecule.kvec L w κ) a‖ := by
    intro hn
    have he : ‖r'‖=‖r‖ := by
      rw [groupGap_eq_flow M (Mole.block_joint_degrees M hA.1).1 hr',
        groupGap_eq_flow M (Mole.block_joint_degrees M hU.1).1 hr]
      exact hn
    have heq := gapKind_eq_of_norm_eq L γ η he
    rw [hsmall] at heq
    rcases houter with ho | ho <;> rw [ho] at heq <;> cases heq
  obtain ⟨hUB,n,hchain⟩ := hU
  obtain ⟨T,p,q,hT,hAT⟩ := VC_in_chain_ingredient_of_flow_norm_ne M hM hA
    (Molecule.kvec L w κ) hk hcons hchain hUB hAU hnorm
  exact ⟨n,T,p,q,hT,hAT⟩

end WaveTurbulence.GammaLow.FinalCount.H
