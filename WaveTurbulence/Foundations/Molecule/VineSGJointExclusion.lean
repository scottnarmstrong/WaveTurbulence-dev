/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineJointFlows
public import WaveTurbulence.Foundations.Molecule.VineNestedGaps
public import WaveTurbulence.Foundations.Molecule.VineBlockJoints
public import WaveTurbulence.Foundations.Molecule.VineEmptyRungs
import Mathlib.Tactic

/-! # SG nested blocks avoid both joints of an LG or ZG outer block -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- If a nested block contains either outer joint, its gap norm equals
the outer gap norm. The shared atom is forced to be an inner joint by its
restricted degree; no ordered-joint identification is assumed. -/
theorem nested_block_at_outer_joint_norm (M : Molecule V D) (hM : M.IsMolecule)
    {S A : Finset V} {a b x y p : V} (hS : M.IsBlock S a b) (hA : M.IsBlock A x y)
    (hAS : A ⊆ S) (hp : p ∈ A) (hpj : p=a ∨ p=b)
    (k : D → Mom d) (hk : ∀ z,k (M.mate z)=k z)
    (hc : ∀ v ∈ M.atoms,M.deg v=4 → ∑ z ∈ M.dartsAt v,M.dartSign z • k z=0)
    {r r' : Mom d} (hr : IsGroupGap M S k a r) (hr' : IsGroupGap M A k x r') :
    ‖r'‖=‖r‖ := by
  have hSd := Mole.block_joint_degrees M hS
  have hAd := Mole.block_joint_degrees M hA
  have hdpS : M.degIn S p=2 := hpj.elim (fun h => h.symm ▸ hSd.1) (fun h => h.symm ▸ hSd.2)
  have hmin := block_degree_ge_two M hA hp
  have hle := degIn_mono M hAS p
  have hdpA : M.degIn A p=2 := by omega
  have hpinner := block_degree_two_joint M hA hp hdpA
  have hflow : groupFlow M A k p=groupFlow M S k p := by
    unfold groupFlow
    rw [internal_darts_eq_of_nested_degree M hAS p (hdpA.trans hdpS.symm)]
  have hnormJoint (T : Finset V) (u v : V) (hB : M.IsBlock T u v)
      (z : V) (hz : z=u ∨ z=v) : ‖groupFlow M T k z‖=‖groupFlow M T k u‖ := by
    rcases hz with rfl | rfl
    · rfl
    · have hh := block_jointFlow_neg M hM hB k hk hc
      rw [hh,norm_neg]
  calc
    ‖r'‖ = ‖groupFlow M A k x‖ := congrArg norm (groupGap_eq_flow M hAd.1 hr')
    _ = ‖groupFlow M A k p‖ := (hnormJoint A x y hA p hpinner).symm
    _ = ‖groupFlow M S k p‖ := congrArg norm hflow
    _ = ‖groupFlow M S k a‖ := hnormJoint S a b hS p hpj
    _ = ‖r‖ := congrArg norm (groupGap_eq_flow M hSd.1 hr).symm

/-- TARGET subsetvc, stem reduction: neither outer joint can occur in an
SG block nested in an LG or ZG block. This uses only source decoration,
containment and gap-kind premises. -/
theorem SG_block_outer_joints_absent (M : Molecule V D) (hM : M.IsMolecule)
    {S A : Finset V} {a b x y : V} (hS : M.IsBlock S a b) (hA : M.IsBlock A x y)
    (hAS : A ⊆ S) (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ S a r)
    (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) : a ∉ A ∧ b ∉ A := by
  have hk (z : D) : Molecule.kvec L w κ (M.mate z)=Molecule.kvec L w κ z := by
    simp only [Molecule.kvec,hκ.1 z]
  have hcons : ∀ v ∈ M.atoms,M.deg v=4 →
      ∑ z ∈ M.dartsAt v,M.dartSign z • Molecule.kvec L w κ z=0 :=
    fun v hv hd => (hκ.2 v hv).trans (hc v hv hd)
  have absurd (p : V) (hp : p ∈ A) (hpj : p=a ∨ p=b) : False := by
    have hn := nested_block_at_outer_joint_norm M hM hS hA hAS hp hpj
      (Molecule.kvec L w κ) hk hcons hr hr'
    have he := gapKind_eq_of_norm_eq L γ η hn
    rw [hsmall] at he
    rcases houter with h | h <;> rw [h] at he <;> cases he
  exact ⟨fun h => absurd a h (Or.inl rfl),fun h => absurd b h (Or.inr rfl)⟩

end WaveTurbulence.Vine
