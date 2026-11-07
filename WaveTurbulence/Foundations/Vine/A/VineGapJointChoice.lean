/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineObjectGeometry
public import WaveTurbulence.Foundations.FinalCount.RedSpliceGapKind
public import WaveTurbulence.Foundations.Molecule.VineBlockGapExists
/-! Ordinary chosen-object gap kinds are independent of their ordered joint choice.
Hyper deleted-bond compatibility is a separate obligation. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {d : ℕ}

/-- A different valid pair of block joints gives the same gap kind on source decorations. -/
theorem block_gapKind_joint_iff (hM : M.IsMolecule) {S : Finset V} {a b c e : V}
    (hB : M.IsBlock S a b) (hC : M.IsBlock S c e) (L γ η : ℝ) (base : Mom d)
    (charge : V → Mom d) (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L base charge κ)
    (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → charge v = 0) (kind : Molecule.GapKind) :
    (∃ r, M.IsBlockGap L base κ S a r ∧ Molecule.gapKind L γ η r = kind) ↔
      ∃ r, M.IsBlockGap L base κ S c r ∧ Molecule.gapKind L γ η r = kind := by
  have hk := kvec_cons L base charge κ hκ hc0
  let k := Molecule.kvec L base κ
  have ha : M.IsBlockGap L base κ S a (Vine.groupFlow M S k a) := Vine.block_groupGap_exists M hB k
  have hc : M.IsBlockGap L base κ S c (Vine.groupFlow M S k c) := Vine.block_groupGap_exists M hC k
  have he := Vine.gapKind_eq_of_norm_eq L γ η (flow_norm_joint M hM hB hC k hk.1 hk.2)
  constructor
  · rintro ⟨r, hr, hkind⟩
    refine ⟨_, hc, he.trans ?_⟩
    have hf : r = Vine.groupFlow M S k a := Vine.groupGap_eq_flow M (Mole.block_joint_degrees M hB).1 hr
    simpa only [hf] using hkind
  · rintro ⟨r, hr, hkind⟩
    refine ⟨_, ha, he.symm.trans ?_⟩
    have hf : r = Vine.groupFlow M S k c := Vine.groupGap_eq_flow M (Mole.block_joint_degrees M hC).1 hr
    simpa only [hf] using hkind

/-- Actual ordinary object choices on the same support have identical gap-kind predicates. -/
theorem ordinary_objects_gapKind_iff (hM : M.IsMolecule) (P Q : Object M)
    (h : P.atoms = Q.atoms) (hP : objectHyperTag P = false) (hQ : objectHyperTag Q = false)
    (L γ η : ℝ) (base : Mom d) (charge : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L base charge κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → charge v = 0)
    (kind : Molecule.GapKind) : P.HasGapKind L γ η base κ kind ↔ Q.HasGapKind L γ η base κ kind := by
  cases hp : P.shape with
  | hyper R => simp only [objectHyperTag, hp, Bool.true_eq_false] at hP
  | vc p =>
    cases hq : Q.shape with
    | hyper R => simp only [objectHyperTag, hq, Bool.true_eq_false] at hQ
    | vc q =>
      unfold Object.HasGapKind
      rw [hp, hq]
      change (∃ r, M.IsBlockGap L base κ P.atoms P.upper r ∧ Molecule.gapKind L γ η r = kind) ↔
        ∃ r, M.IsBlockGap L base κ Q.atoms Q.upper r ∧ Molecule.gapKind L γ η r = kind
      rw [← h]
      exact block_gapKind_joint_iff hM p.1 (h.symm ▸ q.1) L γ η base charge κ hκ hc0 kind

end WaveTurbulence.VineA
