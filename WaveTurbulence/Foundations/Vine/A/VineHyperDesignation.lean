/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineDesignatedSupport
public import WaveTurbulence.Foundations.Spine.SourceHyperDesignation
public import WaveTurbulence.Foundations.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.Molecule.VineLocalDartErasure
public import WaveTurbulence.Foundations.Molecule.VineHyperMissingJoint
/-! HVC chains contain an ordinary prefix, which makes their actual deleted
bond intrinsic up to mates. The single-HV case is deliberately separate. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 LGSpine.SourceVine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- A hyper-adjoint chain with at least two ingredients has an ordinary prefix in the original molecule. -/
theorem hyper_chain_ordinary_prefix (hM : M.IsMolecule) {S : Finset V} {a b : V}
    (e : D) (he : M.ends e = s(a, b)) (hB : (Mole.eraseBond M e).IsBlock S a b)
    {n : ℕ} (hn : 2 ≤ n) (hC : Chain (Mole.eraseBond M e) S a b n) :
    ∃ P c, M.IsBlock P a c ∧ P ⊆ S ∧ b ∉ P := by
  have hN := Vine.eraseBond_isMolecule M hM e (Vine.ends_distinct_of_pair M e he hB.2.2.2.1)
  cases hc : hC.toVine with
  | single hv => omega
  | @append P T a c b n hP hT hi hne =>
    obtain ⟨X, hX⟩ := hT
    have hb : b ∉ P := by
      intro hb
      have hh : b = c := Finset.mem_singleton.mp (hi ▸ Finset.mem_inter.mpr ⟨hb, hX.1.2.2.1⟩)
      exact hX.1.2.2.2.1 hh.symm
    have hp := Vine.chain_prefix_isBlock (Mole.eraseBond M e) hN hP hX hi hB
    have hext : ¬ M.InGroup P e := Vine.bond_external_of_missing_joint M e he (fun h => hb h.2)
    let F := Vine.eraseBond_local_embedding M e P hext
    exact ⟨P, c, (F.isBlock_iff P (Subset.refl P) a c).mp hp, subset_union_left, hb⟩

/-- The designation of an HVC is unique up to mates, even against a differently chosen pair of joints. -/
theorem hyper_added_unique_of_chain (hM : M.IsMolecule) {S : Finset V} {a b c d : V}
    (e f : D) (he : M.ends e = s(a, b)) (hf : M.ends f = s(c, d))
    (hE : (Mole.eraseBond M e).IsBlock S a b) (hF : (Mole.eraseBond M f).IsBlock S c d)
    {n : ℕ} (hn : 2 ≤ n) (hC : Chain (Mole.eraseBond M e) S a b n) : e = f ∨ e = M.mate f := by
  obtain ⟨P, j, hP, hPS, hbP⟩ := hyper_chain_ordinary_prefix hM e he hE hn hC
  exact LGSpine.hyper_designation_eq M e f he hE hf hF hP hPS hbP

end WaveTurbulence.VineA
