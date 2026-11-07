/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4SourceEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountSets
public import WaveTurbulence.Foundations.FinalCount.Degen.LatticeLabels
import Mathlib.Tactic

/-! # Injecting an actual fixed-charge K4 fiber into the canonical integer set -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
open CountLemmas
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

private theorem latticePoint_neg {d : ℕ} (L : ℝ) (n : Fin d → ℤ) :
    latticePoint L (-n) = -latticePoint L n := by
  ext i
  simp only [latticePoint,PiLp.neg_apply,Pi.neg_apply,Int.cast_neg]
  ring

/-- Fixed physical charges imply fixed canonical integer charges on all
actual decorations. They are derived from an actual reference decoration. -/
theorem canonical_K4_integer_momentum_eq (M : Molecule V D)
    (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 ≃ {x // x ∈ M.bonds})
    (he : ∀ r, M.atom (b r).val = (e (k4BondStart r)).val ∧
      M.atom (M.mate (b r).val) = (e (k4BondEnd r)).val)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) {c : V → Mom d} {κ κ0 : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd0 : M.IsDecoration L (0 : Mom d) c κ0) :
    -κ (b 0).val + κ (b 1).val + κ (b 3).val = -κ0 (b 0).val + κ0 (b 1).val + κ0 (b 3).val ∧
    -κ (b 1).val + κ (b 2).val + κ (b 4).val = -κ0 (b 1).val + κ0 (b 2).val + κ0 (b 4).val ∧
    -κ (b 2).val - κ (b 3).val + κ (b 5).val = -κ0 (b 2).val - κ0 (b 3).val + κ0 (b 5).val := by
  have h := canonical_K4_momentum M e b he L hd
  have h0 := canonical_K4_momentum M e b he L hd0
  constructor
  · apply Degen.coset_label_injective hL (0 : Mom d)
    simpa only [zero_add,WeylSums.latticePoint_add_eq,latticePoint_neg] using h.1.trans h0.1.symm
  constructor
  · apply Degen.coset_label_injective hL (0 : Mom d)
    simpa only [zero_add,WeylSums.latticePoint_add_eq,latticePoint_neg] using h.2.1.trans h0.2.1.symm
  · apply Degen.coset_label_injective hL (0 : Mom d)
    simpa only [zero_add,WeylSums.latticePoint_add_eq,WeylSums.latticePoint_sub_eq,latticePoint_neg] using h.2.2.trans h0.2.2.symm

/-- The literal actual source fiber injects into the canonical three-label
set. Integer centers are obtained from a counted reference decoration;
no integer-charge or source-equation premise is inserted. -/
theorem encard_K4_source_fiber_le_reference (M : Molecule V D)
    (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 ≃ {x // x ∈ M.bonds})
    (he : ∀ r, M.atom (b r).val = (e (k4BondStart r)).val ∧
      M.atom (M.mate (b r).val) = (e (k4BondEnd r)).val)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (κ0 : D → (Fin d → ℤ)) (hd0 : M.IsDecoration L (0 : Mom d) c κ0) :
    {κ | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ}.encard ≤
      (k4CanonicalSet L (fun r => k0 (b r).val)
        (-κ0 (b 0).val + κ0 (b 1).val + κ0 (b 3).val)
        (-κ0 (b 1).val + κ0 (b 2).val + κ0 (b 4).val)
        (-κ0 (b 2).val - κ0 (b 3).val + κ0 (b 5).val)
        ![β (e 0).val,β (e 1).val,β (e 2).val] (δ⁻¹ * L^(-2*γ))).encard := by
  let a := -κ0 (b 0).val + κ0 (b 1).val + κ0 (b 3).val
  let b0 := -κ0 (b 1).val + κ0 (b 2).val + κ0 (b 4).val
  let c0 := -κ0 (b 2).val - κ0 (b 3).val + κ0 (b 5).val
  let f := fun κ : D → (Fin d → ℤ) => (κ (b 1).val,κ (b 3).val,κ (b 2).val)
  have hrec (κ : D → (Fin d → ℤ)) (hd : M.IsDecoration L (0 : Mom d) c κ) :
      (fun r => κ (b r).val) = k4Labels a b0 c0 (κ (b 1).val) (κ (b 3).val) (κ (b 2).val) := by
    have hi := canonical_K4_integer_momentum_eq M e b he hL hd hd0
    exact k4Labels_reconstruct a b0 c0 (fun r => κ (b r).val) hi.1 hi.2.1 hi.2.2
  apply Set.encard_le_encard_of_injOn (f := f)
  · intro κ hκ
    obtain ⟨hd,hr,_ha⟩ := hκ
    have heN (r : Fin 6) : NearLattice L (k0 (b r).val) (κ (b r).val) := by
      simpa only [NearLattice,Molecule.kvec,zero_add] using hr.2 (b r).val
    have hE := canonical_K4_energy M e b he L γ δ hd hr
    change f κ ∈ k4CanonicalSet L (fun r => k0 (b r).val) a b0 c0
      ![β (e 0).val,β (e 1).val,β (e 2).val] (δ⁻¹ * L^(-2*γ))
    simp only [k4CanonicalSet,f,Set.mem_ofPred_eq]
    rw [← hrec κ hd]
    exact ⟨heN,hE.1,hE.2.1,hE.2.2⟩
  · intro κ hκ κ' hκ' hh
    have h1 := congrArg Prod.fst hh
    have h3 := congrArg (fun t => t.2.1) hh
    have h2 := congrArg (fun t => t.2.2) hh
    have hlabels : (fun r => κ (b r).val) = (fun r => κ' (b r).val) := by
      rw [hrec κ hκ.1,hrec κ' hκ'.1]
      dsimp only [f] at h1 h3 h2
      rw [h1,h3,h2]
    exact canonicalBondLabels_injOn M b hκ.1.1 hκ'.1.1 hlabels

/-- Integer centers exist for every actual fixed-parameter counting fiber,
including an empty fiber. No reference decoration is assumed. -/
theorem exists_integer_K4_source_fiber_encoding (M : Molecule V D)
    (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 ≃ {x // x ∈ M.bonds})
    (he : ∀ r, M.atom (b r).val = (e (k4BondStart r)).val ∧
      M.atom (M.mate (b r).val) = (e (k4BondEnd r)).val)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    ∃ a b0 c0 : Fin d → ℤ,
      {κ | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ}.encard ≤
        (k4CanonicalSet L (fun r => k0 (b r).val) a b0 c0
          ![β (e 0).val,β (e 1).val,β (e 2).val] (δ⁻¹ * L^(-2*γ))).encard := by
  classical
  by_cases hn : ∃ κ, M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ
  · obtain ⟨κ,hd,_hr,_ha⟩ := hn
    exact ⟨_,_,_,encard_K4_source_fiber_le_reference M e b he hL γ δ c β k0 Adm κ hd⟩
  · refine ⟨0,0,0,?_⟩
    have hempty : {κ | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ} = ∅ := by
      ext κ
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact fun hk => hn ⟨κ,hk⟩
    rw [hempty,Set.encard_empty]
    exact bot_le

/-- The actual terminal simple rank-three source fiber admits the canonical
K4 encoding, with graph enumeration and integer charges both produced here. -/
theorem exists_K4_source_fiber_encoding_of_simple_rank_three (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    (hne : M.atoms.Nonempty) (hmin : ∀ a ∈ M.atoms, 3 ≤ M.deg a)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) (hrank : M.circuitRank = 3)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    ∃ (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 ≃ {x // x ∈ M.bonds}) (a b0 c0 : Fin d → ℤ),
      (∀ r, M.atom (b r).val = (e (k4BondStart r)).val ∧
        M.atom (M.mate (b r).val) = (e (k4BondEnd r)).val) ∧
      {κ | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ}.encard ≤
        (k4CanonicalSet L (fun r => k0 (b r).val) a b0 c0
          ![β (e 0).val,β (e 1).val,β (e 2).val] (δ⁻¹ * L^(-2*γ))).encard := by
  obtain ⟨e,b,he⟩ := exists_canonical_K4_enumeration_of_simple_rank_three M hM hloop hsimple hne hmin hconn hrank
  obtain ⟨a,b0,c0,henc⟩ := exists_integer_K4_source_fiber_encoding M e b he hL γ δ c β k0 Adm
  exact ⟨e,b,a,b0,c0,he,henc⟩

end WaveTurbulence.MoleProp
