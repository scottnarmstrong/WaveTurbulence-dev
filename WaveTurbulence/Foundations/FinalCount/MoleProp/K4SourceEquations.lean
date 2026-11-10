/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4Tournament
public import WaveTurbulence.Foundations.FinalCount.MoleProp.StarEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountAlgebra
import Mathlib.Tactic

/-! # Actual canonical K4 incidence stars and the source equations -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

private theorem bond_out (M : Molecule V D) (b : Fin 6 ≃ {x // x ∈ M.bonds}) (r : Fin 6) :
    M.out (b r).val = true := (mem_filter.mp (b r).property).2

private theorem mate_bond_out (M : Molecule V D) (b : Fin 6 ≃ {x // x ∈ M.bonds}) (r : Fin 6) :
    M.out (M.mate (b r).val) = false := by rw [M.out_mate,bond_out]; rfl

private theorem bond_ne_mate (M : Molecule V D) (b : Fin 6 ≃ {x // x ∈ M.bonds}) (r s : Fin 6) :
    (b r).val ≠ M.mate (b s).val := by
  intro h
  have hh := congrArg M.out h
  rw [bond_out,mate_bond_out] at hh
  cases hh

private theorem bond_ne_bond (M : Molecule V D) (b : Fin 6 ≃ {x // x ∈ M.bonds})
    {r s : Fin 6} (hrs : r ≠ s) : (b r).val ≠ (b s).val :=
  fun h => hrs (b.injective (Subtype.ext h))

private theorem mate_bond_ne_mate (M : Molecule V D) (b : Fin 6 ≃ {x // x ∈ M.bonds})
    {r s : Fin 6} (hrs : r ≠ s) : M.mate (b r).val ≠ M.mate (b s).val :=
  fun h => bond_ne_bond M b hrs (Mole.mate_injective M h)

/-- The canonical outgoing-bond bijection enumerates every actual incidence,
with no assumed degree or prescribed local-star enumeration. -/
theorem mem_dartsAt_canonical_iff (M : Molecule V D)
    (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 ≃ {x // x ∈ M.bonds})
    (he : ∀ r, M.atom (b r).val = (e (k4BondStart r)).val ∧
      M.atom (M.mate (b r).val) = (e (k4BondEnd r)).val)
    (i : Fin 4) (x : D) : x ∈ M.dartsAt (e i).val ↔
      (∃ r, k4BondStart r = i ∧ x = (b r).val) ∨
      (∃ r, k4BondEnd r = i ∧ x = M.mate (b r).val) := by
  constructor
  · intro hx
    have hxa := (Mole.mem_dartsAt M _ _).mp hx
    by_cases ho : M.out x = true
    · obtain ⟨r,hr⟩ := b.surjective ⟨x,mem_filter.mpr ⟨mem_univ _,ho⟩⟩
      have hr' : (b r).val = x := congrArg Subtype.val hr
      refine Or.inl ⟨r,?_,hr'.symm⟩
      have hbr : M.atom (b r).val = (e i).val := by rw [hr']; exact hxa
      exact e.injective (Subtype.ext ((he r).1.symm.trans hbr))
    · have hm : M.out (M.mate x) = true := by
        rw [M.out_mate]
        cases hxout : M.out x <;> simp_all
      obtain ⟨r,hr⟩ := b.surjective ⟨M.mate x,mem_filter.mpr ⟨mem_univ _,hm⟩⟩
      have hr' : (b r).val = M.mate x := congrArg Subtype.val hr
      have hm' : M.mate (b r).val = x := by rw [hr',M.mate_mate]
      refine Or.inr ⟨r,?_,hm'.symm⟩
      have hbr : M.atom (M.mate (b r).val) = (e i).val := by rw [hm']; exact hxa
      exact e.injective (Subtype.ext ((he r).2.symm.trans hbr))
  · rintro (⟨r,hr,rfl⟩ | ⟨r,hr,rfl⟩)
    · exact (Mole.mem_dartsAt M _ _).mpr (by rw [(he r).1,hr])
    · exact (Mole.mem_dartsAt M _ _).mpr (by rw [(he r).2,hr])

/-- The literal canonical incidence set at atom 0. -/
theorem dartsAt_canonical_0 (M : Molecule V D)
    (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 ≃ {x // x ∈ M.bonds})
    (he : ∀ r, M.atom (b r).val = (e (k4BondStart r)).val ∧
      M.atom (M.mate (b r).val) = (e (k4BondEnd r)).val) :
    M.dartsAt (e 0).val = {M.mate (b 0).val,(b 1).val,(b 3).val} := by
  ext x
  rw [mem_dartsAt_canonical_iff M e b he 0 x]
  constructor
  · rintro (⟨r,hr,rfl⟩ | ⟨r,hr,rfl⟩) <;> fin_cases r <;> simp_all [k4BondStart,k4BondEnd]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inr ⟨0,rfl,rfl⟩
    · exact Or.inl ⟨1,rfl,rfl⟩
    · exact Or.inl ⟨3,rfl,rfl⟩

/-- The literal canonical incidence set at atom 1. -/
theorem dartsAt_canonical_1 (M : Molecule V D)
    (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 ≃ {x // x ∈ M.bonds})
    (he : ∀ r, M.atom (b r).val = (e (k4BondStart r)).val ∧
      M.atom (M.mate (b r).val) = (e (k4BondEnd r)).val) :
    M.dartsAt (e 1).val = {M.mate (b 1).val,(b 2).val,(b 4).val} := by
  ext x
  rw [mem_dartsAt_canonical_iff M e b he 1 x]
  constructor
  · rintro (⟨r,hr,rfl⟩ | ⟨r,hr,rfl⟩) <;> fin_cases r <;> simp_all [k4BondStart,k4BondEnd]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inr ⟨1,rfl,rfl⟩
    · exact Or.inl ⟨2,rfl,rfl⟩
    · exact Or.inl ⟨4,rfl,rfl⟩

/-- The literal canonical incidence set at atom 2. -/
theorem dartsAt_canonical_2 (M : Molecule V D)
    (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 ≃ {x // x ∈ M.bonds})
    (he : ∀ r, M.atom (b r).val = (e (k4BondStart r)).val ∧
      M.atom (M.mate (b r).val) = (e (k4BondEnd r)).val) :
    M.dartsAt (e 2).val = {M.mate (b 2).val,M.mate (b 3).val,(b 5).val} := by
  ext x
  rw [mem_dartsAt_canonical_iff M e b he 2 x]
  constructor
  · rintro (⟨r,hr,rfl⟩ | ⟨r,hr,rfl⟩) <;> fin_cases r <;> simp_all [k4BondStart,k4BondEnd]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inr ⟨2,rfl,rfl⟩
    · exact Or.inr ⟨3,rfl,rfl⟩
    · exact Or.inl ⟨5,rfl,rfl⟩

private theorem sum_three {A : Type*} [AddCommMonoid A] (f : D → A)
    {x y z : D} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (∑ a ∈ ({x,y,z} : Finset D), f a) = f x + f y + f z := by
  have hx : x ∉ ({y,z} : Finset D) := by simp only [mem_insert,mem_singleton]; tauto
  have hy : y ∉ ({z} : Finset D) := by simpa only [mem_singleton] using hyz
  rw [sum_insert hx,sum_insert hy,sum_singleton]
  simp only [add_assoc]

theorem sum_dartsAt_canonical_0 (M : Molecule V D)
    (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 ≃ {x // x ∈ M.bonds})
    (he : ∀ r, M.atom (b r).val = (e (k4BondStart r)).val ∧
      M.atom (M.mate (b r).val) = (e (k4BondEnd r)).val)
    {A : Type*} [AddCommMonoid A] (f : D → A) :
    (∑ x ∈ M.dartsAt (e 0).val, f x) = f (M.mate (b 0).val) + f ((b 1).val) + f ((b 3).val) := by
  rw [dartsAt_canonical_0 M e b he]
  apply sum_three
  · exact (bond_ne_mate M b 1 0).symm
  · exact (bond_ne_mate M b 3 0).symm
  · exact bond_ne_bond M b (by decide : (1 : Fin 6) ≠ 3)

theorem sum_dartsAt_canonical_1 (M : Molecule V D)
    (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 ≃ {x // x ∈ M.bonds})
    (he : ∀ r, M.atom (b r).val = (e (k4BondStart r)).val ∧
      M.atom (M.mate (b r).val) = (e (k4BondEnd r)).val)
    {A : Type*} [AddCommMonoid A] (f : D → A) :
    (∑ x ∈ M.dartsAt (e 1).val, f x) = f (M.mate (b 1).val) + f ((b 2).val) + f ((b 4).val) := by
  rw [dartsAt_canonical_1 M e b he]
  apply sum_three
  · exact (bond_ne_mate M b 2 1).symm
  · exact (bond_ne_mate M b 4 1).symm
  · exact bond_ne_bond M b (by decide : (2 : Fin 6) ≠ 4)

theorem sum_dartsAt_canonical_2 (M : Molecule V D)
    (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 ≃ {x // x ∈ M.bonds})
    (he : ∀ r, M.atom (b r).val = (e (k4BondStart r)).val ∧
      M.atom (M.mate (b r).val) = (e (k4BondEnd r)).val)
    {A : Type*} [AddCommMonoid A] (f : D → A) :
    (∑ x ∈ M.dartsAt (e 2).val, f x) = f (M.mate (b 2).val) + f (M.mate (b 3).val) + f ((b 5).val) := by
  rw [dartsAt_canonical_2 M e b he]
  apply sum_three
  · exact mate_bond_ne_mate M b (by decide : (2 : Fin 6) ≠ 3)
  · exact (bond_ne_mate M b 5 2).symm
  · exact (bond_ne_mate M b 5 3).symm

/-- The three actual source momentum equations in canonical bond order.
The fixed charges are arbitrary; no degree-four conservation is invoked. -/
theorem canonical_K4_momentum (M : Molecule V D)
    (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 ≃ {x // x ∈ M.bonds})
    (he : ∀ r, M.atom (b r).val = (e (k4BondStart r)).val ∧
      M.atom (M.mate (b r).val) = (e (k4BondEnd r)).val)
    {d : ℕ} (L : ℝ) {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) :
    -latticePoint L (κ (b 0).val) + latticePoint L (κ (b 1).val) + latticePoint L (κ (b 3).val) = c (e 0).val ∧
    -latticePoint L (κ (b 1).val) + latticePoint L (κ (b 2).val) + latticePoint L (κ (b 4).val) = c (e 1).val ∧
    -latticePoint L (κ (b 2).val) - latticePoint L (κ (b 3).val) + latticePoint L (κ (b 5).val) = c (e 2).val := by
  have h0 := hd.2 (e 0).val (e 0).property
  have h1 := hd.2 (e 1).val (e 1).property
  have h2 := hd.2 (e 2).val (e 2).property
  rw [sum_dartsAt_canonical_0 M e b he] at h0
  rw [sum_dartsAt_canonical_1 M e b he] at h1
  rw [sum_dartsAt_canonical_2 M e b he] at h2
  constructor
  · simpa [Molecule.dartSign,Molecule.kvec,bond_out,mate_bond_out,hd.1,add_assoc] using h0
  constructor
  · simpa [Molecule.dartSign,Molecule.kvec,bond_out,mate_bond_out,hd.1,add_assoc] using h1
  · simpa [Molecule.dartSign,Molecule.kvec,bond_out,mate_bond_out,hd.1,sub_eq_add_neg,add_assoc] using h2

/-- The three actual signed energy bands, exactly as in k4CanonicalSet. -/
theorem canonical_K4_energy (M : Molecule V D)
    (e : Fin 4 ≃ {a // a ∈ M.atoms}) (b : Fin 6 ≃ {x // x ∈ M.bonds})
    (he : ∀ r, M.atom (b r).val = (e (k4BondStart r)).val ∧
      M.atom (M.mate (b r).val) = (e (k4BondEnd r)).val)
    {d : ℕ} (L γ δ : ℝ) {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d}
    {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L (0 : Mom d) c κ)
    (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ) :
    |-‖latticePoint L (κ (b 0).val)‖^2 + ‖latticePoint L (κ (b 1).val)‖^2 + ‖latticePoint L (κ (b 3).val)‖^2 - β (e 0).val| ≤ δ⁻¹ * L^(-2*γ) ∧
    |-‖latticePoint L (κ (b 1).val)‖^2 + ‖latticePoint L (κ (b 2).val)‖^2 + ‖latticePoint L (κ (b 4).val)‖^2 - β (e 1).val| ≤ δ⁻¹ * L^(-2*γ) ∧
    |-‖latticePoint L (κ (b 2).val)‖^2 - ‖latticePoint L (κ (b 3).val)‖^2 + ‖latticePoint L (κ (b 5).val)‖^2 - β (e 2).val| ≤ δ⁻¹ * L^(-2*γ) := by
  have h0 := hr.1 (e 0).val (e 0).property
  have h1 := hr.1 (e 1).val (e 1).property
  have h2 := hr.1 (e 2).val (e 2).property
  unfold Molecule.Gamma at h0 h1 h2
  rw [sum_dartsAt_canonical_0 M e b he] at h0
  rw [sum_dartsAt_canonical_1 M e b he] at h1
  rw [sum_dartsAt_canonical_2 M e b he] at h2
  constructor
  · simpa [Molecule.dartSign,Molecule.kvec,bond_out,mate_bond_out,hd.1,add_assoc] using h0
  constructor
  · simpa [Molecule.dartSign,Molecule.kvec,bond_out,mate_bond_out,hd.1,add_assoc] using h1
  · simpa [Molecule.dartSign,Molecule.kvec,bond_out,mate_bond_out,hd.1,sub_eq_add_neg,add_assoc] using h2

/-- All actual dart labels are determined by the six canonical bond labels,
provided they obey the source equality of the two darts on each bond. -/
theorem canonicalBondLabels_injOn (M : Molecule V D) (b : Fin 6 ≃ {x // x ∈ M.bonds})
    {K : Type*} : Set.InjOn (fun κ : D → K => fun r : Fin 6 => κ (b r).val)
      {κ | ∀ x, κ (M.mate x) = κ x} := by
  intro κ hκ κ' hκ' h
  funext x
  by_cases ho : M.out x = true
  · obtain ⟨r,hr⟩ := b.surjective ⟨x,mem_filter.mpr ⟨mem_univ _,ho⟩⟩
    have hr' : (b r).val = x := congrArg Subtype.val hr
    simpa only [hr'] using congrFun h r
  · have hm : M.out (M.mate x) = true := by
      rw [M.out_mate]
      cases hxout : M.out x <;> simp_all
    obtain ⟨r,hr⟩ := b.surjective ⟨M.mate x,mem_filter.mpr ⟨mem_univ _,hm⟩⟩
    have hr' : (b r).val = M.mate x := congrArg Subtype.val hr
    have hh := congrFun h r
    simpa only [hr',hκ x,hκ' x] using hh

end WaveTurbulence.MoleProp
