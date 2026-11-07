/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairFiveSourceEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.OneSharedSignedCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairCoverage
import Mathlib.Tactic

/-! # Two actual cubic stars sharing a bond give the literal source equations

The original physical charges determine integer parameters on each old
parameter fiber. Only distinctness inside each actual star is required.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def actualSharedSigns (M : Molecule V D) (x y r s t : D) : Fin 6 → Bool :=
  ![M.out x,M.out y,M.out r,M.out (M.mate x),M.out s,M.out t]

theorem actual_shared_physical_momentum (M : Molecule V D) {d : ℕ} (L : ℝ)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {x y r s t : D}
    (hxy : x ≠ y) (hxr : x ≠ r) (hyr : y ≠ r)
    (hxs : M.mate x ≠ s) (hxt : M.mate x ≠ t) (hst : s ≠ t)
    (hA : M.dartsAt a = {x,y,r}) (hB : M.dartsAt b = {M.mate x,s,t})
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L (0 : Mom d) c κ)
    (second : Bool) :
    (∑ i : Fin 5, sharedCoefficients (actualSharedSigns M x y r s t) second i •
      latticePoint L (doubleFiveProfile x y r s t κ i)) = if second then c b else c a := by
  have hpa := momentum_of_dartsAt_triple M L ha hxy hxr hyr hA hd
  have hpb := momentum_of_dartsAt_triple M L hb hxs hxt hst hB hd
  cases second
  · simpa [sharedCoefficients,actualSharedSigns,doubleFiveProfile,Fin.sum_univ_succ,
      doubleSign_out_smul,add_assoc] using hpa
  · simpa [sharedCoefficients,actualSharedSigns,doubleFiveProfile,Fin.sum_univ_succ,
      doubleSign_out_smul,hd.1,add_assoc] using hpb

theorem actual_shared_energy (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {x y r s t : D}
    (hxy : x ≠ y) (hxr : x ≠ r) (hyr : y ≠ r)
    (hxs : M.mate x ≠ s) (hxt : M.mate x ≠ t) (hst : s ≠ t)
    (hA : M.dartsAt a = {x,y,r}) (hB : M.dartsAt b = {M.mate x,s,t})
    {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d} {κ : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ)
    (second : Bool) :
    |(∑ i : Fin 5, sharedCoefficients (actualSharedSigns M x y r s t) second i •
      ‖latticePoint L (doubleFiveProfile x y r s t κ i)‖^2)-
      (if second then β b else β a)| ≤ δ⁻¹*L^(-2*γ) := by
  have hpa := energy_of_dartsAt_triple M L γ δ ha hxy hxr hyr hA hr
  have hpb := energy_of_dartsAt_triple M L γ δ hb hxs hxt hst hB hr
  cases second
  · simpa [sharedCoefficients,actualSharedSigns,doubleFiveProfile,Fin.sum_univ_succ,
      zsmul_eq_mul,doubleSign_out_cast,add_assoc] using hpa
  · simpa [sharedCoefficients,actualSharedSigns,doubleFiveProfile,Fin.sum_univ_succ,
      zsmul_eq_mul,doubleSign_out_cast,hd.1,add_assoc] using hpb

/-- Integer momentum parameters are fixed by the actual old charges,
without requiring these physical charges to vanish. -/
theorem actual_shared_integer_momentum_eq (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {x y r s t : D}
    (hxy : x ≠ y) (hxr : x ≠ r) (hyr : y ≠ r)
    (hxs : M.mate x ≠ s) (hxt : M.mate x ≠ t) (hst : s ≠ t)
    (hA : M.dartsAt a = {x,y,r}) (hB : M.dartsAt b = {M.mate x,s,t})
    {c : V → Mom d} {κ κ0 : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd0 : M.IsDecoration L (0 : Mom d) c κ0)
    (second : Bool) :
    (∑ i : Fin 5, sharedCoefficients (actualSharedSigns M x y r s t) second i • doubleFiveProfile x y r s t κ i) =
      ∑ i : Fin 5, sharedCoefficients (actualSharedSigns M x y r s t) second i • doubleFiveProfile x y r s t κ0 i := by
  apply latticePointHom_injective hL
  simp only [map_sum,map_zsmul,latticePointHom_apply]
  exact (actual_shared_physical_momentum M L ha hb hxy hxr hyr hxs hxt hst hA hB hd second).trans
    (actual_shared_physical_momentum M L ha hb hxy hxr hyr hxs hxt hst hA hB hd0 second).symm

theorem deleted_shared_triples_coverage (M : Molecule V D) {a b : V} {x y r s t : D}
    (hA : M.dartsAt a = {x,y,r}) (hB : M.dartsAt b = {M.mate x,s,t}) :
    ∀ z : DeletedDart M {a,b}, ∃ i : Fin 5,
      z.val = (![x,y,r,s,t] : Fin 5 → D) i ∨ z.val = M.mate ((![x,y,r,s,t] : Fin 5 → D) i) := by
  apply deleted_cover_of_incident_cover
  intro z hz
  rcases mem_insert.mp hz with hz | hz
  · have hmem := (Mole.mem_dartsAt M a z).mpr hz
    rw [hA] at hmem
    rcases mem_insert.mp hmem with hzx | hmem
    · exact ⟨0,Or.inl hzx⟩
    · rcases mem_insert.mp hmem with hzy | hzr
      · exact ⟨1,Or.inl hzy⟩
      · exact ⟨2,Or.inl (mem_singleton.mp hzr)⟩
  · have hmem := (Mole.mem_dartsAt M b z).mpr (mem_singleton.mp hz)
    rw [hB] at hmem
    rcases mem_insert.mp hmem with hzx | hmem
    · exact ⟨0,Or.inr hzx⟩
    · rcases mem_insert.mp hmem with hzs | hzt
      · exact ⟨3,Or.inl hzs⟩
      · exact ⟨4,Or.inl (mem_singleton.mp hzt)⟩

end WaveTurbulence.MoleProp
