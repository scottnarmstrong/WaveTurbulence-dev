/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamActualSignedSum
public import WaveTurbulenceVineParam.VineParamEnergyCertificates
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockBarriers
import Mathlib.Tactic

/-! # Directed energy is the actual negative molecular Gamma

No resonance formula is a premise. The identities follow from the exact
outgoing bond enumeration, mate-invariant decoration, and full interior
degree. Joints retain the internal signed sum for later boundary assembly.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Directed endpoints of an actual internal bond enumeration. -/
@[expose] def actualEnds (M : Molecule V D) (S : Finset V) {m : ℕ}
    (e : Fin m ≃ internalBonds M S) (j : Fin m) : V×V :=
  (M.atom (e j).1,M.atom (M.mate (e j).1))

omit [InnerProductSpace ℝ E] in
/-- Evaluation of the certified energy rows agrees with the exact signed
internal dart sum at every actual atom. -/
theorem directedEnergy_actual (M : Molecule V D) (S : Finset V) {m : ℕ}
    (e : Fin m ≃ internalBonds M S) (v : V) (k : D → E)
    (hk : ∀ d,k (M.mate d)=k d) :
    directedEnergy (actualEnds M S e) v (fun j => k (e j).1)=
      -internalSignedSum M S v (fun d => ‖k d‖^2) := by
  rw [directedEnergy,internalSignedSum_eq_enumeration M S v e _ (fun d => congrArg (fun x : E => ‖x‖^2) (hk d)),
    ← sum_neg_distrib]
  apply sum_congr rfl
  intro j _hj
  dsimp only [energySign,actualEnds]
  by_cases ha : M.atom (e j).1=v <;>
    by_cases hb : M.atom (M.mate (e j).1)=v <;>
      simp only [ha,hb,ite_true,ite_false,Int.cast_sub,Int.cast_one,Int.cast_zero] <;> ring

/-- Full-degree interior atoms have no external dart contribution to Gamma. -/
theorem internalSignedSum_eq_Gamma (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {v : V} (hv : v ∈ S) (hS : S ⊆ M.atoms)
    (hd : M.degIn S v=4) {d : ℕ} (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) :
    internalSignedSum M S v (fun e => ‖Molecule.kvec L w κ e‖^2)=M.Gamma L w κ v := by
  have hfilter : (M.dartsAt v).filter (M.InGroup S)=M.dartsAt v := by
    apply filter_eq_self.mpr
    intro x hx
    have hxv := (Mole.mem_dartsAt M v x).mp hx
    exact ⟨hxv.symm ▸ hv,Mole.full_degree_no_exit M hM (hS hv) hd hxv⟩
  rw [internalSignedSum,hfilter]
  apply sum_congr rfl
  intro x _hx
  simp only [Molecule.dartSign]
  split_ifs <;> simp only [one_mul,neg_one_mul]

/-- Exact source-facing molecular resonance transport for any full-degree
vine atom. Only the decoration's source mate equality is used. -/
theorem directedEnergy_eq_neg_Gamma (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {v : V} (hv : v ∈ S) (hS : S ⊆ M.atoms)
    (hd : M.degIn S v=4) {m d : ℕ} (e : Fin m ≃ internalBonds M S)
    (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ))
    (hk : ∀ x,κ (M.mate x)=κ x) :
    directedEnergy (actualEnds M S e) v (fun j => Molecule.kvec L w κ (e j).1)=
      -M.Gamma L w κ v := by
  rw [directedEnergy_actual M S e v _ (by
    intro x
    simp only [Molecule.kvec,hk x]),internalSignedSum_eq_Gamma M hM hv hS hd]

end WaveTurbulence.Vine.Param
