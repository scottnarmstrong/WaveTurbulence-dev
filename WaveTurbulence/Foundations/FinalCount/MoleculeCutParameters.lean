/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.MoleculeCutDecorations
import Mathlib.Tactic

/-!
# Actual conservation and restriction parameters after a cut

TARGET `defcut` and `defcounta2`. For fixed cut labels, both transformed
parameter functions are fixed. Thus each fiber of the unchanged labels
maps into an actual post-cut restricted-decoration family.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  (M : Molecule V D) {v v2 : V} {x1 x2 : D}

/-- Conservation sources after splitting v: -r at the kept pair and c_v+r
at the new atom. Every other source is inherited. -/
@[expose] def cutSource {d : ℕ} (c : V → Mom d) (v v2 : V) (r : Mom d) (z : V) : Mom d :=
  if z = v then -r else if z = v2 then c v+r else c z

/-- Energy centers after splitting v: exact pair energy q at the kept
atom, and the complementary old center at the new atom. -/
@[expose] def cutCenters (beta : V → ℝ) (v v2 : V) (q : ℝ) (z : V) : ℝ :=
  if z = v then q else if z = v2 then beta v-q else beta z

/-- Unchanged labels satisfy the actual post-cut conservation equations. -/
theorem cut_isDecoration {d : ℕ} (hd : M.IsCutData v v2 x1 x2)
    (L : ℝ) (base : Mom d) (c : V → Mom d) (k : D → (Fin d → ℤ))
    (hk : M.IsDecoration L base c k) :
    (M.cut v v2 x1 x2).IsDecoration L base
      (cutSource c v v2 (Molecule.gapAt L base k x1 x2)) k := by
  refine ⟨hk.1,?_⟩
  intro z hz
  by_cases h1 : z = v
  · subst z
    simpa only [cutSource,ite_true] using cut_conservation_old M hd L base k
  · by_cases h2 : z = v2
    · subst z
      simpa only [cutSource,h1,ite_false,ite_true] using cut_conservation_new M hd L base c k hk
    · have hzold : z ∈ M.atoms := (Finset.mem_insert.mp hz).resolve_left h2
      simp only [cutSource,h1,h2,ite_false]
      rw [cut_dartsAt_other M h1 h2]
      exact hk.2 z hzold

/-- The restricted energy inequality is preserved with the exact new
centers, and all original bond-ball restrictions are unchanged. -/
theorem cut_isRestricted {d : ℕ} (hd : M.IsCutData v v2 x1 x2)
    (L gamma delta : ℝ) (base : Mom d) (beta : V → ℝ) (k0 : D → Mom d)
    (k : D → (Fin d → ℤ)) (hk : M.IsRestricted L gamma delta base beta k0 k) :
    (M.cut v v2 x1 x2).IsRestricted L gamma delta base
      (cutCenters beta v v2 (-‖Molecule.kvec L base k x1‖^2+‖Molecule.kvec L base k x2‖^2)) k0 k := by
  let q := -‖Molecule.kvec L base k x1‖^2+‖Molecule.kvec L base k x2‖^2
  have hq : (M.cut v v2 x1 x2).Gamma L base k v = q := cut_Gamma_old M hd L base k
  have ht : 0 ≤ delta⁻¹*L^(-2*gamma) := (abs_nonneg _).trans (hk.1 v hd.1)
  refine ⟨?_,hk.2⟩
  intro z hz
  by_cases h1 : z = v
  · subst z
    simpa only [cutCenters,ite_true,hq,q,sub_self,abs_zero] using ht
  · by_cases h2 : z = v2
    · subst z
      simp only [cutCenters,h1,ite_false,ite_true]
      have hs := cut_Gamma_add M hd L base k
      rw [hq] at hs
      have he : (M.cut v v2 x1 x2).Gamma L base k v2-(beta v-q) = M.Gamma L base k v-beta v := by
        linarith only [hs]
      rw [he]
      exact hk.1 v hd.1
    · have hzold : z ∈ M.atoms := (Finset.mem_insert.mp hz).resolve_left h2
      simp only [cutCenters,h1,h2,ite_false]
      have he : (M.cut v v2 x1 x2).Gamma L base k z = M.Gamma L base k z := by
        unfold Molecule.Gamma
        rw [cut_dartsAt_other M h1 h2]
        rfl
      rw [he]
      exact hk.1 z hzold

/-- The transformed conservation source is admissible for the actual E
supremum: new degree-two atoms impose no degree-four constraint. -/
theorem cutSource_degree_four {d : ℕ} (hM : M.IsMolecule) (hd : M.IsCutData v v2 x1 x2)
    (c : V → Mom d) (hc : ∀ z ∈ M.atoms, M.deg z = 4 → c z = 0) (r : Mom d) :
    ∀ z ∈ (M.cut v v2 x1 x2).atoms, (M.cut v v2 x1 x2).deg z = 4 → cutSource c v v2 r z = 0 := by
  intro z hz hd4
  have h1 : z ≠ v := by
    intro he
    subst z
    rw [cut_deg_old M hd] at hd4
    omega
  have h2 : z ≠ v2 := by
    intro he
    subst z
    have hsplit := cut_deg_new_add_two M hd
    have hdeg := deg_le_four M hM hd.1
    omega
  have hzold : z ∈ M.atoms := (Finset.mem_insert.mp hz).resolve_left h2
  have hdeg : M.deg z = 4 := by
    simpa only [Molecule.deg,cut_dartsAt_other M h1 h2] using hd4
  simp only [cutSource,h1,h2,ite_false]
  exact hc z hzold hdeg

end WaveTurbulence.Mole
