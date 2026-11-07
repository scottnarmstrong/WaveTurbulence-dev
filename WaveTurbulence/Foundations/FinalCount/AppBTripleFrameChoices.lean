/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameConservation
public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalTriple
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionCounting
import Mathlib.Tactic

/-! # Counting the actual three-label projection inside a larger removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 basiccount(2) on an actual degree-three support, while allowing
additional local bonds elsewhere in the removed group. -/
theorem appb_tripleFrame_projection_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L ≥ L₀, ∀ hLp : 0 < L, ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P),
      M.IsMolecule → ∀ v ∈ r.removedAtoms,∀ t : AppbTripleFrame r v,
      ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (((r.localChoices p hLp γ δ w Adm).image t.project).card : ℝ) ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ)) := by
  classical
  obtain ⟨C,L₀,hC,hL₀⟩ := appb_physical_triple_bound d hd γ hγ
  refine ⟨C,L₀,hC,?_⟩
  intro L hL hLp δ hδ M P r hM v hv t p w Adm
  obtain ⟨π,hsame,hopp⟩ := t.exists_order hM (r.removedAtoms_subset hv)
  let Q := r.localChoices p hLp γ δ w Adm
  let s0 := Q.image t.project
  let encode := fun q : Fin 3 → (Fin d → ℤ) => (q (π 0),q (π 1),q (π 2))
  let s := s0.image encode
  let σ := appbIncidenceSign M v (r.edge (t.index (π 0))).val
  have hb := hL₀ L hL hLp δ hδ w (p.center (r.edge (t.index (π 0))).val)
    (p.center (r.edge (t.index (π 1))).val) (p.center (r.edge (t.index (π 2))).val)
    (((σ⁻¹ : ℤˣ) : ℤ) • p.momentum v) (((σ⁻¹ : ℤˣ) : ℤ)*p.energy v) s (by
      intro q hq
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hz
      obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hLp γ δ w Adm u).mp hu
      exact ⟨r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 (t.index (π 0)),
        r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 (t.index (π 1)),
        r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 (t.index (π 2)),
        t.momentum π hsame hopp hv L w p.momentum κ hκ.1,
        t.energy π hsame hopp hv L γ δ w p.momentum p.energy p.center κ hκ.1 hκ.2.1⟩)
  have hc : s.card = s0.card := card_image_of_injective s0 (appb_triple_permutation_encoding_injective π)
  rw [hc] at hb
  exact hb

end WaveTurbulence.Mole
