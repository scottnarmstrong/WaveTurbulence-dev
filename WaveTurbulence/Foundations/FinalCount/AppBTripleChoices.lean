/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleConservation
public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalTriple
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionCounting
import Mathlib.Tactic

/-! # Actual local-choice bound for three incident outgoing bonds -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 basiccount(2) applies to every actual three-bond deletion with
one full degree-three incidence support. Source degree caps supply the
orientation ordering. The constant is uniform in all graph parameters. -/
theorem appb_three_bond_localChoices_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L ≥ L₀, ∀ hLp : 0 < L, ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P),
      M.IsMolecule → P.edges.length = 3 → ∀ v ∈ r.removedAtoms,
      (∀ i,appbIncidence M v (r.edge i).val = 1) →
      ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      ((r.localChoices p hLp γ δ w Adm).card : ℝ) ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ)) := by
  classical
  obtain ⟨C,L₀,hC,hL₀⟩ := appb_physical_triple_bound d hd γ hγ
  refine ⟨C,L₀,hC,?_⟩
  intro L hL hLp δ hδ M P r hM hlen v hv hinc p w Adm
  obtain ⟨t⟩ := appb_localTriple_exists r hM hlen (r.removedAtoms_subset hv) hinc
  let Q := r.localChoices p hLp γ δ w Adm
  let s := Q.image t.project
  let σ := appbIncidenceSign M v (r.edge t.first).val
  have hb := hL₀ L hL hLp δ hδ w (p.center (r.edge t.first).val)
    (p.center (r.edge t.middle).val) (p.center (r.edge t.last).val)
    (((σ⁻¹ : ℤˣ) : ℤ) • p.momentum v) (((σ⁻¹ : ℤˣ) : ℤ)*p.energy v) s (by
      intro q hq
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
      obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hLp γ δ w Adm z).mp hz
      exact ⟨r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 t.first,
        r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 t.middle,
        r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 t.last,
        t.momentum hv L w p.momentum κ hκ.1,
        t.energy hv L γ δ w p.momentum p.energy p.center κ hκ.1 hκ.2.1⟩)
  simpa only [s,card_image_of_injective Q t.project_injective] using hb

end WaveTurbulence.Mole
