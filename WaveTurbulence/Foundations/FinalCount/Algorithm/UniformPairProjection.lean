/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPairIncidence
public import WaveTurbulence.Foundations.FinalCount.AppBSignedPairNormalization
public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceGap
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionCounting
import Mathlib.Tactic

/-! # Actual pair-projection saving inside larger removals -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset Set
universe u v

/-- Basiccount(1) bounds the actual removed-label tuples. The graph premises
say precisely that the selected pair is the full incidence support of the deleted atom. LG is a standing source premise on admissible decorations. -/
theorem uniform_localPair_projection_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ L₀ : ℝ,
    ∀ (V : Type u) (D : Type v) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ (M : Molecule V D) (P : AppbPattern)
      (r : AppbRealization M P) (v : V) (t : AppbLocalPair r v),
      v ∈ r.removedAtoms →
      ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ, Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∀ hLp : 0 < L,
      (((r.localChoices p hLp γ δ w Adm).image t.project).card : ℝ) ≤ L^((d : ℝ)-γ-3*η/4) := by
  classical
  obtain ⟨L₀,hL₀⟩ := appb_physical_pair_fine_bound d hd δ γ η hδ hγ hη hηγ 0
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL M P r v t hv p w Adm hLG hLp'
  let i := t.first
  let j := t.second
  let σ := appbIncidenceSign M v (r.edge i).val
  let τ := appbIncidenceSign M v (r.edge j).val
  let ε := σ⁻¹*τ
  let Q := r.localChoices p hLp' γ δ w Adm
  let s := Q.image t.project
  have hraw := hL₀ L hL w (p.center (r.edge i).val) (p.center (r.edge j).val)
    (((σ⁻¹ : ℤˣ) : ℤ) • p.momentum v) (((σ⁻¹ : ℤˣ) : ℤ)*p.energy v) ε s
  have hs : ∀ q ∈ s,
      ‖w+latticePoint L q.1-p.center (r.edge i).val‖ ≤ 1 ∧
      ‖w+latticePoint L q.2-p.center (r.edge j).val‖ ≤ 1 ∧
      (w+latticePoint L q.1)+(ε : ℤ) • (w+latticePoint L q.2) = ((σ⁻¹ : ℤˣ) : ℤ) • p.momentum v ∧
      |‖w+latticePoint L q.1‖^2+(ε : ℤ)*‖w+latticePoint L q.2‖^2-
        ((σ⁻¹ : ℤˣ) : ℤ)*p.energy v| ≤ appbWidth δ γ 0 L := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
    obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hLp' γ δ w Adm z).mp hz
    refine ⟨r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 i,
      r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 j,?_,?_⟩
    · exact appb_signed_pair_momentum σ τ _ _ _ (t.momentum hv L w p.momentum κ hκ.1)
    · have hh := appb_signed_pair_energy σ τ _ _ _ _
        (t.energy hv L γ δ w p.momentum p.energy p.center κ hκ.1 hκ.2.1)
      simpa only [appbWidth,pow_zero,mul_one,AppbLocalPair.project,Molecule.kvec,ε,i,j] using hh
  have hg : ε = -1 → ∀ q ∈ s,L^(-γ+η) ≤ ‖(w+latticePoint L q.1)-(w+latticePoint L q.2)‖ := by
    intro he q hq
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
    obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hLp' γ δ w Adm z).mp hz
    have hst : σ ≠ τ := by
      intro hst
      have hone : ε = 1 := by dsimp only [ε]; rw [hst]; simp
      rw [hone] at he
      norm_num at he
    have hne : (r.edge i).val ≠ (r.edge j).val := by
      intro heq
      exact t.distinct (r.edge.injective (Subtype.ext heq))
    have ho (k : Fin P.edges.length) : M.out (r.edge k).val = true :=
      (mem_filter.mp (mem_filter.mp (r.edge k).property).1).2
    exact appb_incidence_large_gap M L w κ _ hκ.1.1 (hLG κ hκ.2.2)
      (r.removedAtoms_subset hv) t.incidence_first t.incidence_second (ho i) (ho j) hne hst
  have hc := hraw hs hg
  exact hc

end WaveTurbulence.Mole.AppbAlgorithm
