/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameConservation
public import WaveTurbulence.Foundations.FinalCount.AppBSignedPairNormalization
public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalPairFine
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionCounting
import Mathlib.Tactic

/-! # Fine pair count inside a triple when the copied boundary label is fixed -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

/-- Actual finite local tuples with the third frame label fixed. This is
the internal-pair counting input to the local cut-count assembly. -/
theorem uniform_triple_fixed_third_fine_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P),
    ∀ v ∈ r.removedAtoms, ∀ t : AppbTripleFrame r v,
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
      (z : Fin d → ℤ) (Q : Finset (Fin P.edges.length → (Fin d → ℤ))),
      Q ⊆ r.localChoices p hLp γ δ w Adm → (∀ q ∈ Q,q (t.index 2) = z) →
      (appbIncidenceSign M v (r.edge (t.index 0)).val ≠ appbIncidenceSign M v (r.edge (t.index 1)).val →
        ∀ κ,κ ∈ p.decorations L γ δ w Adm →
        L^(-γ+η) ≤ ‖Molecule.kvec L w κ (r.edge (t.index 0)).val-
          Molecule.kvec L w κ (r.edge (t.index 1)).val‖) →
      ((Q.image (fun q => (q (t.index 0),q (t.index 1)))).card : ℝ) ≤
        L^((d : ℝ)-γ-3*η/4) := by
  classical
  obtain ⟨L₀,hL₀⟩ := appb_physical_pair_fine_bound d hd δ γ η hδ hγ hη hηγ 0
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M P r v hv t p w Adm z Q hQ hz hgap
  let σ := appbIncidenceSign M v (r.edge (t.index 0)).val
  let ρ := appbIncidenceSign M v (r.edge (t.index 1)).val
  let υ := appbIncidenceSign M v (r.edge (t.index 2)).val
  let Z := w+latticePoint L z
  let ε := σ⁻¹*ρ
  let s := Q.image (fun q => (q (t.index 0),q (t.index 1)))
  apply hL₀ L hL w (p.center (r.edge (t.index 0)).val) (p.center (r.edge (t.index 1)).val)
    (((σ⁻¹ : ℤˣ) : ℤ) • (p.momentum v-(υ : ℤ) • Z))
    (((σ⁻¹ : ℤˣ) : ℤ)*(p.energy v-(υ : ℤ)*‖Z‖^2)) ε s
  · intro q hq
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
    obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hLp γ δ w Adm u).mp (hQ hu)
    have hZ : Molecule.kvec L w (r.localLabels κ) (t.index 2) = Z := by
      change w+latticePoint L (r.localLabels κ (t.index 2)) = Z
      rw [hz _ hu]
    have hm := r.local_momentum L w p.momentum κ hκ.1 hv
    rw [t.sum_incidence,Fin.sum_univ_three,hZ] at hm
    have he := r.local_energy L γ δ w p.momentum p.energy p.center κ hκ.1 hκ.2.1 hv
    rw [t.sum_incidence,Fin.sum_univ_three,hZ] at he
    simp only [zsmul_eq_mul] at he
    refine ⟨r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 (t.index 0),
      r.local_spatial L γ δ w p.energy p.center κ hκ.2.1 (t.index 1),?_,?_⟩
    · exact appb_signed_pair_momentum σ ρ _ _ _ (eq_sub_iff_add_eq.mpr hm)
    · have hpair : |(σ : ℤ)*‖Molecule.kvec L w (r.localLabels κ) (t.index 0)‖^2+
          (ρ : ℤ)*‖Molecule.kvec L w (r.localLabels κ) (t.index 1)‖^2-
          (p.energy v-(υ : ℤ)*‖Z‖^2)| ≤ δ⁻¹*L^(-2*γ) := by
        convert he using 1 <;> congr 1 <;> ring
      have hh := appb_signed_pair_energy σ ρ _ _ _ _ hpair
      simpa only [appbWidth,pow_zero,mul_one,ε,Molecule.kvec] using hh
  · intro he q hq
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
    obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hLp γ δ w Adm u).mp (hQ hu)
    apply hgap ?_ κ hκ
    intro hs
    change σ = ρ at hs
    have hone : ε = 1 := by dsimp only [ε]; rw [hs]; simp
    rw [hone] at he
    norm_num at he

end WaveTurbulence.Mole.AppbAlgorithm
