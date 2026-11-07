/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.StarEquations
public import WaveTurbulence.Foundations.FinalCount.Degen.LatticeLabels
import Mathlib.Tactic

/-! # The actual three-incidence local counting problem in DH23 10.1 -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem ordered_triple_momentum (M : Molecule V D) {d : ℕ} (L : ℝ)
    {v : V} (hv : v ∈ M.atoms) (e : Fin 3 ≃ IncidentDart M v)
    (b : Bool) (h0 : M.out (e 0).val = b) (h1 : M.out (e 1).val = !b)
    (h2 : M.out (e 2).val = b) {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) :
    latticePoint L (κ (e 0).val) - latticePoint L (κ (e 1).val) +
      latticePoint L (κ (e 2).val) = if b then c v else -c v := by
  have h := ordered_star_momentum M L (0 : Mom d) hv e hd
  simp only [Fin.sum_univ_three] at h
  cases b
  · simp [h0,h1,h2,Molecule.dartSign,Molecule.kvec] at h ⊢
    rw [← h]
    abel
  · simpa [h0,h1,h2,Molecule.dartSign,Molecule.kvec,sub_eq_add_neg] using h

theorem ordered_triple_energy (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    {v : V} (hv : v ∈ M.atoms) (e : Fin 3 ≃ IncidentDart M v)
    (b : Bool) (h0 : M.out (e 0).val = b) (h1 : M.out (e 1).val = !b)
    (h2 : M.out (e 2).val = b) {β : V → ℝ} {k0 : D → Mom d}
    {κ : D → (Fin d → ℤ)} (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ) :
    |‖latticePoint L (κ (e 0).val)‖ ^ 2 - ‖latticePoint L (κ (e 1).val)‖ ^ 2 +
      ‖latticePoint L (κ (e 2).val)‖ ^ 2 - (if b then β v else -β v)| ≤ δ⁻¹ * L ^ (-2*γ) := by
  have h := ordered_star_energy M L γ δ (0 : Mom d) hv e hr
  simp only [Fin.sum_univ_three] at h
  cases b
  · simp [h0,h1,h2,Molecule.dartSign,Molecule.kvec] at h ⊢
    rw [← abs_neg] at h
    convert h using 1 <;> congr 1 <;> ring
  · simpa [h0,h1,h2,Molecule.dartSign,Molecule.kvec,sub_eq_add_neg] using h

/-- Fixing the source charges fixes the canonical integer momentum of
all actual local triples, without assuming those charges vanish. -/
theorem ordered_triple_integer_momentum_eq (M : Molecule V D) {d : ℕ} {L : ℝ}
    (hL : L ≠ 0) {v : V} (hv : v ∈ M.atoms) (e : Fin 3 ≃ IncidentDart M v)
    (b : Bool) (h0 : M.out (e 0).val = b) (h1 : M.out (e 1).val = !b)
    (h2 : M.out (e 2).val = b) {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd' : M.IsDecoration L (0 : Mom d) c κ') :
    κ (e 0).val - κ (e 1).val + κ (e 2).val =
      κ' (e 0).val - κ' (e 1).val + κ' (e 2).val := by
  have he := (ordered_triple_momentum M L hv e b h0 h1 h2 hd).trans
    (ordered_triple_momentum M L hv e b h0 h1 h2 hd').symm
  apply Degen.coset_label_injective hL (0 : Mom d)
  simpa only [zero_add,WeylSums.latticePoint_add_eq,WeylSums.latticePoint_sub_eq] using he

/-- Ordered triple values determine every actual incidence at the atom. -/
theorem starTriple_injective (M : Molecule V D) (v : V) (e : Fin 3 ≃ IncidentDart M v)
    {K : Type*} : Function.Injective (fun q : IncidentDart M v → K => (q (e 0),q (e 1),q (e 2))) := by
  intro q q' h
  funext x
  obtain ⟨i,rfl⟩ := e.surjective x
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg (fun t => t.2.1) h
  · exact congrArg (fun t => t.2.2) h

/-- DH23 basiccount(2) applied to the literal local labels at a degree-three
atom. The source charges may be nonzero and the graph is not otherwise
restricted; the alternating incidence enumeration is typing/orientation data. -/
theorem star_three_count_bound (d : ℕ) (hdim : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ L ≥ L₀, 0 < L → ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D) (v : V), v ∈ M.atoms →
    ∀ (e : Fin 3 ≃ IncidentDart M v) (b : Bool),
      M.out (e 0).val = b → M.out (e 1).val = !b → M.out (e 2).val = b →
    ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (S : Finset (D → (Fin d → ℤ))),
      (∀ κ ∈ S, M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ) →
      ((S.image (starLabels M v)).card : ℝ) ≤ C * δ⁻¹ * L ^ (2*((d : ℝ)-γ)) := by
  classical
  obtain ⟨C,R,hbound⟩ := CountLemmas.atomTriple_bound d hdim γ hγ
  refine ⟨max C 0,R,le_max_right _ _,?_⟩
  intro L hL hL0 δ hδ V' D' _ _ _ M v hv e b h0 h1 h2 c β k0 S hS
  by_cases hne : S.Nonempty
  · obtain ⟨κ0,hκ0⟩ := hne
    let nk := κ0 (e 0).val - κ0 (e 1).val + κ0 (e 2).val
    let β' := if b then β v else -β v
    let a0 := k0 (e 0).val
    let a1 := k0 (e 1).val
    let a2 := k0 (e 2).val
    let f := fun q : IncidentDart M v → (Fin d → ℤ) => (q (e 0),q (e 1),q (e 2))
    let T := (S.image (starLabels M v)).image f
    have hcard : T.card = (S.image (starLabels M v)).card := card_image_of_injective _ (starTriple_injective M v e)
    obtain ⟨hf,hb⟩ := hbound L hL δ hδ β' nk a0 a1 a2
    have hsub : (T : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))) ⊆
        CountLemmas.atomTripleSet L a0 a1 a2 nk β' (δ⁻¹*L^(-2*γ)) := by
      intro q hq
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hq
      obtain ⟨κ,hκ,rfl⟩ := mem_image.mp ht
      have hd := (hS κ hκ).1
      have hr := (hS κ hκ).2
      refine ⟨?_,?_,?_,?_,?_⟩
      · simpa only [CountLemmas.NearLattice,Molecule.kvec,zero_add,f,starLabels,a0,a1,a2] using hr.2 (e 0).val
      · simpa only [CountLemmas.NearLattice,Molecule.kvec,zero_add,f,starLabels,a0,a1,a2] using hr.2 (e 1).val
      · simpa only [CountLemmas.NearLattice,Molecule.kvec,zero_add,f,starLabels,a0,a1,a2] using hr.2 (e 2).val
      · exact ordered_triple_integer_momentum_eq M hL0.ne' hv e b h0 h1 h2 hd (hS κ0 hκ0).1
      · exact ordered_triple_energy M L γ δ hv e b h0 h1 h2 hr
    have hn : T.card ≤ (CountLemmas.atomTripleSet L a0 a1 a2 nk β' (δ⁻¹*L^(-2*γ))).ncard := by
      simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub hf
    have hnR : (T.card : ℝ) ≤ (CountLemmas.atomTripleSet L a0 a1 a2 nk β' (δ⁻¹*L^(-2*γ))).ncard := by exact_mod_cast hn
    rw [hcard] at hnR
    exact (hnR.trans hb).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (inv_nonneg.mpr hδ.1.le)) (by positivity))
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst S
    simp only [image_empty,card_empty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (le_max_right C 0) (inv_nonneg.mpr hδ.1.le)) (Real.rpow_nonneg hL0.le _)

end WaveTurbulence.MoleProp
