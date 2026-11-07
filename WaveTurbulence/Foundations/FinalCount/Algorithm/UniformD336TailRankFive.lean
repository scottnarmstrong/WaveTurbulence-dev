/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD336ResidualChoices
public import WaveTurbulence.Foundations.FinalCount.AppBD336FirstFour
public import WaveTurbulence.Foundations.FinalCount.AppBD336HeadReconstruction
public import WaveTurbulence.Foundations.FinalCount.AppBD336LabelMaps
public import WaveTurbulence.Foundations.FinalCount.AppBConditionedDeletion
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionMolecule
import Mathlib.Tactic

/-! # Remaining four labels after fixing the first triple in split 3D3New -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

theorem uniform_d336_tail_rank_five_fiber_bound (d : ℕ) (hd : 3 ≤ d) (δ γ : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33new.pattern),
      M.IsMolecule →
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
    ∀ Q : Finset (Fin AppbPatternKind.d33new.pattern.edges.length → (Fin d → ℤ)),
      Q ⊆ r.localChoices p hLp γ δ w Adm →
      ∀ z : Fin 3 → (Fin d → ℤ), (∀ q ∈ Q,(appbD336FirstTriple r).project q = z) →
      (Q.card : ℝ) ≤ L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4) := by
  classical
  obtain ⟨L₀,hL₀⟩ := uniform_d336_residual_localChoices_bound d hd γ hγ δ hδ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M r hM p w Adm Q hQ z hz
  by_cases hn : Q.Nonempty
  · obtain ⟨q0,hq0⟩ := hn
    obtain ⟨κ0,hκ0,hκq0⟩ := (r.mem_localChoices p hLp γ δ w Adm q0).mp (hQ hq0)
    let r1 := appbD336FirstPair r
    let s := appbD336SecondPair r
    let qfirst := r1.localLabels κ0
    let pp := r1.deletionParameters p L w qfirst
    let Adm' := r1.conditionedPostAdmissibility Adm qfirst
    let tail := fun q : Fin AppbPatternKind.d33new.pattern.edges.length → (Fin d → ℤ) =>
      fun j : Fin appbD336ResidualPattern.edges.length => q (appbD336SecondEmbedding j)
    have hhead : ∀ q ∈ Q,∀ j : Fin AppbPatternKind.d33.pattern.edges.length,q (appbD336FirstEmbedding j) = r.localLabels κ0 (appbD336FirstEmbedding j) := by
      intro q hq
      obtain ⟨κ,hκ,hκq⟩ := (r.mem_localChoices p hLp γ δ w Adm q).mp (hQ hq)
      have he : (appbD336FirstTriple r).project (r.localLabels κ) =
          (appbD336FirstTriple r).project (r.localLabels κ0) := by
        rw [hκq,hκq0]
        exact (hz q hq).trans (hz q0 hq0).symm
      have hh := appb_d336_first_four_eq_of_first_triple r hLp.ne' w p.momentum κ κ0 hκ.1 hκ0.1 he
      simpa only [hκq] using hh
    have hfirst {κ : D → (Fin d → ℤ)} (hκ : κ ∈ p.decorations L γ δ w Adm)
        (hq : r.localLabels κ ∈ Q) : r1.localLabels κ = qfirst := by
      funext j
      change (appbD336FirstPair r).localLabels κ j = (appbD336FirstPair r).localLabels κ0 j
      simp only [appb_d336_first_local_labels]
      exact hhead _ hq j
    have hsubset : Q.image tail ⊆ s.localChoices pp hLp γ δ w Adm' := by
      intro q hq
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
      obtain ⟨κ,hκ,hκu⟩ := (r.mem_localChoices p hLp γ δ w Adm u).mp (hQ hu)
      have hpost := r1.deletion_maps_conditioned p L γ δ w Adm hκ (hfirst hκ (hκu.symm ▸ hu))
      apply (s.mem_localChoices pp hLp γ δ w Adm' _).mpr
      refine ⟨r1.retainedLabels κ,hpost,?_⟩
      funext j
      rw [appb_d336_second_local_labels]
      exact congrFun hκu (appbD336SecondEmbedding j)
    have hi : Set.InjOn tail (Q : Set _) := by
      intro q hq q' hq' he
      funext i
      fin_cases i
      · exact (hhead q hq ⟨0,by decide⟩).trans (hhead q' hq' ⟨0,by decide⟩).symm
      · exact (hhead q hq ⟨1,by decide⟩).trans (hhead q' hq' ⟨1,by decide⟩).symm
      · exact (hhead q hq ⟨2,by decide⟩).trans (hhead q' hq' ⟨2,by decide⟩).symm
      · exact (hhead q hq ⟨3,by decide⟩).trans (hhead q' hq' ⟨3,by decide⟩).symm
      · exact congrFun he ⟨0,by decide⟩
      · exact congrFun he ⟨1,by decide⟩
      · exact congrFun he ⟨2,by decide⟩
      · exact congrFun he ⟨3,by decide⟩
      · exact congrFun he ⟨4,by decide⟩
    have hb := hL₀ V _ L hL hLp r1.post s (appb_eraseAtoms_isMolecule M hM r1.removedAtoms) pp w Adm'
    have hcard := Finset.card_le_card hsubset
    have hcard' : ((Q.image tail).card : ℝ) ≤ (s.localChoices pp hLp γ δ w Adm').card := by exact_mod_cast hcard
    rw [Finset.card_image_of_injOn hi] at hcard'
    exact hcard'.trans hb
  · have he : Q = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end WaveTurbulence.Mole.AppbAlgorithm
