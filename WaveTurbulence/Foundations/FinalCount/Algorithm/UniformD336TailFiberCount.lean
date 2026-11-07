/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformD336FixedSharedCount
public import WaveTurbulence.Foundations.FinalCount.AppBD336HeadReconstruction
public import WaveTurbulence.Foundations.FinalCount.AppBD336LabelMaps
public import WaveTurbulence.Foundations.FinalCount.AppBConditionedDeletion
import Mathlib.Tactic

/-! # Remaining four labels after fixing the first triple in split 3D3New -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

theorem uniform_d336_tail_fiber_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.d33new.pattern),
      (∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) → r.post.numComponents = 2 →
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
    ∀ Q : Finset (Fin AppbPatternKind.d33new.pattern.edges.length → (Fin d → ℤ)),
      Q ⊆ r.localChoices p hLp γ δ w Adm →
      ∀ z : Fin 3 → (Fin d → ℤ), (∀ q ∈ Q,(appbD336FirstTriple r).project q = z) →
      (Q.card : ℝ) ≤ L^(2*((d : ℝ)-γ)-3*η/2) := by
  classical
  obtain ⟨L₀,hL₀⟩ := uniform_d336_fixed_shared_count_bound d hd δ γ η hδ hγ hη hηγ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M r hc hF p w Adm hLG Q hQ z hz
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
    have hhead : ∀ q ∈ Q,∀ j : Fin 5,q (appbD336HeadEmbedding j) = r.localLabels κ0 (appbD336HeadEmbedding j) := by
      intro q hq
      obtain ⟨κ,hκ,hκq⟩ := (r.mem_localChoices p hLp γ δ w Adm q).mp (hQ hq)
      have he : (appbD336FirstTriple r).project (r.localLabels κ) =
          (appbD336FirstTriple r).project (r.localLabels κ0) := by
        rw [hκq,hκq0]
        exact (hz q hq).trans (hz q0 hq0).symm
      have hh := appb_d336_head_eq_of_first_triple r hc hF hLp.ne' w p.momentum κ κ0 hκ.1 hκ0.1 he
      simpa only [hκq] using hh
    have hfirst {κ : D → (Fin d → ℤ)} (hκ : κ ∈ p.decorations L γ δ w Adm)
        (hq : r.localLabels κ ∈ Q) : r1.localLabels κ = qfirst := by
      funext j
      change (appbD336FirstPair r).localLabels κ j = (appbD336FirstPair r).localLabels κ0 j
      simp only [appb_d336_first_local_labels]
      exact hhead _ hq ⟨j.val,by have hj := j.isLt; change j.val < 4 at hj; omega⟩
    have hLG' : ∀ κ,Adm' κ → AppbLargeGap r1.post L w κ (L^(-γ+η)) := by
      intro κ hκ
      obtain ⟨κold,hA,hm,hq,hr⟩ := hκ
      subst κ
      exact appb_largeGap_eraseAtoms M r1.removedAtoms (hLG κold hA)
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
    have hfixed : ∀ q ∈ Q.image tail,q ⟨0,by decide⟩ = r.localLabels κ0 ⟨4,by decide⟩ := by
      intro q hq
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
      exact hhead u hu ⟨4,by decide⟩
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
    have hb := hL₀ V _ L hL hLp r1.post s pp w Adm' hLG' (r.localLabels κ0 ⟨4,by decide⟩)
      (Q.image tail) hsubset hfixed
    rw [Finset.card_image_of_injOn hi] at hb
    exact hb
  · have he : Q = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end WaveTurbulence.Mole.AppbAlgorithm
