/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBR32Frame
public import WaveTurbulence.Foundations.FinalCount.AppBR32CutPair
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformSpecialFixedShared
public import WaveTurbulence.Foundations.FinalCount.AppBConditionedDeletion
public import WaveTurbulence.Foundations.FinalCount.AppBCutPairDifference
import Mathlib.Tactic

/-! # The two residual internal pairs after fixing the original star triple -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

theorem uniform_r32_tail_fiber_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r3.pattern)
      (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms),
    ∀ (S : Finset V) (hS : S ⊆ r.post.atoms) (j : Fin AppbPatternKind.r3.pattern.edges.length),
      appbCrossingBonds M S = {(r.edge j).val,(s.edge ⟨0,by decide⟩).val.val} →
    ∀ (π : Equiv.Perm (Fin 3)) (p : AppbCountParameters M d) (w : Mom d)
      (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
    ∀ Q : Finset (Fin (r.combinedPattern s).edges.length → (Fin d → ℤ)),
      Q ⊆ (r.combinedRemoval s v0).localChoices p hLp γ δ w Adm →
      ∀ z : Fin 3 → (Fin d → ℤ), (∀ q ∈ Q,(appbR32Frame r s v0 π).project q = z) →
      (Q.card : ℝ) ≤ L^(2*((d : ℝ)-γ)-3*η/2) := by
  classical
  obtain ⟨L₀,hL₀⟩ := uniform_special_fixed_shared_count_bound d hd δ γ η hδ hγ hη hηγ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M r s v0 S hS j hcross π p w Adm hLG Q hQ z hz
  let b := r.combinedRemoval s v0
  let cut := appbR32CutPair r s v0 S hS j hcross
  by_cases hn : Q.Nonempty
  · obtain ⟨q0,hq0⟩ := hn
    obtain ⟨κ0,hκ0,hκq0⟩ := (b.mem_localChoices p hLp γ δ w Adm q0).mp (hQ hq0)
    let qfirst := r.localLabels κ0
    let pp := r.deletionParameters p L w qfirst
    let Adm' := r.conditionedPostAdmissibility Adm qfirst
    let tail := fun q : Fin (r.combinedPattern s).edges.length → (Fin d → ℤ) =>
      fun k : Fin AppbPatternKind.s33new3.pattern.edges.length => q (r.combinedRightIndex s k)
    have hfirst {κ : D → (Fin d → ℤ)} (hκ : κ ∈ p.decorations L γ δ w Adm)
        (hq : b.localLabels κ ∈ Q) : r.localLabels κ = qfirst := by
      apply appb_r32_first_labels_eq_of_frame r s v0 π κ κ0
      rw [hκq0]
      exact (hz _ hq).trans (hz q0 hq0).symm
    have hprefix : ∀ q ∈ Q,∀ k,q (r.combinedLeftIndex s k) = r.localLabels κ0 k := by
      intro q hq k
      obtain ⟨κ,hκ,hκq⟩ := (b.mem_localChoices p hLp γ δ w Adm q).mp (hQ hq)
      rw [← hκq,r.combined_labels_left]
      exact congrFun (hfirst hκ (hκq.symm ▸ hq)) k
    have hLG' : ∀ κ,Adm' κ → AppbLargeGap r.post L w κ (L^(-γ+η)) := by
      intro κ hκ
      obtain ⟨κold,hA,hm,hq,hr⟩ := hκ
      subst κ
      exact appb_largeGap_eraseAtoms M r.removedAtoms (hLG κold hA)
    have hsubset : Q.image tail ⊆ s.localChoices pp hLp γ δ w Adm' := by
      intro q hq
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
      obtain ⟨κ,hκ,hκu⟩ := (b.mem_localChoices p hLp γ δ w Adm u).mp (hQ hu)
      have hpost := r.deletion_maps_conditioned p L γ δ w Adm hκ (hfirst hκ (hκu.symm ▸ hu))
      apply (s.mem_localChoices pp hLp γ δ w Adm' _).mpr
      refine ⟨r.retainedLabels κ,hpost,?_⟩
      funext k
      rw [← r.combined_labels_right s v0 κ k]
      exact congrFun hκu (r.combinedRightIndex s k)
    have hfixed : ∀ q ∈ Q.image tail,q ⟨0,by decide⟩ = s.localLabels (r.retainedLabels κ0) ⟨0,by decide⟩ := by
      intro q hq
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
      obtain ⟨κ,hκ,hκu⟩ := (b.mem_localChoices p hLp γ δ w Adm u).mp (hQ hu)
      have hefirst : b.localLabels κ cut.first = b.localLabels κ0 cut.first := by
        change b.localLabels κ (r.combinedLeftIndex s j) = b.localLabels κ0 (r.combinedLeftIndex s j)
        rw [r.combined_labels_left,r.combined_labels_left]
        exact congrFun (hfirst hκ (hκu.symm ▸ hu)) j
      have hsecond := cut.second_label_eq hLp.ne' w p.momentum κ κ0 hκ.1 hκ0.1 hefirst
      change b.localLabels κ (r.combinedRightIndex s ⟨0,by decide⟩) =
        b.localLabels κ0 (r.combinedRightIndex s ⟨0,by decide⟩) at hsecond
      rw [hκu,r.combined_labels_right] at hsecond
      exact hsecond
    have hi : Set.InjOn tail (Q : Set _) := by
      intro q hq q' hq' he
      funext i
      rcases r.combined_index_cases s i with ⟨k,rfl⟩ | ⟨k,rfl⟩
      · exact (hprefix q hq k).trans (hprefix q' hq' k).symm
      · exact congrFun he k
    have hb := hL₀ V _ L hL hLp r.post s pp w Adm' hLG'
      (s.localLabels (r.retainedLabels κ0) ⟨0,by decide⟩) (Q.image tail) hsubset hfixed
    rw [Finset.card_image_of_injOn hi] at hb
    exact hb
  · have he : Q = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end WaveTurbulence.Mole.AppbAlgorithm
