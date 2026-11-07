/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformR32TailFiber
public import WaveTurbulence.Foundations.FinalCount.AppBR32FiveIndices
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformFixedThirdFine
import Mathlib.Tactic

/-! # Last internal-pair count after fixing the indirect five-label projection -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

theorem uniform_r32_five_tail_fiber_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r3.pattern)
      (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms),
    ∀ (S : Finset V) (hS : S ⊆ r.post.atoms) (j : Fin 3) (which : Bool),
      appbCrossingBonds M S = {(r.edge j).val,(s.edge ⟨0,by decide⟩).val.val} →
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
    ∀ Q : Finset (Fin (r.combinedPattern s).edges.length → (Fin d → ℤ)),
      Q ⊆ (r.combinedRemoval s v0).localChoices p hLp γ δ w Adm →
      ∀ z : Fin 5 → (Fin d → ℤ), (∀ q ∈ Q,(fun k => q (appbR32FiveIndices r s j which k)) = z) →
      (Q.card : ℝ) ≤ L^((d : ℝ)-γ-3*η/4) := by
  classical
  obtain ⟨L₀,hL₀⟩ := uniform_triple_fixed_third_fine_bound d hd δ γ η hδ hγ hη hηγ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M r s v0 S hS j which hcross p w Adm hLG Q hQ z hz
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
    let R := Q.image tail
    let π : Equiv.Perm (Fin 3) := Equiv.swap j 0
    have hprefix : ∀ q ∈ Q,∀ k : Fin 3,q (r.combinedLeftIndex s k) = b.localLabels κ0 (r.combinedLeftIndex s k) := by
      intro q hq k
      have hh := congrFun ((hz q hq).trans (hz q0 hq0).symm) (Fin.castAdd 2 (π.symm k))
      rw [appb_r32_five_indices_left,show (Equiv.swap j 0) (π.symm k) = k from π.apply_symm_apply k] at hh
      rw [hκq0]
      exact hh
    have hfirst {κ : D → (Fin d → ℤ)} (hκ : κ ∈ p.decorations L γ δ w Adm)
        (hq : b.localLabels κ ∈ Q) : r.localLabels κ = qfirst := by
      change (fun k : Fin 3 => r.localLabels κ k) = (fun k : Fin 3 => r.localLabels κ0 k)
      funext k
      have hh := hprefix _ hq k
      have hL1 := r.combined_labels_left s v0 κ k
      have hL2 := r.combined_labels_left s v0 κ0 k
      rw [hL1,hL2] at hh
      exact hh
    have hLG' : ∀ κ,Adm' κ → AppbLargeGap r.post L w κ (L^(-γ+η)) := by
      intro κ hκ
      obtain ⟨κold,hA,hm,hq,hr⟩ := hκ
      subst κ
      exact appb_largeGap_eraseAtoms M r.removedAtoms (hLG κold hA)
    have hsubset : R ⊆ s.localChoices pp hLp γ δ w Adm' := by
      intro q hq
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
      obtain ⟨κ,hκ,hκu⟩ := (b.mem_localChoices p hLp γ δ w Adm u).mp (hQ hu)
      have hpost := r.deletion_maps_conditioned p L γ δ w Adm hκ (hfirst hκ (hκu.symm ▸ hu))
      apply (s.mem_localChoices pp hLp γ δ w Adm' _).mpr
      refine ⟨r.retainedLabels κ,hpost,?_⟩
      funext k
      rw [← r.combined_labels_right s v0 κ k]
      exact congrFun hκu (r.combinedRightIndex s k)
    have hbridge : ∀ q ∈ R,q ⟨0,by decide⟩ = s.localLabels (r.retainedLabels κ0) ⟨0,by decide⟩ := by
      intro q hq
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
      obtain ⟨κ,hκ,hκu⟩ := (b.mem_localChoices p hLp γ δ w Adm u).mp (hQ hu)
      have hefirst : b.localLabels κ cut.first = b.localLabels κ0 cut.first := hprefix _ (hκu.symm ▸ hu) j
      have hsecond := cut.second_label_eq hLp.ne' w p.momentum κ κ0 hκ.1 hκ0.1 hefirst
      change b.localLabels κ (r.combinedRightIndex s ⟨0,by decide⟩) = b.localLabels κ0 (r.combinedRightIndex s ⟨0,by decide⟩) at hsecond
      rw [hκu,r.combined_labels_right] at hsecond
      exact hsecond
    have hE1 : appbR32FiveIndices r s j which (Fin.natAdd 3 (0 : Fin 2)) = r.combinedRightIndex s (s.specialFirst which) := by
      rw [appb_r32_five_indices_right,show (0 : Fin 2).succ = (1 : Fin 3) by decide,(s.specialFrame_indices which).2.1]
    have hE2 : appbR32FiveIndices r s j which (Fin.natAdd 3 (1 : Fin 2)) = r.combinedRightIndex s (s.specialSecond which) := by
      rw [appb_r32_five_indices_right,show (1 : Fin 2).succ = (2 : Fin 3) by decide,(s.specialFrame_indices which).2.2]
    have hinner1 : ∀ q ∈ R,q (s.specialFirst which) = s.localLabels (r.retainedLabels κ0) (s.specialFirst which) := by
      intro q hq
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
      have hh := congrFun ((hz u hu).trans (hz q0 hq0).symm) (Fin.natAdd 3 (0 : Fin 2))
      rw [hE1,← hκq0] at hh
      have hR0 := r.combined_labels_right s v0 κ0 (s.specialFirst which)
      rw [hR0] at hh
      exact hh
    have hinner2 : ∀ q ∈ R,q (s.specialSecond which) = s.localLabels (r.retainedLabels κ0) (s.specialSecond which) := by
      intro q hq
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
      have hh := congrFun ((hz u hu).trans (hz q0 hq0).symm) (Fin.natAdd 3 (1 : Fin 2))
      rw [hE2,← hκq0] at hh
      have hR0 := r.combined_labels_right s v0 κ0 (s.specialSecond which)
      rw [hR0] at hh
      exact hh
    let ρ : Equiv.Perm (Fin 3) := Equiv.ofBijective (![1,2,0]) (by decide)
    let t := (s.specialFrame (!which)).reindex ρ
    have ht0 : t.index 0 = s.specialFirst (!which) := (s.specialFrame_indices (!which)).2.1
    have ht1 : t.index 1 = s.specialSecond (!which) := (s.specialFrame_indices (!which)).2.2
    have ht2 : t.index 2 = ⟨0,by decide⟩ := (s.specialFrame_indices (!which)).1
    let f := fun q : Fin AppbPatternKind.s33new3.pattern.edges.length → (Fin d → ℤ) => (q (t.index 0),q (t.index 1))
    have hi : Set.InjOn f (R : Set _) := by
      intro q hq q' hq' he
      have h0 := (hbridge q hq).trans (hbridge q' hq').symm
      have h1 := (hinner1 q hq).trans (hinner1 q' hq').symm
      have h2 := (hinner2 q hq).trans (hinner2 q' hq').symm
      have h3 := congrArg Prod.fst he
      have h4 := congrArg Prod.snd he
      change q (t.index 0) = q' (t.index 0) at h3
      change q (t.index 1) = q' (t.index 1) at h4
      rw [ht0] at h3
      rw [ht1] at h4
      cases which
      · funext k
        fin_cases k
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
      · funext k
        fin_cases k
        · exact h0
        · exact h3
        · exact h4
        · exact h1
        · exact h2
    have hb := hL₀ V _ L hL hLp r.post _ s (s.specialAtom (!which)) (s.special_atom_removed (!which)) t
      pp w Adm' (s.localLabels (r.retainedLabels κ0) ⟨0,by decide⟩) R hsubset (by simpa only [ht2] using hbridge) (by
        intro hsign κ hκ
        exact appb_tripleFrame_pair_gap s t (s.special_atom_removed (!which)) L w κ _ hκ.1.1 (hLG' κ hκ.2.2) 0 1 (by decide) hsign)
    rw [Finset.card_image_of_injOn hi] at hb
    have hiTail : Set.InjOn tail (Q : Set _) := by
      intro q hq q' hq' he
      funext k
      rcases r.combined_index_cases s k with ⟨i,rfl⟩ | ⟨i,rfl⟩
      · exact (hprefix q hq i).trans (hprefix q' hq' i).symm
      · exact congrFun he i
    have hc : R.card = Q.card := Finset.card_image_of_injOn hiTail
    rw [hc] at hb
    exact hb
  · have he : Q = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end WaveTurbulence.Mole.AppbAlgorithm
