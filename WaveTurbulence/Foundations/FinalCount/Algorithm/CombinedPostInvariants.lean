/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.CombinedPostTransport
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ConditionedDeletionInvariants
import Mathlib.Tactic

/-! # The sequential combined post predicate retains physical witnesses -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable {M : Molecule V D} {P Q : AppbPattern}

theorem combinedSequential_witness (r : AppbRealization M P) (s : AppbRealization r.post Q)
    (v0 : M.atoms) {d : ℕ} (A : (D → (Fin d → ℤ)) → Prop)
    (q : Fin (r.combinedPattern s).edges.length → (Fin d → ℤ))
    {ζ : Degen.RetainedDart r.post s.removedAtoms → (Fin d → ℤ)}
    (hζ : combinedSequentialAdmissibility r s v0 A q ζ) :
    ∃ κ,A κ ∧ (∀ x,κ (M.mate x) = κ x) ∧
      (r.combinedRemoval s v0).localLabels κ = q ∧ s.retainedLabels (r.retainedLabels κ) = ζ := by
  obtain ⟨κ,hκ,hm,hq,hr⟩ := hζ
  refine ⟨κ,hκ,hm,hq,?_⟩
  funext x
  let f := combinedPostDartEquiv r s v0
  have hh := congrFun hr (f.symm x)
  change κ x.val.val = ζ (f (f.symm x)) at hh
  rw [f.apply_symm_apply] at hh
  exact hh

theorem combinedSequential_largeGap (r : AppbRealization M P) (s : AppbRealization r.post Q)
    (v0 : M.atoms) {d : ℕ} {L g : ℝ} {w : Mom d} {A : (D → (Fin d → ℤ)) → Prop}
    (q : Fin (r.combinedPattern s).edges.length → (Fin d → ℤ))
    (h : ∀ κ,A κ → AppbLargeGap M L w κ g) :
    ∀ ζ,combinedSequentialAdmissibility r s v0 A q ζ → AppbLargeGap s.post L w ζ g := by
  intro ζ hζ
  obtain ⟨κ,hκ,hm,hq,hr⟩ := combinedSequential_witness r s v0 A q hζ
  rw [← hr]
  exact appb_largeGap_eraseAtoms r.post s.removedAtoms (appb_largeGap_eraseAtoms M r.removedAtoms (h κ hκ))

theorem combinedSequential_mate_labels (r : AppbRealization M P) (s : AppbRealization r.post Q)
    (v0 : M.atoms) {d : ℕ} (A : (D → (Fin d → ℤ)) → Prop)
    (q : Fin (r.combinedPattern s).edges.length → (Fin d → ℤ)) :
    ∀ ζ,combinedSequentialAdmissibility r s v0 A q ζ → ∀ x,ζ (s.post.mate x) = ζ x := by
  intro ζ hζ x
  obtain ⟨κ,hκ,hm,hq,hr⟩ := combinedSequential_witness r s v0 A q hζ
  rw [← hr]
  exact hm x.val.val

theorem combinedSequential_validLinkScales (r : AppbRealization M P) (s : AppbRealization r.post Q)
    (v0 : M.atoms) {d : ℕ} {L c : ℝ} {w : Mom d} {A : (D → (Fin d → ℤ)) → Prop}
    {scales : Finset V → ℝ} (q : Fin (r.combinedPattern s).edges.length → (Fin d → ℤ))
    (h : AppbValidLinkScales M L w A c scales) :
    AppbValidLinkScales s.post L w (combinedSequentialAdmissibility r s v0 A q) c scales := by
  apply ((h.eraseAtoms r.removedAtoms).eraseAtoms s.removedAtoms).mono
  intro ζ hζ
  obtain ⟨κ,hκ,hm,hq,hr⟩ := combinedSequential_witness r s v0 A q hζ
  exact ⟨r.retainedLabels κ,⟨κ,hκ,rfl⟩,hr.symm⟩

end WaveTurbulence.Mole.AppbAlgorithm
