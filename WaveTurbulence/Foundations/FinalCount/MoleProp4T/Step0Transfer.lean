/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.SplitBound
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitBoundAdm
import Mathlib.Tactic

/-! # Pulling the decoration split back through one (Y2) sequence

Let `𝕄′` (`T.post`) come from `𝕄` by a (Y) sequence ending in (Y2), and let `Q₁` split the decorations of `𝕄′`. Its pull
back `pullQ T Q₁` holds for a decoration of `𝕄` when some multiplier `g ∈ {0,…,4}` makes the transported decoration
of `𝕄′` LG and in `Q₁`.
* `split_first_Y2`: `𝔄(𝕄; ¬ pullQ) ≤ K · ε₁` from `𝔄(𝕄′; ¬Q₁) ≤ ε₁`.
* `split_second_removed`: if `ℓ` is removed by the sequence, `𝔄(𝕄 ∖ ℓ; pullQ) ≤ K · ε₂` from
  `𝔄(𝕄′ ∖ ℓ′; Q₁) ≤ ε₂`, `ℓ′` the new bond.
Each lemma is at fixed `L`, taking the general (Y2) bound it uses as a hypothesis.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace TwoExit
variable {M : Molecule V D} (T : TwoExit M)

/-- **The pull-back of a condition on post decorations.** -/
def pullQ {d : ℕ} (L γ η : ℝ) (Q₁ : (Degen.RetainedDart M T.Y ⊕ Bool → (Fin d → ℤ)) → Prop)
    (κ : D → (Fin d → ℤ)) : Prop :=
  ∃ g ∈ Finset.Icc (0 : ℤ) 4, MoleProp.LargeGap T.post L γ (η / 2) 0 (T.postLabels κ g) ∧ Q₁ (T.postLabels κ g)

/-- **The first alternative through a (Y2) sequence.** -/
theorem split_first_Y2 (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) {d : ℕ} {L γ δ η C1 K ε₁ : ℝ}
    (hL1 : 1 ≤ L) (hL11 : 11 ≤ L ^ (η / 2)) (P : Finset V → ℝ)
    (hY2 : ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdm M L γ η P κ) →
      ∀ W : ℤ → (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → (∀ x, κ (M.mate x) = κ x) →
        ∃ g ∈ Finset.Icc (0 : ℤ) 4, MoleProp.LargeGap T.post L γ (η / 2) 0 (T.postLabels κ g) ∧ W g κ) →
        MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal K * ⨆ g ∈ Finset.Icc (0 : ℤ) 4,
            AFreeSupAdm T.post d L γ δ C1 fun P' => T.postAdm Adm W L γ (η / 2) P' g)
    (Q₁ : (Degen.RetainedDart M T.Y ⊕ Bool → (Fin d → ℤ)) → Prop)
    (hQ₁ : ∀ P' : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells T.post, 0 ≤ P' S) →
      MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (fun τ => lgAdm T.post L γ (η / 2) P' τ ∧ ¬ Q₁ τ) P' ≤
        ENNReal.ofReal ε₁) :
    MoleProp.countAFree M L γ δ C1 (0 : Mom d) (fun κ => lgAdm M L γ η P κ ∧ ¬ T.pullQ L γ η Q₁ κ) P ≤
      ENNReal.ofReal K * ENNReal.ofReal ε₁ := by
  refine (hY2 _ (fun κ h => h.1) (fun _ _ => True) (fun κ hκ hsym => ?_)).trans (mul_le_mul' le_rfl ?_)
  · obtain ⟨g, hg, hLG⟩ := T.exists_post_largeGap hL1 hL11 hsym hcap hκ.1.1
    exact ⟨g, hg, hLG, trivial⟩
  refine iSup₂_le fun g hg => iSup₂_le fun P' hP' => (countAFree_mono_adm _ fun τ hτ => ⟨hτ.1, ?_⟩).trans (hQ₁ P' hP')
  obtain ⟨hlg, κ, ⟨_, hnq⟩, _, _, rfl⟩ := hτ
  exact fun hq => hnq ⟨g, hg, hlg.1, hq⟩

end TwoExit

/-- Retained darts for equal erased sets. -/
def retainedCongr (M : Molecule V D) {Y Y' : Finset V} (h : Y = Y') : Degen.RetainedDart M Y ≃ Degen.RetainedDart M Y' :=
  Equiv.subtypeEquivRight fun x => by rw [h]

namespace Y2End
variable {M : Molecule V D} {C : YChain M} (E : Y2End C)

/-- **The second alternative through a (Y2) sequence removing `ℓ`.** -/
theorem split_second_removed (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) (e : D)
    (hYe : M.atom e ∈ C.set ∨ M.atom (M.mate e) ∈ C.set) {d : ℕ} {L γ δ η C1 K ε₂ : ℝ} (P : Finset V → ℝ)
    (hsec : ∀ Adm : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm κ → lgAdm (MoleProp.eraseBond M e) L γ η P κ) →
      ∀ Φ : (Degen.RetainedDart M C.set → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → Φ (resY M e C.set hYe κ)) →
        MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal K * AFreeSupAdm (Degen.eraseAtoms M C.set) d L γ δ C1
            (fun P' τ => lgAdm (Degen.eraseAtoms M C.set) L γ (η / 2) P' τ ∧ Φ τ))
    (Q₁ : (Degen.RetainedDart M (E.toTwoExit hcap).Y ⊕ Bool → (Fin d → ℤ)) → Prop)
    (hQ₁ : ∀ P' : Finset V → ℝ,
      (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inr true)), 0 ≤ P' S) →
      MoleProp.countAFree (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inr true)) L γ δ C1 (0 : Mom d)
        (fun τ => lgAdm (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inr true)) L γ (η / 2) P' τ ∧
          MoleProp.erasedBondAdmissibility (E.toTwoExit hcap).post (Sum.inr true)
            (fun κ0 => MoleProp.LargeGap (E.toTwoExit hcap).post L γ (η / 2) 0 κ0 ∧ Q₁ κ0) τ) P' ≤
        ENNReal.ofReal ε₂) :
    MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d)
      (fun κ => lgAdm (MoleProp.eraseBond M e) L γ η P κ ∧
        MoleProp.erasedBondAdmissibility M e
          (fun κ0 => MoleProp.LargeGap M L γ η 0 κ0 ∧ (E.toTwoExit hcap).pullQ L γ η Q₁ κ0) κ) P ≤
      ENNReal.ofReal K * ENNReal.ofReal ε₂ := by
  have hTY : (E.toTwoExit hcap).Y = C.set := E.toTwoExit_Y hcap
  -- the dart equivalence `𝕄 ∖ chain ≅ 𝕄′ ∖ ℓ′`
  let f := (retainedCongr M hTY.symm).trans (E.toTwoExit hcap).eraseNewEquiv
  have hA : (Degen.eraseAtoms M C.set).atoms = (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inr true)).atoms := by
    change M.atoms \ C.set = (E.toTwoExit hcap).post.atoms; rw [(E.toTwoExit hcap).post_atoms, hTY]
  have ha : ∀ x, (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inr true)).atom (f x) = (Degen.eraseAtoms M C.set).atom x :=
    fun _ => rfl
  have hm : ∀ x, (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inr true)).mate (f x) = f ((Degen.eraseAtoms M C.set).mate x) :=
    fun _ => rfl
  have ho : ∀ x, (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inr true)).out (f x) = (Degen.eraseAtoms M C.set).out x :=
    fun _ => rfl
  let Φ : (Degen.RetainedDart M C.set → (Fin d → ℤ)) → Prop := fun τ =>
    MoleProp.erasedBondAdmissibility (E.toTwoExit hcap).post (Sum.inr true)
      (fun κ0 => MoleProp.LargeGap (E.toTwoExit hcap).post L γ (η / 2) 0 κ0 ∧ Q₁ κ0) (MoleProp.relabelDartLabels f τ)
  refine (hsec _ (fun κ h => h.1) Φ ?_).trans (mul_le_mul' le_rfl (iSup₂_le fun P' hP' => ?_))
  · -- the condition holds for restrictions
    rintro κ'' ⟨_, κ, ⟨_, g, _, hLG, hq⟩, hsym, rfl⟩
    refine ⟨(E.toTwoExit hcap).postLabels κ g, ⟨hLG, hq⟩, (E.toTwoExit hcap).postLabels_mate hsym g, ?_⟩
    funext ⟨z, hz⟩
    rcases z with w | bo
    · rfl
    · exact absurd (by cases bo <;> [exact hz.2 rfl; exact (hz.1 rfl).elim]) id
  · have hcells : ∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inr true)), 0 ≤ P' S := by
      intro S hS
      rw [← ladderCells_eq_of_dart_equiv' _ _ f hA ha hm ho] at hS
      exact hP' S hS
    refine le_trans ?_ (hQ₁ P' hcells)
    refine MoleProp.countAFree_le_of_dart_equiv _ _ f hA ha hm ho L γ δ C1 0 _ _ (fun τ h => ⟨?_, h.2⟩) P'
    exact lgAdm_relabel _ _ f hA ha hm ho h.1

end Y2End
end WaveTurbulence.MoleProp4
