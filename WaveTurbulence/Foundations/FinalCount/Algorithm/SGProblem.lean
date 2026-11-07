/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.Problem
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ComponentNormalizedProduct
public import WaveTurbulence.Foundations.FinalCount.Algorithm.AdmissibilityPartition
import Mathlib.Tactic

/-! # Counting problems with at most `ws` small-gap atoms (DH23 L1834)

DH23 Proposition 10.2 allows at most `w` atoms to be SG in the decoration (L553: an atom of
degree four whose opposite pairs are not separated).  The set of SG atoms depends on the
decoration, so `ProblemSG` stores, for every admissible decoration, some set `S` of at most
`ws` atoms off which the large-gap condition holds.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Large gap at every atom outside `S`. -/
def AppbLargeGapOff (M : Molecule V D) (S : Finset V) {d : ℕ} (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (g : ℝ) : Prop :=
  ∀ v ∈ M.atoms, v ∉ S → ∀ x ∈ M.dartsAt v, ∀ y ∈ M.dartsAt v,
    M.out x ≠ M.out y → y ≠ M.mate x →
    g ≤ ‖Molecule.kvec L w κ x - Molecule.kvec L w κ y‖

/-- Removing exactly the exceptional atoms leaves a large-gap molecule. -/
theorem appb_largeGapOff_eraseAtoms (M : Molecule V D) (S : Finset V) {d : ℕ}
    {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {g : ℝ}
    (h : AppbLargeGapOff M S L w κ g) :
    AppbLargeGap (Degen.eraseAtoms M S) L w (fun x => κ x.val) g := by
  intro v hv x hx y hy hdir hmate
  have hv' := mem_sdiff.mp hv
  have hx' : x.val ∈ M.dartsAt v := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩
  have hy' : y.val ∈ M.dartsAt v := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2⟩
  have hm : y.val ≠ M.mate x.val := by
    intro he
    exact hmate (Subtype.ext he)
  exact h v hv'.1 hv'.2 x.val hx' y.val hy' hdir hm

end WaveTurbulence.Mole

namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
open Finset
universe u v

variable {V : Type v} [DecidableEq V] {d : ℕ} {L c g : ℝ} {w : Mom d}
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A counting problem all of whose admissible decorations are large gap off some set of at
most `ws` atoms. -/
structure ProblemSG (V : Type v) [DecidableEq V] (d : ℕ) (L : ℝ) (w : Mom d) (c g : ℝ)
    (ws : ℕ) where
  state : State.{u,v} V
  admissible : (state.Dart → (Fin d → ℤ)) → Prop
  scales : Finset V → ℝ
  molecule : state.graph.IsMolecule
  noLoops : AppbNoLoops state.graph
  scales_nonneg : ∀ S,0 ≤ scales S
  validLinkScales : AppbValidLinkScales state.graph L w admissible c scales
  mateLabels : ∀ κ,admissible κ → ∀ x,κ (state.graph.mate x) = κ x
  largeGap : ∀ κ,admissible κ → ∃ S ⊆ state.graph.atoms, S.card ≤ ws ∧
    AppbLargeGapOff state.graph S L w κ g

noncomputable def ProblemSG.value {ws : ℕ} (p : ProblemSG.{u,v} V d L w c g ws) (γ δ C1 : ℝ) :
    ℝ≥0∞ :=
  appbLinkCountA p.state.graph L γ δ C1 w p.admissible p.scales

/-- A problem that is large gap everywhere is an SG problem with no exceptional atoms. -/
def Problem.toSG (p : Problem.{u,v} V d L w c g) : ProblemSG.{u,v} V d L w c g 0 where
  state := p.state
  admissible := p.admissible
  scales := p.scales
  molecule := p.molecule
  noLoops := p.noLoops
  scales_nonneg := p.scales_nonneg
  validLinkScales := p.validLinkScales
  mateLabels := p.mateLabels
  largeGap := fun κ hκ => ⟨∅,empty_subset _,by simp,fun v hv _ x hx y hy hd hm =>
    p.largeGap κ hκ v hv x hx y hy hd hm⟩

/-- The finite union bound over the exceptional set. -/
theorem linkCountA_le_finset_cover {ι : Type*} [DecidableEq ι] (M : Molecule V D) (L γ δ C1 : ℝ)
    (w : Mom d) (P : Finset V → ℝ) (A : ι → (D → (Fin d → ℤ)) → Prop) (T : Finset ι) :
    ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ,Adm κ → ∃ i ∈ T,A i κ) →
    appbLinkCountA M L γ δ C1 w Adm P ≤
      ∑ i ∈ T,appbLinkCountA M L γ δ C1 w (fun κ => Adm κ ∧ A i κ) P := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro Adm h
    have h0 : appbCountE M L γ δ w Adm = 0 := by
      unfold appbCountE
      refine le_antisymm (iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_) bot_le
      have : {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ} = ∅ := by
        ext κ
        simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
        intro hκ
        obtain ⟨i,hi,-⟩ := h κ hκ.2.2
        simp at hi
      rw [this]; simp
    unfold appbLinkCountA
    rw [h0]; simp
  | insert a T ha ih =>
    intro Adm h
    have h1 := linkCountA_le_admissibility_cover M L γ δ C1 w Adm (fun κ => Adm κ ∧ A a κ)
      (fun κ => Adm κ ∧ ¬A a κ) P (fun κ hκ => by
        by_cases hh : A a κ
        · exact Or.inl ⟨hκ,hh⟩
        · exact Or.inr ⟨hκ,hh⟩)
    have h2 := ih (fun κ => Adm κ ∧ ¬A a κ) (fun κ hκ => by
      obtain ⟨i,hi,hA⟩ := h κ hκ.1
      rcases mem_insert.mp hi with rfl | hi
      · exact absurd hA hκ.2
      · exact ⟨i,hi,hA⟩)
    rw [sum_insert ha]
    refine h1.trans (add_le_add le_rfl (h2.trans (sum_le_sum fun i _ => ?_)))
    exact linkCountA_mono M L γ δ C1 w P (fun κ hκ => ⟨hκ.1.1,hκ.2⟩)

/-- The decoration set of an SG problem is covered by the problems with a fixed exceptional set. -/
theorem ProblemSG.value_le_sum {ws : ℕ} (p : ProblemSG.{u,v} V d L w c g ws) (γ δ C1 : ℝ) :
    p.value γ δ C1 ≤
      ∑ S ∈ p.state.graph.atoms.powerset.filter (fun S => S.card ≤ ws),
        appbLinkCountA p.state.graph L γ δ C1 w
          (fun κ => p.admissible κ ∧ AppbLargeGapOff p.state.graph S L w κ g) p.scales := by
  apply linkCountA_le_finset_cover p.state.graph L γ δ C1 w p.scales
    (fun S κ => AppbLargeGapOff p.state.graph S L w κ g)
  intro κ hκ
  obtain ⟨S,hS,hc,hg⟩ := p.largeGap κ hκ
  exact ⟨S,mem_filter.mpr ⟨mem_powerset.mpr hS,hc⟩,hg⟩

end WaveTurbulence.Mole.AppbAlgorithm
