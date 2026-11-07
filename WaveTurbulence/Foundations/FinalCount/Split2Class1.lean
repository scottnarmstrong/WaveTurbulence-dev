/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Split2Gen
import Mathlib.Tactic

/-! # The first class of the two-chain split (finalcount-g8, F6-1)

`class1_bound`: the decorations of `𝕄₀` that have a good pair of multipliers `(g₁, g₂)` whose transported decoration
of `𝕄₁` fails `Q` are counted by operation (d) twice (`opDW`), and the count of the second post is the first
clause of `SplitBound`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **First class**: some good pair of multipliers transports `κ` to a decoration of `𝕄₁` that fails `Q`. -/
def Cls1 {M₀ : Molecule V D} (Ta : TwoExit M₀) (Tb : TwoExit Ta.post) {Dcl : Type*}
    (Φ : Degen.RetainedDart Ta.post Tb.Y ⊕ Bool ≃ Dcl) {d : ℕ} (Q : (Dcl → (Fin d → ℤ)) → Prop)
    (Bs : Finset V) (L γ η : ℝ) (κ : D → (Fin d → ℤ)) : Prop :=
  ∃ g₁ ∈ Icc (0 : ℤ) 4, ∃ g₂ ∈ Icc (0 : ℤ) 4, Ta.PostGoodOff Bs L γ (η / 2) κ g₁ ∧
    Tb.PostGoodOff (Bs \ Ta.Y) L γ (η / 2 / 2) (Ta.postLabels κ g₁) g₂ ∧
    ¬ Q (MoleProp.relabelDartLabels Φ (Tb.postLabels (Ta.postLabels κ g₁) g₂))

theorem class1_bound {d : ℕ} {L γ δ η C1 ε₁ : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1)
    {M₀ : Molecule V D} (Ta : TwoExit M₀) (Tb : TwoExit Ta.post) (Bs : Finset V)
    (hcap : ∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2) (hloop : ∀ z, M₀.atom z ≠ M₀.atom (M₀.mate z))
    (hconn : ∀ a ∈ M₀.atoms, ∀ b ∈ M₀.atoms, M₀.SameComponent a b)
    (hY3a : Ta.Y.card ≤ 3) (hcha : ∀ b ∈ Ta.Y, M₀.outdeg b = 1 ∧ M₀.indeg b = 1)
    (hYconna : ∀ a ∈ Ta.Y, ∀ b ∈ Ta.Y, (piece M₀ Ta.Y).SameComponent a b)
    (hpostA : ∀ a ∈ Ta.post.atoms, ∀ b ∈ Ta.post.atoms, Ta.post.SameComponent a b)
    (hopenA : ∀ S ∈ MoleProp.ladderCells Ta.post, GoodCell Ta.post S)
    (hcap1 : ∀ a ∈ Ta.post.atoms, Ta.post.outdeg a ≤ 2 ∧ Ta.post.indeg a ≤ 2)
    (hloop1 : ∀ z, Ta.post.atom z ≠ Ta.post.atom (Ta.post.mate z))
    (hY3b : Tb.Y.card ≤ 3) (hchb : ∀ b ∈ Tb.Y, Ta.post.outdeg b = 1 ∧ Ta.post.indeg b = 1)
    (hYconnb : ∀ a ∈ Tb.Y, ∀ b ∈ Tb.Y, (piece Ta.post Tb.Y).SameComponent a b)
    (hpostB : ∀ a ∈ Tb.post.atoms, ∀ b ∈ Tb.post.atoms, Tb.post.SameComponent a b)
    (hopenB : ∀ S ∈ MoleProp.ladderCells Tb.post, GoodCell Tb.post S)
    (hBs : (Bs \ Ta.Y) \ Tb.Y = ∅)
    {Dcl : Type*} [Fintype Dcl] [DecidableEq Dcl] (cl : Molecule V Dcl)
    (Φ : Degen.RetainedDart Ta.post Tb.Y ⊕ Bool ≃ Dcl)
    (hA : Tb.post.atoms = cl.atoms) (ha : ∀ x, cl.atom (Φ x) = Tb.post.atom x)
    (hm : ∀ x, cl.mate (Φ x) = Φ (Tb.post.mate x)) (ho : ∀ x, cl.out (Φ x) = Tb.post.out x)
    (Q : (Dcl → (Fin d → ℤ)) → Prop)
    (hQ1 : ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells cl, 0 ≤ P S) →
      MoleProp.countAFree cl L γ δ C1 (0 : Mom d)
        (fun κ => lgAdm cl L γ (η / 2 / 2) P κ ∧ ¬ Q κ) P ≤ ENNReal.ofReal ε₁)
    (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells M₀, 0 ≤ P S)
    (Adm : (D → (Fin d → ℤ)) → Prop) (hAdm : ∀ κ, Adm κ → lgAdmOff M₀ Bs L γ η P κ) :
    MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) (fun κ => Adm κ ∧ Cls1 Ta Tb Φ Q Bs L γ η κ) P ≤
      ENNReal.ofReal (21125 * Real.log L ^ (14 : ℝ)) *
        (ENNReal.ofReal (21125 * Real.log L ^ (14 : ℝ)) * ENNReal.ofReal ε₁) := by
  classical
  have hA1 := opDW hL hlog hδ hC1 M₀ Ta hcap hloop hconn Bs hY3a hcha hYconna hpostA hopenA P hP
    (fun κ => Adm κ ∧ Cls1 Ta Tb Φ Q Bs L γ η κ) (fun κ h => hAdm κ h.1)
    (fun g₁ κ => ∃ g₂ ∈ Icc (0 : ℤ) 4, Tb.PostGoodOff (Bs \ Ta.Y) L γ (η / 2 / 2) (Ta.postLabels κ g₁) g₂ ∧
      ¬ Q (MoleProp.relabelDartLabels Φ (Tb.postLabels (Ta.postLabels κ g₁) g₂)))
    (by
      rintro κ ⟨hκ, g₁, hg₁, g₂, hg₂, hpa, hpb, hnq⟩ _
      exact ⟨g₁, hg₁, hpa, g₂, hg₂, hpb, hnq⟩)
  refine hA1.trans (mul_le_mul' le_rfl ?_)
  refine iSup₂_le fun g₁ hg₁ => ?_
  unfold TwoExit.afreeSupPost
  refine iSup₂_le fun P' hP' => ?_
  have hB1 := opDW (η := η / 2) hL hlog hδ hC1 Ta.post Tb hcap1 hloop1 hpostA (Bs \ Ta.Y) hY3b hchb hYconnb hpostB
    hopenB P' hP'
    (Ta.postAdmOff Bs (fun κ => Adm κ ∧ Cls1 Ta Tb Φ Q Bs L γ η κ)
      (fun g₁ κ => ∃ g₂ ∈ Icc (0 : ℤ) 4, Tb.PostGoodOff (Bs \ Ta.Y) L γ (η / 2 / 2) (Ta.postLabels κ g₁) g₂ ∧
        ¬ Q (MoleProp.relabelDartLabels Φ (Tb.postLabels (Ta.postLabels κ g₁) g₂))) L γ (η / 2) P' g₁)
    (fun κ' h => h.1)
    (fun g₂ κ' => ¬ Q (MoleProp.relabelDartLabels Φ (Tb.postLabels κ' g₂)))
    (by
      rintro κ' ⟨_, κ, _, _, ⟨g₂, hg₂, hpb, hnq⟩, rfl⟩ _
      exact ⟨g₂, hg₂, hpb, hnq⟩)
  refine hB1.trans (mul_le_mul' le_rfl ?_)
  refine iSup₂_le fun g₂ hg₂ => ?_
  unfold TwoExit.afreeSupPost
  refine iSup₂_le fun P'' hP'' => ?_
  have hcells := MoleProp.ladderCells_eq_of_dart_equiv Tb.post cl Φ hA ha hm ho
  refine (MoleProp.countAFree_le_of_dart_equiv Tb.post cl Φ hA ha hm ho L γ δ C1 0 _
    (fun κ => lgAdm cl L γ (η / 2 / 2) P'' κ ∧ ¬ Q κ) ?_ P'').trans
    (hQ1 P'' (fun S hS => hP'' S (by rw [hcells]; exact hS)))
  rintro κ''' ⟨hlg, κ', _, _, hnq, rfl⟩
  rw [hBs] at hlg
  exact ⟨lgAdm_relabel Tb.post cl Φ hA ha hm ho (lgAdmOff_empty hlg), hnq⟩

end WaveTurbulence.FinalCountG8
