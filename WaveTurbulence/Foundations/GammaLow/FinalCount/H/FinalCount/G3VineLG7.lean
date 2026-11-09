/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineLG7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3MapDec5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3VineLG7`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: `vineLG`, part 7: `HRunC` and `VineLGAt` from the run.**

`HRunC` is the run of the model with the two extra model facts of TARGET Operation 1 and requirement (e):
* **Step 1 removes the collected objects** (L2101: "In Operation 1, we collect all the SG vine-like objects in `C₁` and `C₂` ... we
  remove `U'`"): after the Step-1 phase no dart of any member of `C₁ ∪ C₂` (`Object.ContainsDart`) is a dart of the state;
* **hinges are cut along their designated bonds** (`DesRec`, `subpro` (5), requirement (e)). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {Tm : V → Prop}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀} {a₀ j₁ j₂ : V}

/-- A run from `M_sub` with the collection data of Operation 1 (`C₁` = `C.collection`, `C₂ = C.C2Can Unsel`) and the designated pairs. -/
def HRunC (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (M₀ : Molecule V D₀) (hf : HSt V D₀) (C : CollData M₀)
    (Unsel : Set (Src.Object Src.γL M₀)) : Prop :=
  ∃ h₁ h₂ h₃ : HSt V D₀,
    Relation.ReflTransGen (HStep1 L γ η w κ) (HSt.init M₀) h₁ ∧ NoTripleBond h₁.s.M ∧
    Relation.ReflTransGen (HStep2 L γ η w κ) h₁ h₂ ∧ NoSGTriangle L γ η w κ h₂.s ∧
    Relation.ReflTransGen (HStep3 L γ η w κ) h₂ h₃ ∧ NoSGLeft L γ η w κ (HSt.init M₀).s h₃.s ∧
    Relation.ReflTransGen (HStep4 L w κ) h₃ hf ∧ NoBetaCut L w κ hf.s ∧
    (∀ U, ((∃ i, U = C.collection i) ∨ U ∈ C.C2Can L γ η w κ Unsel) → ∀ x : h₁.s.D, ¬ U.ContainsDart (h₁.s.down x)) ∧
    DesRec C hf

theorem HRunC.toHRun {C : CollData M₀} {Unsel : Set (Src.Object Src.γL M₀)} (h : HRunC L γ η w κ M₀ hf C Unsel) :
    HRun L γ η w κ (HSt.init M₀) hf := by
  obtain ⟨h₁, h₂, h₃, a1, n1, a2, n2, a3, n3, a4, n4, -, -⟩ := h
  exact ⟨h₁, h₂, h₃, a1, n1, a2, n2, a3, n3, a4, n4⟩

theorem HRunC.rem {C : CollData M₀} {Unsel : Set (Src.Object Src.γL M₀)} (h : HRunC L γ η w κ M₀ hf C Unsel) :
    (∀ i, ∀ x : hf.s.D, ¬ (C.collection i).ContainsDart (hf.s.down x)) ∧
    (∀ U ∈ C.C2Can L γ η w κ Unsel, ∀ x : hf.s.D, ¬ U.ContainsDart (hf.s.down x)) := by
  obtain ⟨h₁, h₂, h₃, a1, n1, a2, n2, a3, n3, a4, n4, hrem, -⟩ := h
  have s4 : St.Sub hf.s h₃.s := rtg_sub (fun _ _ h => h.sub) a4
  have s3 : St.Sub h₃.s h₂.s := rtg_sub (fun _ _ h => h.sub) a3
  have s2 : St.Sub h₂.s h₁.s := rtg_sub (fun _ _ h => h.sub) a2
  have key : ∀ U, ((∃ i, U = C.collection i) ∨ U ∈ C.C2Can L γ η w κ Unsel) → ∀ x : hf.s.D,
      ¬ U.ContainsDart (hf.s.down x) := by
    intro U hU x hx
    obtain ⟨x', hx'⟩ := (s4.trans (s3.trans s2)) ⟨x, rfl⟩
    exact hrem U hU x' (by rw [hx']; exact hx)
  exact ⟨fun i x => key _ (Or.inl ⟨i, rfl⟩) x, fun U hU x => key U (Or.inr hU) x⟩

/-! ### The double bond and the gap of a joint -/

theorem vine_of_vineOrDouble (hC : Prop95ConclAt L γ η w κ R hf Tm) {a₀ : V} (ha₀ : a₀ ∈ hf.s.M.atoms)
    (h : (∃ j₁ j₂, (compMol hf.s.M a₀).IsVineEnl (compMol hf.s.M a₀).atoms j₁ j₂) ∨
      ((compMol hf.s.M a₀).atoms.card = 2 ∧ ∀ a ∈ (compMol hf.s.M a₀).atoms, (compMol hf.s.M a₀).deg a = 2)) :
    ∃ j₁ j₂, (compMol hf.s.M a₀).IsVineEnl (compMol hf.s.M a₀).atoms j₁ j₂ := by
  rcases h with h | ⟨hcard, hdeg⟩
  · exact h
  · obtain ⟨j₁, j₂, hne, hat⟩ := Finset.card_eq_two.1 hcard
    refine ⟨j₁, j₂, Or.inl (isVine_I _ hne hat ?_ ?_ ?_ ?_ ?_)⟩
    all_goals first
      | (intro x; exact hC.noloop x.1)
      | skip
    all_goals
      have hm : ∀ j, j ∈ (compMol hf.s.M a₀).atoms → j ∈ hf.s.M.atoms ∧ hf.s.M.SameComponent a₀ j := fun j hj =>
        (mem_compMol _ _).1 hj
    · have hj := hm j₁ (by rw [hat]; simp)
      have := hC.bal.2 j₁ hj.1 (by rw [← compMol_deg _ _ hj.2]; exact hdeg j₁ (by rw [hat]; simp))
      rw [compMol_outdeg _ _ hj.2]; exact this.1
    · have hj := hm j₁ (by rw [hat]; simp)
      have := hC.bal.2 j₁ hj.1 (by rw [← compMol_deg _ _ hj.2]; exact hdeg j₁ (by rw [hat]; simp))
      rw [compMol_indeg _ _ hj.2]; exact this.2
    · have hj := hm j₂ (by rw [hat]; simp)
      have := hC.bal.2 j₂ hj.1 (by rw [← compMol_deg _ _ hj.2]; exact hdeg j₂ (by rw [hat]; simp))
      rw [compMol_outdeg _ _ hj.2]; exact this.1
    · have hj := hm j₂ (by rw [hat]; simp)
      have := hC.bal.2 j₂ hj.1 (by rw [← compMol_deg _ _ hj.2]; exact hdeg j₂ (by rw [hat]; simp))
      rw [compMol_indeg _ _ hj.2]; exact this.2

end WaveTurbulence.GammaLow.FinalCount.H
