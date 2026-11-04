/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.InputFactors
public import WaveTurbulence.Foundations.Sumint.ProductMeasureTools

/-!
# The actual Lebesgue coordinates of the independent time factors

Each linear, pair and normal factor has respectively one, two and three
real coordinates. The dependent sum of these finite coordinate sets is
explicitly equivalent to the source time index.
-/

public section

open MeasureTheory

namespace WaveTurbulence.Sumint

/-- The one, two or three coordinate labels of each source factor. -/
abbrev FactorCoordinate (S : SumintShape) : FactorIdx S → Type
  | .inl _ => Fin 1
  | .inr (.inl _) => Fin 2
  | .inr (.inr _) => Fin 3

instance (S : SumintShape) (a : FactorIdx S) : Fintype (FactorCoordinate S a) := by
  rcases a with i | (p | i) <;> dsimp [FactorCoordinate] <;> infer_instance

/-- Send a factor coordinate to its literal source time coordinate. -/
@[expose] def factorCoordinateTime (S : SumintShape) :
    (Σ a : FactorIdx S, FactorCoordinate S a) → S.TVar
  | ⟨.inl i,_⟩ => .inl ⟨i,0⟩
  | ⟨.inr (.inl p),j⟩ => if j = 0 then .inl ⟨p.1,p.2.succ⟩ else .inr (.inl p)
  | ⟨.inr (.inr i),j⟩ => .inr (.inr ⟨i,j⟩)

/-- Its inverse distinguishes the zero linear coordinate from the positive pair coordinates. -/
@[expose] def timeFactorCoordinate (S : SumintShape) :
    S.TVar → (Σ a : FactorIdx S, FactorCoordinate S a)
  | .inl ⟨i,j⟩ => Fin.cases ⟨.inl i,0⟩ (fun k => ⟨.inr (.inl ⟨i,k⟩),0⟩) j
  | .inr (.inl p) => ⟨.inr (.inl p),1⟩
  | .inr (.inr ⟨i,j⟩) => ⟨.inr (.inr i),j⟩

/-- Exact source coordinate equivalence; this is a permutation, with no scaling. -/
@[expose] def factorCoordinateTimeEquiv (S : SumintShape) :
    (Σ a : FactorIdx S, FactorCoordinate S a) ≃ S.TVar where
  toFun := factorCoordinateTime S
  invFun := timeFactorCoordinate S
  left_inv := by
    rintro ⟨a,j⟩
    rcases a with i | (p | i)
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rfl
    · fin_cases j <;> rfl
    · rfl
  right_inv := by
    rintro (⟨i,j⟩ | (p | ⟨i,j⟩))
    · refine Fin.cases ?_ (fun _ => ?_) j <;> rfl
    · rfl
    · rfl

/-- Regroup the source real coordinates by factor, retaining finite-coordinate form. -/
@[expose] noncomputable def timeCoordinateGrouping (S : SumintShape) :
    (S.TVar → ℝ) ≃ᵐ ((a : FactorIdx S) → FactorCoordinate S a → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (factorCoordinateTimeEquiv S).symm).trans
    (MeasurableEquiv.piCurry (fun (a : FactorIdx S) (_ : FactorCoordinate S a) => ℝ))

/-- The grouping preserves the precise product Lebesgue measure used in the draft. -/
theorem volume_preserving_timeCoordinateGrouping (S : SumintShape) :
    MeasurePreserving (timeCoordinateGrouping S) volume volume := by
  exact (volume_measurePreserving_piCurry (ι := FactorIdx S)
    (κ := FactorCoordinate S)).comp
      (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (factorCoordinateTimeEquiv S).symm)

/-- Its linear coordinate is exactly the source distinguished time. -/
theorem timeCoordinateGrouping_linear (S : SumintShape) (τ : S.TVar → ℝ) (i : Fin S.I) :
    timeCoordinateGrouping S τ (.inl i) 0 = τ (.inl ⟨i,0⟩) := rfl

/-- Its pair coordinates are exactly the source outer and inner times. -/
theorem timeCoordinateGrouping_pair (S : SumintShape) (τ : S.TVar → ℝ)
    (p : Σ i : Fin S.I, Fin (S.m i)) :
    timeCoordinateGrouping S τ (.inr (.inl p)) 0 = τ (.inl ⟨p.1,p.2.succ⟩) ∧
      timeCoordinateGrouping S τ (.inr (.inl p)) 1 = τ (.inr (.inl p)) := ⟨rfl,rfl⟩

/-- Its normal coordinates are exactly the three source normal times. -/
theorem timeCoordinateGrouping_normal (S : SumintShape) (τ : S.TVar → ℝ)
    (i : {i : Fin S.I // S.nor i = true}) (j : Fin 3) :
    timeCoordinateGrouping S τ (.inr (.inr i)) j = τ (.inr (.inr ⟨i,j⟩)) := rfl

end WaveTurbulence.Sumint
