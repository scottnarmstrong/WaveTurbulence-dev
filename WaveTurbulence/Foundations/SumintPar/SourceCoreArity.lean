/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceCoreGroupProperties

/-!
# At most eight inputs are affected by fixing two source time coordinates

Every coarse core embeds into four slots: slot zero is its linear
factor, and the other slots are either its first pair or its normal
triple. Those two possibilities cannot coexist. The image of two
selected times therefore has total coarse arity at most eight.
-/

@[expose] public section
set_option autoImplicit false

open scoped Classical

namespace WaveTurbulence.SumintPar

/-- Four slots suffice for every old coordinate within one possible source core. -/
@[expose] def factorCoreSlotCode (S : SumintShape) :
    (a : FactorIdx S) → FactorCoordinate S a → Fin 4
  | .inl _,_ => 0
  | .inr (.inl _),j => ⟨j.val+1,by have hj := j.isLt; omega⟩
  | .inr (.inr _),j => ⟨j.val+1,by have hj := j.isLt; omega⟩

/-- Encode a native coarse coordinate in its four possible slots. -/
@[expose] def sourceCoreCoordinateCode {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S)
    (z : SourceCoreCoordinate D b) : Fin 4 := factorCoreSlotCode D.S z.1.1 z.2

/-- The four-slot encoding is injective on each actual coarse source core. -/
theorem sourceCoreCoordinateCode_injective {d : ℕ} (D : SumintDatum d) (c : FactorIdx D.S) :
    Function.Injective (sourceCoreCoordinateCode D c) := by
  rintro ⟨⟨a,ha⟩,j⟩ ⟨⟨b,hb⟩,k⟩ h
  have hg := ha.trans hb.symm
  rcases a with i | (p | n) <;> rcases b with i' | (p' | n')
  · have hi := Sum.inl.inj hg
    cases hi
    have hj : j = k := Subsingleton.elim _ _
    cases hj
    rfl
  · have hh := congrArg Fin.val h
    change (0:ℕ) = k.val+1 at hh
    omega
  · have hh := congrArg Fin.val h
    change (0:ℕ) = k.val+1 at hh
    omega
  · have hh := congrArg Fin.val h
    change j.val+1 = (0:ℕ) at hh
    omega
  · have hp := sourceCoreGroup_pair_injective D hg
    cases hp
    have hh := congrArg Fin.val h
    change j.val+1 = k.val+1 at hh
    have hj : j = k := Fin.ext (by omega)
    cases hj
    rfl
  · exact False.elim (sourceCoreGroup_pair_ne_normal D p n' hg)
  · have hh := congrArg Fin.val h
    change j.val+1 = (0:ℕ) at hh
    omega
  · exact False.elim (sourceCoreGroup_pair_ne_normal D p' n hg.symm)
  · have hn := sourceCoreGroup_normal_injective D hg
    cases hn
    have hh := congrArg Fin.val h
    change j.val+1 = k.val+1 at hh
    have hj : j = k := Fin.ext (by omega)
    cases hj
    rfl

/-- Every actual coarse core has arity at most four, including unused labels of arity zero. -/
theorem sourceCoreArity_le_four {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S) :
    sourceCoreArity D b ≤ 4 := by
  have hc := Fintype.card_le_of_injective (sourceCoreCoordinateCode D b) (sourceCoreCoordinateCode_injective D b)
  simpa only [sourceCoreArity,Fintype.card_fin] using hc

/-- The total coarse arity in a finite family is bounded by four times its cardinality. -/
theorem sum_sourceCoreArity_le {d : ℕ} (D : SumintDatum d) (s : Finset (FactorIdx D.S)) :
    ∑ b ∈ s, sourceCoreArity D b ≤ 4*s.card := by
  calc
    _ ≤ ∑ _b ∈ s, 4 := Finset.sum_le_sum (fun b _ => sourceCoreArity_le_four D b)
    _ = _ := by simp [Nat.mul_comm]

/-- The coarse cores touched by a finite selected family of actual source input times. -/
@[expose] noncomputable def sourceExitCores {d : ℕ} (D : SumintDatum d) (s : Finset D.S.TVar) :
    Finset (FactorIdx D.S) := s.image (fun v => sourceCoreGroup D (timeFactorCoordinate D.S v).1)

/-- Fixing at most two actual source input times affects at most eight input vectors. -/
theorem sum_arity_sourceExitCores_le_eight {d : ℕ} (D : SumintDatum d) (s : Finset D.S.TVar)
    (hs : s.card ≤ 2) : ∑ b ∈ sourceExitCores D s, sourceCoreArity D b ≤ 8 := by
  have hc : (sourceExitCores D s).card ≤ s.card := Finset.card_image_le
  exact (sum_sourceCoreArity_le D _).trans (by omega)

end WaveTurbulence.SumintPar
