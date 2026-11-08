/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKStep.Run1
public import WaveTurbulence.Foundations.FinalCount.LowChain4

/-! # C1b1 MK-PHASE1 (1): the reach API of the survivor Step 1 (`HStep1RLE`, `Reach1LE`), `Inv1LE`

Count.lean (R164) states the survivor Step 1 `HStep1RLE` over `CollDataMK` with the ancestor-matched survivor cut
`SurvCut` (`(E i).atoms = K.C.atoms.image h.anc`, C1b1's finding F-C1b1-1). Every step is a step of C1a's LOW run
`HStep1LE` (`HStep1RLE.toLE`), so the run bookkeeping and the invariant `InvL` hold along the reach (`reach1LE_aux`,
`invL_reach1E`, from C1a's `HStep1LE.aux` and `HRunLE.inv1`). `Inv1LE` is main's `Inv1L` with `Reach1LE`. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section mol
variable {M₀ : Molecule V D₀} {m : ℕ}

variable {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)}
  {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

/-- Every survivor Step-1 step is a step of the LOW run with re-cuts (C1a's `HStep1LE`). -/
theorem HStep1RLE.toLE {h h' : HSt V D₀} (hs : HStep1RLE C Un Fst E L γ η w κ h h') :
    HStep1LE C.toCollData L γ η w κ h h' := by
  cases hs with
  | vine K R kp hs _ _ _ _ _ _ => exact HStep1LE.base (HStep1L.old hs)
  | d1 K hs _ _ _ _ _ _ => exact HStep1LE.base (HStep1L.low hs)
  | triple _ hs _ _ _ _ => exact HStep1LE.base (HStep1L.old hs)
  | survVine K R kp i hs _ _ => exact HStep1LE.base (HStep1L.old hs)
  | survD1 K i hs _ _ => exact HStep1LE.base (HStep1L.low hs)
  | survRC K i hs _ _ => exact HStep1LE.recut hs

theorem Reach1LE.toLE {h : HSt V D₀} (hr : Reach1LE C Un Fst E L γ η w κ h) :
    Relation.ReflTransGen (HStep1LE C.toCollData L γ η w κ) (HSt.init M₀) h :=
  Relation.ReflTransGen.mono (fun _ _ hs => HStep1RLE.toLE hs) _ _ hr

theorem Reach1LE.ext {h h' : HSt V D₀} (hr : Reach1LE C Un Fst E L γ η w κ h)
    (hs : HStep1RLE C Un Fst E L γ η w κ h h') : Reach1LE C Un Fst E L γ η w κ h' :=
  Relation.ReflTransGen.tail hr hs

/-- **The invariant along the survivor Step 1** (main's `invL_reach1`, LowChain4, through C1a's `HRunLE.inv1`). -/
theorem invL_reach1E {Rn : ℕ} (hS : SubHypL Rn M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) {h : HSt V D₀}
    (hr : Reach1LE C Un Fst E L γ η w κ h) : ∃ R', R' ≤ Rn ∧ InvL M₀ R' L γ η w κ h :=
  HRunLE.inv1 (Reach1LE.toLE hr) (InvL.init hS h0)

/-- The run bookkeeping (`DPInv`, the ancestor relation, `DesRecN`) along the survivor Step 1. -/
theorem reach1LE_aux {h : HSt V D₀} (hr : Reach1LE C Un Fst E L γ η w κ h) : RunAux M₀ C.toCollData h :=
  rtgH (P := fun h => RunAux M₀ C.toCollData h) (fun _ _ hs hp => HStep1LE.aux hs hp) (Reach1LE.toLE hr) (RunAux.init C.toCollData)

/-- The ancestor relation along the survivor Step 1. -/
theorem reach1LE_ancRel {h : HSt V D₀} (hr : Reach1LE C Un Fst E L γ η w κ h) : AncRel M₀ h.s h.anc :=
  (reach1LE_aux hr).2.1

end mol

/-- **The class invariant of the survivor Step 1** (main's `Inv1L` with `Reach1LE`). -/
abbrev Inv1LE {m : ℕ} (M₀ : Molecule V D₀) (Rn : ℕ) (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀))
    (Fst : Set (Object M₀)) (E : Fin m → Object M₀) (L γ η : ℝ) (w : Mom d) (A0 A : Set (D₀ → (Fin d → ℤ)))
    (h : HSt V D₀) : Prop :=
  Inv3L M₀ Rn (fun κ h => Reach1LE C Un Fst E L γ η w κ h) L w A0 A h

theorem Inv1LE.mono {m : ℕ} {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollDataMK M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d}
    {A0 A B : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} (hA : Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h) (hB : B ⊆ A) :
    Inv1LE M₀ Rn C Un Fst E L γ η w A0 B h :=
  Inv3L.mono hA hB

end WaveTurbulence.Flower.FinalMKPhase1
