/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.WaveB.FrozenB2
/-! FLOWER-REG (R12): the regular-couple leg of B1.12 clause (2) with kind `L0` and `dt = false`.

`CoupleDataD`, `CoupleDataD.carries` and `regularCoupleSum` are byte-identical copies of the FLOWER-SPINE
definitions of `FS7/Gates.lean` (sha256 ea7b5775...f75; `RegularCouplesAt` is L176-L183 there), placed in
`WaveTurbulence.FlowerReg` so that they live in the snapshot-9 universe. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerReg
open WaveTurbulence MeasureTheory Finset Set
open scoped Classical ENNReal

/-- The data of one restricted couple sum `coupleSum` (depends on `d` only). (Copy of
`FlowerSpine.CoupleDataD`.) -/
structure CoupleDataD (d : ℕ) where
  kind : TreeKind
  dt : Bool
  t : ℝ
  k : Mom d

/-- The index condition of `coupleSum`, verbatim. (Copy of `FlowerSpine.CoupleDataD.carries`.) -/
def CoupleDataD.carries (P : WTParams) (D : CoupleDataD P.d) (p N : ℕ)
    (LG : LayeredGarden 2) : Prop :=
  IsCanonC (p + 1) LG ∧
      (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
      LG.TreeKindOK p (P.N (p + 1)) D.kind ∧
      (D.dt = true → ∀ j : Fin 2, ∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ LG.layer b.toNode = p)

/-- The regular canonical couples of `coupleSum` (TARGET L2312: "using (taylorbound) and (estcouple2)").
(Copy of `FlowerSpine.regularCoupleSum`.) -/
noncomputable def regularCoupleSum (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (kind : TreeKind)
    (dt : Bool) (t : ℝ) (k : Mom P.d) : ℂ :=
  ∑ᶠ (LG : LayeredGarden 2) (_ : (CoupleDataD.mk kind dt t k).carries P p N LG ∧
      IsRegularCouple LG.garden),
    kernelKgen P.L P.γ P.δ F LG (fun b => if dt = true ∧ b.1.2 = [] then some t else none) ∅
      (fun _ => 1) (fun _ => t) k (fun _ => 0) 0

/-- **`RegularCouplesL0At`**: the regular-couple leg of B1.12 clause (2), kind `ℒ₀`, no `∂_t`
(`dt = false`). It is `FlowerSpine.RegularCouplesAt` (FS7/Gates.lean L176-L183) restricted to
`kind = L0` and `dt = false`; the exponents are the pinned ones, `δ^{2νN}` and `L^{50d}`, which are sharper than
B1.12 (2)'s `δ^{νN}`, `L^{100d}` and are proved here.

Source: TARGET L2312, "using (taylorbound) and (estcouple2), we get the same bound (trterm1) ... with extra
factor `e^{−100N_{p+1}}`" (the regular-couple part of the sum for `ℒ₀`). -/
def RegularCouplesL0At (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ k : Mom P.d, ∀ N ≤ P.N (p + 1) ^ 4,
    ‖regularCoupleSum P (inputsF P R) p N .L0 false t k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (50 * P.d : ℝ) * P.δ ^ (2 * P.ν * N)

end WaveTurbulence.FlowerReg
