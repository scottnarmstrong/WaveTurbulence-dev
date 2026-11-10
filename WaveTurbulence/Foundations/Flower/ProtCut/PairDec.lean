/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.PairDom

/-! # D2c PROT-CUT: decorations of a closing pair

A decoration of a closing pair with root value `0` is the same as
* an exceptional triple `e = (x, yr, yg)` (the values at the interior root, at the red and at the green couple)
  satisfying the node relations at `𝔫_a` and `𝔫_b` (`PairE`: the lone child of `𝔫_b` carries `0`), and
* decorations with root values `0` of the three pieces (the piece values shifted by `x`, `yr`, `yg`).

`PairData.decEquiv` is this bijection (`GenDecoration` level). Translation invariance of the code decorations
(`chainDec_add_const`, `cplDec_add_const`) and the region-wise glue `pairGlue` are the tools. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

section Translation

variable {V : Type*} [AddCommGroup V] {w : ℕ}

theorem nodeRel_add_const (f : Fin w × Path → V) (k : V) (x : Fin w × Path) :
    NodeRel (fun z => f z + k) x ↔ NodeRel f x := by
  unfold NodeRel
  simp only
  constructor
  · intro h
    have : f x + k = (f (addrExt x [0]) - f (addrExt x [1]) + f (addrExt x [2])) + k := by
      rw [h]; abel
    exact add_right_cancel this
  · intro h; rw [h]; abel

mutual
theorem cplDec_add_const (f : Fin w × Path → V) (k : V) :
    (Q : RegCpl) → (a b : Fin w × Path) → (CplDec (fun z => f z + k) Q a b ↔ CplDec f Q a b)
  | .triv, a, b => by simp only [CplDec, add_left_inj]
  | .type1 c Q₁ Q₂ Q₃, a, b => by
    simp only [CplDec, nodeRel_add_const, cplDec_add_const f k Q₁, cplDec_add_const f k Q₂,
      cplDec_add_const f k Q₃]
  | .type2 Xp Xm Qlp, a, b => by
    simp only [CplDec, chainDec_add_const f k Xp, chainDec_add_const f k Xm, cplDec_add_const f k Qlp]
termination_by structural Q => Q

theorem chainDec_add_const (f : Fin w × Path → V) (k : V) :
    (X : RegChain) → (ζ : ℤˣ) → (a : Fin w × Path) → (ChainDec (fun z => f z + k) X ζ a ↔ ChainDec f X ζ a)
  | .nil, _, _ => Iff.rfl
  | .pair m Qr Qg inner rest, ζ, a => by
    simp only [ChainDec, nodeRel_add_const, cplDec_add_const f k Qr, cplDec_add_const f k Qg,
      chainDec_add_const f k inner, chainDec_add_const f k rest]
termination_by structural X => X
end

end Translation

/-! ### The exceptional data -/

variable (m : MiniTreeCode)

/-- The values at the children of `𝔫_a`. -/
def pairA {V : Type*} [AddCommGroup V] (x yr yg : V) (i : Fin 3) : V :=
  if i = m.c then x else if i = m.red.1 then yr else yg

/-- The values at the children of `𝔫_b` (the lone child carries `0`). -/
def pairB {V : Type*} [AddCommGroup V] (yr yg : V) (k : Fin 3) : V :=
  if k = m.lone then 0 else if k = m.red.2 then yr else yg

/-- The node relations at `𝔫_a` (value `0`) and `𝔫_b` (value `x`). -/
def PairRel {V : Type*} [AddCommGroup V] (x yr yg : V) : Prop :=
  (0 : V) = pairA m x yr yg 0 - pairA m x yr yg 1 + pairA m x yr yg 2 ∧
    x = pairB m yr yg 0 - pairB m yr yg 1 + pairB m yr yg 2

/-- **The exceptional lattice data of a closing pair.** -/
def PairE (d : ℕ) : Type := {e : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) // PairRel m e.1 e.2.1 e.2.2}

/-! ### The region-wise glue -/

variable (inner : RegChain) (ζ : ℤˣ)

/-- The glued values of a closing pair, region by region. -/
def pairGlue {V : Type*} [AddCommGroup V] (x yr yg : V) (fi : Fin 1 × Path → V)
    (fr fg : Fin 2 × Path → V) (z : Fin 1 × Path) : V :=
  match regionOf m inner ζ z.2 with
  | .root => 0
  | .bnode => x
  | .lone => 0
  | .red j => fr (j, z.2.drop (rBase m inner ζ j).length) + yr
  | .green j => fg (j, z.2.drop (gBase m inner ζ j).length) + yg
  | .inner => fi (0, z.2.drop 1) + x
  | .other => 0

section Glue

variable {V : Type*} [AddCommGroup V] (x yr yg : V) (fi : Fin 1 × Path → V) (fr fg : Fin 2 × Path → V)

theorem pairGlue_nil : pairGlue m inner ζ x yr yg fi fr fg (0, []) = 0 := by
  simp [pairGlue, regionOf_nil]

theorem pairGlue_bPath : pairGlue m inner ζ x yr yg fi fr fg (0, bPath m inner) = x := by
  simp [pairGlue, regionOf_bPath]

theorem pairGlue_lonePos : pairGlue m inner ζ x yr yg fi fr fg (0, lonePos m inner) = 0 := by
  simp [pairGlue, regionOf_lonePos]

theorem pairGlue_rBase (j : Fin 2) (q : Path) :
    pairGlue m inner ζ x yr yg fi fr fg (0, rBase m inner ζ j ++ q) = fr (j, q) + yr := by
  simp [pairGlue, regionOf_rBase]

theorem pairGlue_gBase (j : Fin 2) (q : Path) :
    pairGlue m inner ζ x yr yg fi fr fg (0, gBase m inner ζ j ++ q) = fg (j, q) + yg := by
  simp [pairGlue, regionOf_gBase]

theorem pairGlue_inner (q : Path) (hq : ¬ inner.lonePath <+: q) :
    pairGlue m inner ζ x yr yg fi fr fg (0, m.c :: q) = fi (0, q) + x := by
  simp [pairGlue, regionOf_inner m inner ζ q hq]

end Glue

theorem exists_rBase_top : ∃ j, rBase m inner ζ j = [m.red.1] := by
  by_cases hs : slotSign ζ m.red.1 = 1
  · exact ⟨0, by simp [rBase, hs]⟩
  · exact ⟨1, by simp [rBase, hs]⟩

theorem exists_rBase_bot : ∃ j, rBase m inner ζ j = bPath m inner ++ [m.red.2] := by
  by_cases hs : slotSign ζ m.red.1 = 1
  · exact ⟨1, by simp [rBase, hs]⟩
  · exact ⟨0, by simp [rBase, hs]⟩

theorem exists_gBase_top : ∃ j, gBase m inner ζ j = [m.green.1] := by
  by_cases hs : slotSign ζ m.green.1 = 1
  · exact ⟨0, by simp [gBase, hs]⟩
  · exact ⟨1, by simp [gBase, hs]⟩

theorem exists_gBase_bot : ∃ j, gBase m inner ζ j = bPath m inner ++ [m.green.2] := by
  by_cases hs : slotSign ζ m.green.1 = 1
  · exact ⟨1, by simp [gBase, hs]⟩
  · exact ⟨0, by simp [gBase, hs]⟩

/-- The oriented red couple of a chain decoration is the couple at `rBase`. -/
theorem oriented_rBase {V : Type*} [AddCommGroup V] (f : Fin 1 × Path → V) (Q : RegCpl) :
    (if slotSign ζ m.red.1 = 1 then
        CplDec f Q (addrExt ((0 : Fin 1), ([] : Path)) [m.red.1])
          (addrExt ((0 : Fin 1), ([] : Path)) ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else CplDec f Q (addrExt ((0 : Fin 1), ([] : Path)) ([m.c] ++ inner.lonePath ++ [m.red.2]))
          (addrExt ((0 : Fin 1), ([] : Path)) [m.red.1])) ↔
      CplDec f Q (0, rBase m inner ζ 0) (0, rBase m inner ζ 1) := by
  by_cases hs : slotSign ζ m.red.1 = 1 <;> simp [rBase, hs, addrExt, bPath]

theorem oriented_gBase {V : Type*} [AddCommGroup V] (f : Fin 1 × Path → V) (Q : RegCpl) :
    (if slotSign ζ m.green.1 = 1 then
        CplDec f Q (addrExt ((0 : Fin 1), ([] : Path)) [m.green.1])
          (addrExt ((0 : Fin 1), ([] : Path)) ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else CplDec f Q (addrExt ((0 : Fin 1), ([] : Path)) ([m.c] ++ inner.lonePath ++ [m.green.2]))
          (addrExt ((0 : Fin 1), ([] : Path)) [m.green.1])) ↔
      CplDec f Q (0, gBase m inner ζ 0) (0, gBase m inner ζ 1) := by
  by_cases hs : slotSign ζ m.green.1 = 1 <;> simp [gBase, hs, addrExt, bPath]

end WaveTurbulence.Flower.ProtCut
