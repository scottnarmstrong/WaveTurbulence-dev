/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.GardenB
public import WaveTurbulence.Foundations.WaveB.RegularHeldOut
public import WaveTurbulence.Foundations.ClassJR.MCProp51

/-!
# B2 codes and the ClassJR copies

`ClassJR.RegCpl` (where DH21 Prop 5.1 is proved, `ClassJR.RegCpl.maincoef`) is a verbatim copy of the
B2 code type `WaveTurbulence.RegCpl` (the copy in REG-STRUCT's `WaveB2Draft/RegularDefs.lean`, sha256
`92546fc4…`). `toJR` is the identity translation; when B2 lands, the copies are deleted and `toJR`
becomes `id`.

Also: the node signs `ζ_𝔫` along addresses, the sign tables of the mini-trees (the red and green
pairs have opposite signs; the lone leaf keeps the root's sign), and the phases `β = ζα` of a tree
rooted at an address.
-/

@[expose] public section

namespace WaveTurbulence.MainCoef

open TTree

/-- The mini-tree code in ClassJR. -/
def toJRm (m : MiniTreeCode) : ClassJR.MiniTreeCode := ⟨m.c, m.b⟩

mutual
/-- **The ClassJR copy of a B2 couple code.** -/
def toJR : RegCpl → ClassJR.RegCpl
  | .triv => .triv
  | .type1 c Q₁ Q₂ Q₃ => .type1 c (toJR Q₁) (toJR Q₂) (toJR Q₃)
  | .type2 Xp Xm Qlp => .type2 (toJRc Xp) (toJRc Xm) (toJR Qlp)

/-- The ClassJR copy of a B2 chain code. -/
def toJRc : RegChain → ClassJR.RegChain
  | .nil => .nil
  | .pair m Qr Qg inner rest => .pair (toJRm m) (toJR Qr) (toJR Qg) (toJRc inner) (toJRc rest)
end

theorem lonePath_toJRc : ∀ X : RegChain, (toJRc X).lonePath = X.lonePath
  | .nil => rfl
  | .pair m Qr Qg inner rest => by
    simp only [toJRc, ClassJR.RegChain.lonePath, RegChain.lonePath, lonePath_toJRc inner,
      lonePath_toJRc rest]
    rfl

theorem slotSign_eq (ζ : ℤˣ) (i : Fin 3) : ClassJR.slotSign ζ i = slotSign ζ i := rfl

theorem slotSign_val (ζ : ℤˣ) (i : Fin 3) :
    ((slotSign ζ i : ℤˣ) : ℤ) = if i = 1 then -(ζ : ℤ) else ζ := by
  unfold slotSign; split_ifs <;> simp

/-! ### Node signs -/

theorem nodeSgn_addrExt (x : ClassJR.Addr) (p : TTree.Path) :
    ClassJR.nodeSgn (ClassJR.addrExt x p) = ClassJR.nodeSgn x * (-1) ^ (p.count 1) := by
  simp only [ClassJR.nodeSgn, ClassJR.addrExt, List.count_append, pow_add, ← mul_assoc]
  rfl

/-- The node sign of a slot, for a node of sign `ζ`. -/
theorem nodeSgn_slot {x : ClassJR.Addr} {ζ : ℤˣ} (hx : ClassJR.nodeSgn x = ζ) (i : Fin 3) :
    ClassJR.nodeSgn (ClassJR.addrExt x [i]) = ((slotSign ζ i : ℤˣ) : ℤ) := by
  rw [slotSign_val, nodeSgn_addrExt, hx]
  fin_cases i <;> simp

theorem MiniTreeCode.lone_sign (m : MiniTreeCode) (ζ : ℤˣ) :
    slotSign (slotSign ζ m.c) m.lone = ζ := by
  rcases m with ⟨c, b⟩
  rcases Int.units_eq_one_or ζ with rfl | rfl <;>
    fin_cases c <;> fin_cases b <;> decide

theorem MiniTreeCode.red_sign (m : MiniTreeCode) (ζ : ℤˣ) :
    slotSign (slotSign ζ m.c) m.red.2 = -slotSign ζ m.red.1 := by
  rcases m with ⟨c, b⟩
  rcases Int.units_eq_one_or ζ with rfl | rfl <;>
    fin_cases c <;> fin_cases b <;> decide

theorem MiniTreeCode.green_sign (m : MiniTreeCode) (ζ : ℤˣ) :
    slotSign (slotSign ζ m.c) m.green.2 = -slotSign ζ m.green.1 := by
  rcases m with ⟨c, b⟩
  rcases Int.units_eq_one_or ζ with rfl | rfl <;>
    fin_cases c <;> fin_cases b <;> decide

/-- **The lone leaf of a chain has the sign of its root.** -/
theorem nodeSgn_lonePath : ∀ (X : RegChain) {x : ClassJR.Addr} {ζ : ℤˣ},
    ClassJR.nodeSgn x = ζ → ClassJR.nodeSgn (ClassJR.addrExt x X.lonePath) = ζ
  | .nil, x, ζ, hx => by simpa [RegChain.lonePath, ClassJR.addrExt] using hx
  | .pair m Qr Qg inner rest, x, ζ, hx => by
    have h1 := nodeSgn_slot hx m.c
    have h2 := nodeSgn_lonePath inner h1
    have h3 := nodeSgn_slot h2 m.lone
    rw [MiniTreeCode.lone_sign] at h3
    have h4 := nodeSgn_lonePath rest h3
    have e : ClassJR.addrExt x (RegChain.pair m Qr Qg inner rest).lonePath =
        ClassJR.addrExt (ClassJR.addrExt (ClassJR.addrExt (ClassJR.addrExt x [m.c]) inner.lonePath)
          [m.lone]) rest.lonePath := by
      simp [ClassJR.addrExt, RegChain.lonePath, List.append_assoc]
    rw [e]
    exact h4

/-! ### Phases -/

/-- The phases `β_p = ζ_{x⬝p} α_{x⬝p}` of the tree rooted at the address `x`. -/
def betaAt (α : ClassJR.Addr → ℝ) (x : ClassJR.Addr) (p : TTree.Path) : ℝ :=
  ClassJR.nodeSgn (ClassJR.addrExt x p) * α (ClassJR.addrExt x p)

theorem betaAt_cons (α : ClassJR.Addr → ℝ) (x : ClassJR.Addr) (i : Fin 3) :
    (fun p => betaAt α x (i :: p)) = betaAt α (ClassJR.addrExt x [i]) := by
  funext p
  simp [betaAt, ClassJR.addrExt]

theorem betaAt_nil (α : ClassJR.Addr → ℝ) (x : ClassJR.Addr) :
    betaAt α x [] = ClassJR.nodeSgn x * α x := by
  simp [betaAt, ClassJR.addrExt]

/-- The link relation `ζ_{𝔫'}α_{𝔫'} = -ζ_𝔫α_𝔫` (DH21/DH23 (deftildeb)). -/
def LinkRel (α : ClassJR.Addr → ℝ) (l : ClassJR.Addr × ClassJR.Addr) : Prop :=
  ClassJR.nodeSgn l.2 * α l.2 = -(ClassJR.nodeSgn l.1 * α l.1)

end WaveTurbulence.MainCoef
