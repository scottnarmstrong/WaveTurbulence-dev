/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.RegularHeldOut

/-!
# The conjugate of a regular couple code (CONJ-COH)

`conjCpl Q` is the code of the conjugate couple: the two trees are exchanged, so the roles of `𝒯⁺, 𝒯⁻`
swap (TARGET deftree/defgarden: conjugation reverses all signs).  Type 1 codes keep their mini-couple code `c` and
exchange the roles of `Q₁, Q₃` when `c = 1`; type 2 codes exchange `𝒳⁺, 𝒳⁻`; chains keep their structure (only the
root sign flips, which is a parameter of `plug`, `pairsAt`, `linksAt`).

* `trees_conjCpl`, `plug_conjChain`, `lonePath_conjChain`, `size_conjCpl`, `wf_conjCpl`: the code-level facts.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.ConjCoh

open WaveTurbulence TTree

mutual
/-- The code of the conjugate couple. -/
def conjCpl : RegCpl → RegCpl
  | .triv => .triv
  | .type1 c Q₁ Q₂ Q₃ =>
    if c = 0 then .type1 c (conjCpl Q₁) (conjCpl Q₂) (conjCpl Q₃)
    else .type1 c (conjCpl Q₃) (conjCpl Q₂) (conjCpl Q₁)
  | .type2 Xp Xm Qlp => .type2 (conjChain Xm) (conjChain Xp) (conjCpl Qlp)

/-- The code of the conjugate chain (the sign is a parameter, so only the couples change). -/
def conjChain : RegChain → RegChain
  | .nil => .nil
  | .pair m Qr Qg inner rest => .pair m (conjCpl Qr) (conjCpl Qg) (conjChain inner) (conjChain rest)
end

theorem slotSign_neg (ζ : ℤˣ) (i : Fin 3) : slotSign (-ζ) i = -slotSign ζ i := by
  unfold slotSign; split_ifs <;> simp

theorem treeOfSign_neg (T : TTree × TTree) (s : ℤˣ) :
    treeOfSign (T.2, T.1) (-s) = treeOfSign T s := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp [treeOfSign]

mutual
theorem size_conjCpl : ∀ Q : RegCpl, (conjCpl Q).size = Q.size
  | .triv => rfl
  | .type1 c Q₁ Q₂ Q₃ => by
    have h1 := size_conjCpl Q₁
    have h2 := size_conjCpl Q₂
    have h3 := size_conjCpl Q₃
    by_cases hc : c = 0
    · simp only [conjCpl, hc, ite_true, RegCpl.size, h1, h2, h3]
    · simp only [conjCpl, hc, ite_false, RegCpl.size, h1, h2, h3]; omega
  | .type2 Xp Xm Qlp => by
    have h1 := size_conjChain Xp
    have h2 := size_conjChain Xm
    have h3 := size_conjCpl Qlp
    simp only [conjCpl, RegCpl.size, h1, h2, h3]; omega
termination_by structural Q => Q

theorem size_conjChain : ∀ X : RegChain, (conjChain X).size = X.size
  | .nil => rfl
  | .pair m Qr Qg inner rest => by
    simp only [conjChain, RegChain.size, size_conjCpl Qr, size_conjCpl Qg,
      size_conjChain inner, size_conjChain rest]
termination_by structural X => X
end

theorem lonePath_conjChain : ∀ X : RegChain, (conjChain X).lonePath = X.lonePath
  | .nil => rfl
  | .pair m Qr Qg inner rest => by
    simp only [conjChain, RegChain.lonePath, lonePath_conjChain inner, lonePath_conjChain rest]

mutual
theorem trees_conjCpl : ∀ Q : RegCpl, (conjCpl Q).trees = (Q.trees.2, Q.trees.1)
  | .triv => rfl
  | .type1 c Q₁ Q₂ Q₃ => by
    have h1 := trees_conjCpl Q₁
    have h2 := trees_conjCpl Q₂
    have h3 := trees_conjCpl Q₃
    by_cases hc : c = 0
    · simp only [conjCpl, hc, ite_true, RegCpl.trees, h1, h2, h3]
    · simp only [conjCpl, hc, ite_false, RegCpl.trees, h1, h2, h3]
  | .type2 Xp Xm Qlp => by
    have h3 := trees_conjCpl Qlp
    have h1 : ∀ h, (conjChain Xm).plug 1 h = Xm.plug (-1) h := fun h => by
      simpa using plug_conjChain Xm (-1) h
    have h2 : ∀ h, (conjChain Xp).plug (-1) h = Xp.plug 1 h := fun h => plug_conjChain Xp 1 h
    simp only [conjCpl, RegCpl.trees, h3, h1, h2]
termination_by structural Q => Q

theorem plug_conjChain : ∀ (X : RegChain) (ζ : ℤˣ) (h : TTree),
    (conjChain X).plug (-ζ) h = X.plug ζ h
  | .nil, _, _ => rfl
  | .pair m Qr Qg inner rest, ζ, h => by
    have hI : ∀ ζ' h', (conjChain inner).plug (-ζ') h' = inner.plug ζ' h' :=
      fun ζ' h' => plug_conjChain inner ζ' h'
    have hR : ∀ ζ' h', (conjChain rest).plug (-ζ') h' = rest.plug ζ' h' :=
      fun ζ' h' => plug_conjChain rest ζ' h'
    have hr := trees_conjCpl Qr
    have hg := trees_conjCpl Qg
    simp only [conjChain, RegChain.plug, slotSign_neg, hr, hg, treeOfSign_neg, hI, hR]
termination_by structural X => X
end

theorem isType2_conjCpl : ∀ Q : RegCpl, (conjCpl Q).isType2 = Q.isType2
  | .triv => rfl
  | .type1 c Q₁ Q₂ Q₃ => by
    by_cases hc : c = 0 <;> simp [conjCpl, hc, RegCpl.isType2]
  | .type2 Xp Xm Qlp => rfl

theorem isNil_conjChain : ∀ X : RegChain, (conjChain X).isNil = X.isNil
  | .nil => rfl
  | .pair .. => rfl

mutual
theorem wf_conjCpl : ∀ Q : RegCpl, (conjCpl Q).wf = Q.wf
  | .triv => rfl
  | .type1 c Q₁ Q₂ Q₃ => by
    have h1 := wf_conjCpl Q₁
    have h2 := wf_conjCpl Q₂
    have h3 := wf_conjCpl Q₃
    by_cases hc : c = 0
    · simp only [conjCpl, hc, ite_true, RegCpl.wf, h1, h2, h3]
    · simp only [conjCpl, hc, ite_false, RegCpl.wf, h1, h2, h3]
      rw [Bool.and_comm (Q₃.wf && Q₂.wf) , Bool.and_comm (Q₃.wf) , Bool.and_assoc]
  | .type2 Xp Xm Qlp => by
    have h1 := wf_conjChain Xp
    have h2 := wf_conjChain Xm
    have h3 := wf_conjCpl Qlp
    simp only [conjCpl, RegCpl.wf, h1, h2, h3, isType2_conjCpl, isNil_conjChain]
    cases Xp.wf <;> cases Xm.wf <;> cases Qlp.wf <;> cases Qlp.isType2 <;> cases Xp.isNil <;>
      cases Xm.isNil <;> rfl
termination_by structural Q => Q

theorem wf_conjChain : ∀ X : RegChain, (conjChain X).wf = X.wf
  | .nil => rfl
  | .pair m Qr Qg inner rest => by
    simp only [conjChain, RegChain.wf, wf_conjCpl Qr, wf_conjCpl Qg, wf_conjChain inner, wf_conjChain rest]
termination_by structural X => X
end

end WaveTurbulence.ConjCoh
