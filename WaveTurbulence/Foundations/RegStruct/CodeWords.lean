/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CodeOrders

/-! # Prefix encoding of regular structure data (DH21 Corollary 4.9)

This is an auxiliary encoding of the already drafted codes, not a replacement
for decoding into source gardens. Eleven symbols distinguish all constructors.
-/

@[expose] public section

namespace WaveTurbulence.Reg

/-- Token for one of the two type-1 mini-couples. -/
def cplToken (c : MiniCplCode) : Fin 11 := ⟨1 + c.val, by have := c.isLt; omega⟩

/-- Token for one of the six mini-trees. -/
def chainToken (m : MiniTreeCode) : Fin 11 :=
  ⟨5 + 2 * m.c.val + m.b.val, by have := m.c.isLt; have := m.b.isLt; omega⟩

theorem cplToken_injective : Function.Injective cplToken := by
  intro c d h
  apply Fin.ext
  have hh := congrArg Fin.val h
  change 1 + c.val = 1 + d.val at hh
  omega

theorem chainToken_injective : Function.Injective chainToken := by
  rintro ⟨c,b⟩ ⟨d,e⟩ h
  have hh := congrArg Fin.val h
  change 5 + 2 * c.val + b.val = 5 + 2 * d.val + e.val at hh
  have hb := b.isLt
  have he := e.isLt
  have hcd : c = d := Fin.ext (by omega)
  have hbe : b = e := Fin.ext (by omega)
  subst d
  subst e
  rfl

mutual
/-- Prefix word of a couple code. -/
def coupleWord : RegCpl → List (Fin 11)
  | .triv => [0]
  | .type1 c a b d => cplToken c :: (coupleWord a ++ coupleWord b ++ coupleWord d)
  | .type2 a b q => 3 :: (chainWord a ++ chainWord b ++ coupleWord q)

/-- Prefix word of a chain code. -/
def chainWord : RegChain → List (Fin 11)
  | .nil => [4]
  | .pair m r g i s => chainToken m :: (coupleWord r ++ coupleWord g ++ chainWord i ++ chainWord s)
end

mutual
/-- Parsing a couple prefix determines both the code and the unconsumed suffix. -/
theorem coupleWord_prefix (Q R : RegCpl) (a b : List (Fin 11))
    (h : coupleWord Q ++ a = coupleWord R ++ b) : Q = R ∧ a = b := by
  cases Q with
  | triv =>
    cases R with
    | triv => exact ⟨rfl, List.cons.inj h |>.2⟩
    | type1 c r s t =>
      have hh := congrArg Fin.val (List.cons.inj h |>.1)
      change 0 = 1 + c.val at hh
      omega
    | type2 r s t => exact (by have hh := List.cons.inj h |>.1; contradiction)
  | type1 c q r s =>
    cases R with
    | triv =>
      have hh := congrArg Fin.val (List.cons.inj h |>.1)
      change 1 + c.val = 0 at hh
      omega
    | type1 d u v w =>
      have ht := List.cons.inj h
      have hcd := cplToken_injective ht.1
      have hh := ht.2
      simp only [List.append_eq, List.append_assoc] at hh
      obtain ⟨hqu,hh⟩ := coupleWord_prefix q u _ _ hh
      obtain ⟨hrv,hh⟩ := coupleWord_prefix r v _ _ hh
      obtain ⟨hsw,hab⟩ := coupleWord_prefix s w _ _ hh
      subst d; subst u; subst v; subst w
      exact ⟨rfl,hab⟩
    | type2 u v w =>
      have hh := congrArg Fin.val (List.cons.inj h |>.1)
      change 1 + c.val = 3 at hh
      have := c.isLt
      omega
  | type2 x y q =>
    cases R with
    | triv => exact (by have hh := List.cons.inj h |>.1; contradiction)
    | type1 c u v w =>
      have hh := congrArg Fin.val (List.cons.inj h |>.1)
      change 3 = 1 + c.val at hh
      have := c.isLt
      omega
    | type2 u v r =>
      have hh := List.cons.inj h |>.2
      simp only [List.append_eq, List.append_assoc] at hh
      obtain ⟨hxu,hh⟩ := chainWord_prefix x u _ _ hh
      obtain ⟨hyv,hh⟩ := chainWord_prefix y v _ _ hh
      obtain ⟨hqr,hab⟩ := coupleWord_prefix q r _ _ hh
      subst u; subst v; subst r
      exact ⟨rfl,hab⟩
termination_by structural Q

/-- Parsing a chain prefix determines both the code and the unconsumed suffix. -/
theorem chainWord_prefix (X Y : RegChain) (a b : List (Fin 11))
    (h : chainWord X ++ a = chainWord Y ++ b) : X = Y ∧ a = b := by
  cases X with
  | nil =>
    cases Y with
    | nil => exact ⟨rfl, List.cons.inj h |>.2⟩
    | pair m r g i s =>
      have hh := congrArg Fin.val (List.cons.inj h |>.1)
      change 4 = 5 + 2 * m.c.val + m.b.val at hh
      omega
  | pair m r g i s =>
    cases Y with
    | nil =>
      have hh := congrArg Fin.val (List.cons.inj h |>.1)
      change 5 + 2 * m.c.val + m.b.val = 4 at hh
      omega
    | pair p r' g' i' s' =>
      have ht := List.cons.inj h
      have hmp := chainToken_injective ht.1
      have hh := ht.2
      simp only [List.append_eq, List.append_assoc] at hh
      obtain ⟨hrr,hh⟩ := coupleWord_prefix r r' _ _ hh
      obtain ⟨hgg,hh⟩ := coupleWord_prefix g g' _ _ hh
      obtain ⟨hii,hh⟩ := chainWord_prefix i i' _ _ hh
      obtain ⟨hss,hab⟩ := chainWord_prefix s s' _ _ hh
      subst p; subst r'; subst g'; subst i'; subst s'
      exact ⟨rfl,hab⟩
termination_by structural X
end

/-- The auxiliary prefix encoding loses no couple-code information. -/
theorem coupleWord_injective : Function.Injective coupleWord := by
  intro Q R h
  exact (coupleWord_prefix Q R [] [] (by simpa only [List.append_nil] using h)).1

/-- The auxiliary prefix encoding loses no chain-code information. -/
theorem chainWord_injective : Function.Injective chainWord := by
  intro X Y h
  exact (chainWord_prefix X Y [] [] (by simpa only [List.append_nil] using h)).1

end WaveTurbulence.Reg
