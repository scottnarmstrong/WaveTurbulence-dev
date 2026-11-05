/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.EnhancedDraft.NetSign

/-!
# Enhanced dominant couple codes, address-free (DH21 §7.4; TARGET Def `defencpl`)

An enhanced dominant couple `(𝒬, Z)` (DH21 L1795, Def 4.18; TARGET Def `defencpl`, L1127) is a dominant
couple with a special subset `Z ⊆ 𝒩^ch`. The B2 draft stores `Z` as a set of node addresses. For the sums of
DH21 Props 7.7–7.10 it is convenient to record `Z` instead by one bit `𝙸 = [𝔫_{2j-1} ∈ Z]` at each chain pair,
the only places where a special node can sit (ENHANCED `mem_specialSets_iff`, DH21 (unionz)).

* `ECpl` / `EChain`: dominant couple and chain codes with these bits (chains with `inner = nil`, the
  dominant form, ENHANCED `partition_dominant_iff`).
* `ECpl.code`, `ECpl.hsize` (`n(𝒬)/2`), `ECpl.wf`, `ECpl.shape` (the ENHANCED class data), `ECpl.sw`
  (`∏_{𝔫∈Z}(−ζ_𝔫 π i)^{-1}`, F61), `ECpl.bits`.
* `enh Z Q a b`: the enhanced code of `(𝒬, Z)` placed at `(a, b)`, read off `Z` exactly as ENHANCED's
  `cplShape` reads it. `shape_enh`, `code_enh`, `bits_enh`, `sw_enh` identify the data.
* `ECpl.ext_code_bits`: an enhanced code is determined by its code and its bits.
-/

@[expose] public section

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links

mutual
/-- **Enhanced dominant couple codes** (address-free): the B2 codes of dominant couples with one bit
`𝙸 ∈ {0, 1}` at every chain pair (`𝙸 = 1` iff the chosen node `𝔫_{2j-1}` lies in `Z`). -/
inductive ECpl : Type
  | triv : ECpl
  | type1 (c : MiniCplCode) (Q₁ Q₂ Q₃ : ECpl) : ECpl
  | type2 (Xp Xm : EChain) (Qlp : ECpl) : ECpl

/-- Enhanced dominant chains: pairs `{2j-1, 2j}` from the root, each with its mini-tree code, its bit and
its red and green couples. -/
inductive EChain : Type
  | nil : EChain
  | pair (m : MiniTreeCode) (I : Bool) (Qr Qg : ECpl) (rest : EChain) : EChain
end

mutual
/-- The underlying B2 couple code (forget the bits). -/
def ECpl.code : ECpl → RegCpl
  | .triv => .triv
  | .type1 c Q₁ Q₂ Q₃ => .type1 c Q₁.code Q₂.code Q₃.code
  | .type2 Xp Xm Qlp => .type2 Xp.code Xm.code Qlp.code

/-- The underlying B2 chain code (`inner = nil` at every pair). -/
def EChain.code : EChain → RegChain
  | .nil => .nil
  | .pair m _ Qr Qg rest => .pair m Qr.code Qg.code .nil rest.code
end

mutual
/-- Half the order, `n(𝒬)/2`. -/
def ECpl.hsize : ECpl → ℕ
  | .triv => 0
  | .type1 _ Q₁ Q₂ Q₃ => Q₁.hsize + Q₂.hsize + Q₃.hsize + 1
  | .type2 Xp Xm Qlp => Xp.hsize + Xm.hsize + Qlp.hsize

/-- Half the number of branching nodes of a chain with its couples. -/
def EChain.hsize : EChain → ℕ
  | .nil => 0
  | .pair _ _ Qr Qg rest => Qr.hsize + Qg.hsize + rest.hsize + 1
end

/-- Is the code of type 2? -/
def ECpl.isType2 : ECpl → Bool
  | .type2 .. => true
  | _ => false

/-- Is the chain empty? -/
def EChain.isNil : EChain → Bool
  | .nil => true
  | _ => false

mutual
/-- Well-formedness (B2 `RegCpl.wf`): `Q_lp` is trivial or of type 1 and the two chains are not both empty. -/
def ECpl.wf : ECpl → Bool
  | .triv => true
  | .type1 _ Q₁ Q₂ Q₃ => Q₁.wf && Q₂.wf && Q₃.wf
  | .type2 Xp Xm Qlp => Xp.wf && Xm.wf && Qlp.wf && !Qlp.isType2 && !(Xp.isNil && Xm.isNil)

/-- Well-formedness of a chain (its couples are well formed). -/
def EChain.wf : EChain → Bool
  | .nil => true
  | .pair _ _ Qr Qg rest => Qr.wf && Qg.wf && rest.wf
end

mutual
/-- **The class data** (ENHANCED `Shape`) of an enhanced code: type 2 lists the tuples `(𝙸, 𝚌 - 1, 𝒳₁, 𝒳₂)` of
the `+` chain, then of the `-` chain, and the tail. -/
def ECpl.shape : ECpl → Shape
  | .triv => .triv
  | .type1 _ Q₁ Q₂ Q₃ => .type1 Q₁.shape Q₂.shape Q₃.shape
  | .type2 Xp Xm Qlp => .type2 (Xp.tuples.append Xm.tuples) Qlp.shape

/-- The tuples of a chain. -/
def EChain.tuples : EChain → Tuples
  | .nil => .nil
  | .pair m I Qr Qg rest => .cons I m.c Qr.shape Qg.shape rest.tuples
end

/-- The weight of a chain pair of sign `ε` with bit `𝙸`: `(−ε π i)^{-1}` if `𝙸 = 1` (F61), else `1`. -/
noncomputable def wt (ε : ℤˣ) (I : Bool) : ℂ :=
  if I then (-((((ε : ℤˣ) : ℤ) : ℂ) * Real.pi * Complex.I))⁻¹ else 1

mutual
/-- **The special weight** `∏_{𝔫 ∈ Z} (−ζ_𝔫 π i)^{-1}` (B2 `specialWeight`): the chosen nodes of the `+`
chain have sign `+`, those of the `-` chain sign `-`. -/
noncomputable def ECpl.sw : ECpl → ℂ
  | .triv => 1
  | .type1 _ Q₁ Q₂ Q₃ => Q₁.sw * Q₂.sw * Q₃.sw
  | .type2 Xp Xm Qlp => Xp.sw 1 * Xm.sw (-1) * Qlp.sw

/-- The special weight of a chain whose chosen nodes have sign `ε`. -/
noncomputable def EChain.sw : EChain → ℤˣ → ℂ
  | .nil, _ => 1
  | .pair _ I Qr Qg rest, ε => wt ε I * Qr.sw * Qg.sw * rest.sw ε
end

mutual
/-- The bits, in the order of ENHANCED's special candidates `cplSpecial`. -/
def ECpl.bits : ECpl → List Bool
  | .triv => []
  | .type1 _ Q₁ Q₂ Q₃ => Q₁.bits ++ Q₂.bits ++ Q₃.bits
  | .type2 Xp Xm Qlp => Xp.bits ++ Xm.bits ++ Qlp.bits

/-- The bits of a chain. -/
def EChain.bits : EChain → List Bool
  | .nil => []
  | .pair _ I Qr Qg rest => I :: (Qr.bits ++ Qg.bits ++ rest.bits)
end

/-! ### The enhanced code of `(𝒬, Z)` -/

variable {w : ℕ}

mutual
/-- **The enhanced code of `(𝒬, Z)`** with `𝒬` placed at `(a, b)` (addresses as in `RegCpl.linksAt` and
ENHANCED `cplShape`): the bit of a chain pair is `[𝔫_{2j-1} ∈ Z]`. -/
def enh (Z : Finset (Fin w × Path)) : RegCpl → (Fin w × Path) → (Fin w × Path) → ECpl
  | .triv, _, _ => .triv
  | .type1 c Q₁ Q₂ Q₃, a, b =>
    .type1 c (enh Z Q₁ (addrExt a [0]) (addrExt b [c.partner 0]))
      (enh Z Q₂ (addrExt b [1]) (addrExt a [1]))
      (enh Z Q₃ (addrExt a [2]) (addrExt b [c.partner 2]))
  | .type2 Xp Xm Qlp, a, b =>
    .type2 (enhC Z Xp 1 a) (enhC Z Xm (-1) b)
      (enh Z Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath))

/-- The enhanced chain of a chain rooted at `a` with root sign `ζ`. -/
def enhC (Z : Finset (Fin w × Path)) : RegChain → ℤˣ → (Fin w × Path) → EChain
  | .nil, _, _ => .nil
  | .pair m Qr Qg inner rest, ζ, a =>
    .pair m (decide (a ∈ Z))
      (if slotSign ζ m.red.1 = 1 then
        enh Z Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else enh Z Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1]))
      (if slotSign ζ m.green.1 = 1 then
        enh Z Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else enh Z Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1]))
      (enhC Z rest (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])))
end

mutual
/-- **The class data of `(𝒬, Z)` is ENHANCED's shape.** -/
theorem shape_enh (Z : Finset (Fin w × Path)) : (Q : RegCpl) → (a b : Fin w × Path) →
    (enh Z Q a b).shape = cplShape Z Q a b
  | .triv, _, _ => rfl
  | .type1 c Q₁ Q₂ Q₃, a, b => by
    simp only [enh, ECpl.shape, cplShape, shape_enh Z Q₁, shape_enh Z Q₂, shape_enh Z Q₃]
  | .type2 Xp Xm Qlp, a, b => by
    simp only [enh, ECpl.shape, cplShape, tuples_enhC Z Xp, tuples_enhC Z Xm, shape_enh Z Qlp]

theorem tuples_enhC (Z : Finset (Fin w × Path)) : (X : RegChain) → (ζ : ℤˣ) → (a : Fin w × Path) →
    (enhC Z X ζ a).tuples = chainTuples Z X ζ a
  | .nil, _, _ => rfl
  | .pair m Qr Qg inner rest, ζ, a => by
    simp only [enhC, EChain.tuples, chainTuples, tuples_enhC Z rest]
    congr 1
    · split_ifs <;> exact shape_enh Z Qr _ _
    · split_ifs <;> exact shape_enh Z Qg _ _
end

mutual
/-- For a dominant code, forgetting the bits of `enh Z 𝒬` gives back `𝒬`. -/
theorem code_enh (Z : Finset (Fin w × Path)) : (Q : RegCpl) → Q.dominant = true →
    (a b : Fin w × Path) → (enh Z Q a b).code = Q
  | .triv, _, _, _ => rfl
  | .type1 c Q₁ Q₂ Q₃, h, a, b => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    simp only [enh, ECpl.code, code_enh Z Q₁ h.1.1, code_enh Z Q₂ h.1.2, code_enh Z Q₃ h.2]
  | .type2 Xp Xm Qlp, h, a, b => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    simp only [enh, ECpl.code, code_enhC Z Xp h.1.1, code_enhC Z Xm h.1.2, code_enh Z Qlp h.2]

theorem code_enhC (Z : Finset (Fin w × Path)) : (X : RegChain) → X.dominant = true →
    (ζ : ℤˣ) → (a : Fin w × Path) → (enhC Z X ζ a).code = X
  | .nil, _, _, _ => rfl
  | .pair m Qr Qg inner rest, h, ζ, a => by
    simp only [RegChain.dominant, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hi, hr⟩, hg⟩, hs⟩ := h
    have hin : inner = .nil := by cases inner <;> simp_all [RegChain.isNil]
    subst hin
    simp only [enhC, EChain.code, code_enhC Z rest hs]
    congr 1
    · split_ifs <;> exact code_enh Z Qr hr _ _
    · split_ifs <;> exact code_enh Z Qg hg _ _
end

mutual
/-- **The bits of `enh Z 𝒬` read `Z` on the special candidates**, in order. -/
theorem bits_enh (Z : Finset (Fin w × Path)) : (Q : RegCpl) → Q.dominant = true →
    (a b : Fin w × Path) → (enh Z Q a b).bits = (cplSpecial Q a b).map fun z => decide (z ∈ Z)
  | .triv, _, _, _ => rfl
  | .type1 c Q₁ Q₂ Q₃, h, a, b => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    simp only [enh, ECpl.bits, cplSpecial, List.map_append, bits_enh Z Q₁ h.1.1,
      bits_enh Z Q₂ h.1.2, bits_enh Z Q₃ h.2]
  | .type2 Xp Xm Qlp, h, a, b => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    simp only [enh, ECpl.bits, cplSpecial, List.map_append, bits_enhC Z Xp h.1.1,
      bits_enhC Z Xm h.1.2, bits_enh Z Qlp h.2]

theorem bits_enhC (Z : Finset (Fin w × Path)) : (X : RegChain) → X.dominant = true →
    (ζ : ℤˣ) → (a : Fin w × Path) →
    (enhC Z X ζ a).bits = (chainSpecial X ζ a).map fun z => decide (z ∈ Z)
  | .nil, _, _, _ => rfl
  | .pair m Qr Qg inner rest, h, ζ, a => by
    simp only [RegChain.dominant, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hi, hr⟩, hg⟩, hs⟩ := h
    have hin : inner = .nil := by cases inner <;> simp_all [RegChain.isNil]
    subst hin
    have eR : (if slotSign ζ m.red.1 = 1 then
        enh Z Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
      else enh Z Qr (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1])).bits = (if slotSign ζ m.red.1 = 1 then
        cplSpecial Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
      else cplSpecial Qr (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1])).map fun z => decide (z ∈ Z) := by
      split_ifs <;> exact bits_enh Z Qr hr _ _
    have eG : (if slotSign ζ m.green.1 = 1 then
        enh Z Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
      else enh Z Qg (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1])).bits = (if slotSign ζ m.green.1 = 1 then
        cplSpecial Qg (addrExt a [m.green.1])
          (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
      else cplSpecial Qg (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1])).map fun z => decide (z ∈ Z) := by
      split_ifs <;> exact bits_enh Z Qg hg _ _
    simp only [enhC, EChain.bits, chainSpecial, RegChain.isNil, ↓reduceIte]
    rw [eR, eG, bits_enhC Z rest hs]
    simp only [List.map_append, List.map_cons, List.nil_append, List.append_nil, List.append_assoc,
      List.cons_append]
end

/-! ### An enhanced code is determined by its code and its bits -/

mutual
theorem ECpl.length_bits_eq : (e e' : ECpl) → e.code = e'.code → e.bits.length = e'.bits.length
  | .triv, .triv, _ => rfl
  | .triv, .type1 .., h => by simp [ECpl.code] at h
  | .triv, .type2 .., h => by simp [ECpl.code] at h
  | .type1 .., .triv, h => by simp [ECpl.code] at h
  | .type1 _ Q₁ Q₂ Q₃, .type1 _ Q₁' Q₂' Q₃', h => by
    simp only [ECpl.code, RegCpl.type1.injEq] at h
    simp only [ECpl.bits, List.length_append, ECpl.length_bits_eq Q₁ Q₁' h.2.1,
      ECpl.length_bits_eq Q₂ Q₂' h.2.2.1, ECpl.length_bits_eq Q₃ Q₃' h.2.2.2]
  | .type1 .., .type2 .., h => by simp [ECpl.code] at h
  | .type2 .., .triv, h => by simp [ECpl.code] at h
  | .type2 .., .type1 .., h => by simp [ECpl.code] at h
  | .type2 Xp Xm Qlp, .type2 Xp' Xm' Qlp', h => by
    simp only [ECpl.code, RegCpl.type2.injEq] at h
    simp only [ECpl.bits, List.length_append, EChain.length_bits_eq Xp Xp' h.1,
      EChain.length_bits_eq Xm Xm' h.2.1, ECpl.length_bits_eq Qlp Qlp' h.2.2]

theorem EChain.length_bits_eq : (X X' : EChain) → X.code = X'.code →
    X.bits.length = X'.bits.length
  | .nil, .nil, _ => rfl
  | .nil, .pair .., h => by simp [EChain.code] at h
  | .pair .., .nil, h => by simp [EChain.code] at h
  | .pair _ _ Qr Qg rest, .pair _ _ Qr' Qg' rest', h => by
    simp only [EChain.code, RegChain.pair.injEq] at h
    simp only [EChain.bits, List.length_cons, List.length_append,
      ECpl.length_bits_eq Qr Qr' h.2.1, ECpl.length_bits_eq Qg Qg' h.2.2.1,
      EChain.length_bits_eq rest rest' h.2.2.2.2]
end

theorem append3_inj {α : Type*} {a b c a' b' c' : List α} (ha : a.length = a'.length)
    (hb : b.length = b'.length) (h : a ++ b ++ c = a' ++ b' ++ c') : a = a' ∧ b = b' ∧ c = c' := by
  have h1 := List.append_inj h (by simp [ha, hb])
  have h2 := List.append_inj h1.1 ha
  exact ⟨h2.1, h2.2, h1.2⟩

mutual
/-- **An enhanced code is determined by its code and its bits.** -/
theorem ECpl.ext_code_bits : (e e' : ECpl) → e.code = e'.code → e.bits = e'.bits → e = e'
  | .triv, .triv, _, _ => rfl
  | .triv, .type1 .., h, _ => by simp [ECpl.code] at h
  | .triv, .type2 .., h, _ => by simp [ECpl.code] at h
  | .type1 .., .triv, h, _ => by simp [ECpl.code] at h
  | .type1 c Q₁ Q₂ Q₃, .type1 c' Q₁' Q₂' Q₃', h, hb => by
    simp only [ECpl.code, RegCpl.type1.injEq] at h
    simp only [ECpl.bits] at hb
    obtain ⟨b1, b2, b3⟩ := append3_inj (ECpl.length_bits_eq Q₁ Q₁' h.2.1)
      (ECpl.length_bits_eq Q₂ Q₂' h.2.2.1) hb
    rw [h.1, ECpl.ext_code_bits Q₁ Q₁' h.2.1 b1, ECpl.ext_code_bits Q₂ Q₂' h.2.2.1 b2,
      ECpl.ext_code_bits Q₃ Q₃' h.2.2.2 b3]
  | .type1 .., .type2 .., h, _ => by simp [ECpl.code] at h
  | .type2 .., .triv, h, _ => by simp [ECpl.code] at h
  | .type2 .., .type1 .., h, _ => by simp [ECpl.code] at h
  | .type2 Xp Xm Qlp, .type2 Xp' Xm' Qlp', h, hb => by
    simp only [ECpl.code, RegCpl.type2.injEq] at h
    simp only [ECpl.bits] at hb
    obtain ⟨b1, b2, b3⟩ := append3_inj (EChain.length_bits_eq Xp Xp' h.1)
      (EChain.length_bits_eq Xm Xm' h.2.1) hb
    rw [EChain.ext_code_bits Xp Xp' h.1 b1, EChain.ext_code_bits Xm Xm' h.2.1 b2,
      ECpl.ext_code_bits Qlp Qlp' h.2.2 b3]

theorem EChain.ext_code_bits : (X X' : EChain) → X.code = X'.code → X.bits = X'.bits → X = X'
  | .nil, .nil, _, _ => rfl
  | .nil, .pair .., h, _ => by simp [EChain.code] at h
  | .pair .., .nil, h, _ => by simp [EChain.code] at h
  | .pair m I Qr Qg rest, .pair m' I' Qr' Qg' rest', h, hb => by
    simp only [EChain.code, RegChain.pair.injEq] at h
    simp only [EChain.bits, List.cons.injEq] at hb
    obtain ⟨b1, b2, b3⟩ := append3_inj (ECpl.length_bits_eq Qr Qr' h.2.1)
      (ECpl.length_bits_eq Qg Qg' h.2.2.1) hb.2
    rw [h.1, hb.1, ECpl.ext_code_bits Qr Qr' h.2.1 b1, ECpl.ext_code_bits Qg Qg' h.2.2.1 b2,
      EChain.ext_code_bits rest rest' h.2.2.2.2 b3]
end

/-! ### Size, well-formedness, dominance of the underlying code -/

mutual
theorem ECpl.size_code : (e : ECpl) → e.code.size = 2 * e.hsize
  | .triv => rfl
  | .type1 _ Q₁ Q₂ Q₃ => by
    simp only [ECpl.code, RegCpl.size, ECpl.hsize, ECpl.size_code Q₁, ECpl.size_code Q₂,
      ECpl.size_code Q₃]
    ring
  | .type2 Xp Xm Qlp => by
    simp only [ECpl.code, RegCpl.size, ECpl.hsize, EChain.size_code Xp, EChain.size_code Xm,
      ECpl.size_code Qlp]
    ring

theorem EChain.size_code : (X : EChain) → X.code.size = 2 * X.hsize
  | .nil => rfl
  | .pair _ _ Qr Qg rest => by
    simp only [EChain.code, RegChain.size, EChain.hsize, ECpl.size_code Qr, ECpl.size_code Qg,
      EChain.size_code rest, RegChain.size]
    ring
end

theorem ECpl.isType2_code (e : ECpl) : e.code.isType2 = e.isType2 := by
  cases e <;> rfl

theorem EChain.isNil_code (X : EChain) : X.code.isNil = X.isNil := by
  cases X <;> rfl

mutual
theorem ECpl.wf_code : (e : ECpl) → e.code.wf = e.wf
  | .triv => rfl
  | .type1 _ Q₁ Q₂ Q₃ => by
    simp only [ECpl.code, RegCpl.wf, ECpl.wf, ECpl.wf_code Q₁, ECpl.wf_code Q₂, ECpl.wf_code Q₃]
  | .type2 Xp Xm Qlp => by
    simp only [ECpl.code, RegCpl.wf, ECpl.wf, EChain.wf_code Xp, EChain.wf_code Xm,
      ECpl.wf_code Qlp, ECpl.isType2_code, EChain.isNil_code]

theorem EChain.wf_code : (X : EChain) → X.code.wf = X.wf
  | .nil => rfl
  | .pair _ _ Qr Qg rest => by
    simp only [EChain.code, RegChain.wf, EChain.wf, ECpl.wf_code Qr, ECpl.wf_code Qg,
      EChain.wf_code rest, Bool.and_true]
end

mutual
theorem ECpl.dominant_code : (e : ECpl) → e.code.dominant = true
  | .triv => rfl
  | .type1 _ Q₁ Q₂ Q₃ => by
    simp only [ECpl.code, RegCpl.dominant, ECpl.dominant_code Q₁, ECpl.dominant_code Q₂,
      ECpl.dominant_code Q₃, Bool.and_self]
  | .type2 Xp Xm Qlp => by
    simp only [ECpl.code, RegCpl.dominant, EChain.dominant_code Xp, EChain.dominant_code Xm,
      ECpl.dominant_code Qlp, Bool.and_self]

theorem EChain.dominant_code : (X : EChain) → X.code.dominant = true
  | .nil => rfl
  | .pair _ _ Qr Qg rest => by
    simp only [EChain.code, RegChain.dominant, RegChain.isNil, ECpl.dominant_code Qr,
      ECpl.dominant_code Qg, EChain.dominant_code rest, Bool.and_self]
end

/-! ### The net sign only depends on the code -/

mutual
theorem ECpl.netSign_shape : (e : ECpl) → e.shape.netSign = (cplShape0 e.code).netSign
  | .triv => rfl
  | .type1 _ Q₁ Q₂ Q₃ => by
    simp only [ECpl.shape, ECpl.code, cplShape0, Shape.netSign, ECpl.netSign_shape Q₁,
      ECpl.netSign_shape Q₂, ECpl.netSign_shape Q₃]
  | .type2 Xp Xm Qlp => by
    simp only [ECpl.shape, ECpl.code, cplShape0, Shape.netSign, Tuples.netSign_append,
      EChain.netSign_tuples Xp, EChain.netSign_tuples Xm, ECpl.netSign_shape Qlp]

theorem EChain.netSign_tuples : (X : EChain) → X.tuples.netSign = (chainTuples0 X.code).netSign
  | .nil => rfl
  | .pair m _ Qr Qg rest => by
    simp only [EChain.tuples, EChain.code, chainTuples0, Tuples.netSign, ECpl.netSign_shape Qr,
      ECpl.netSign_shape Qg, EChain.netSign_tuples rest]
end

/-! ### The special weight -/

/-- The factor `(−ζ_z π i)^{-1}` of a node `z` of a garden with root signs `σ`. -/
noncomputable def wz (σ : Fin w → ℤˣ) (z : Fin w × Path) : ℂ :=
  (-((((nodeSign σ z : ℤˣ) : ℤ) : ℂ) * Real.pi * Complex.I))⁻¹

theorem wt_decide (σ : Fin w → ℤˣ) (Z : Finset (Fin w × Path)) (a : Fin w × Path) {ζ : ℤˣ}
    (ha : nodeSign σ a = ζ) : wt ζ (decide (a ∈ Z)) = if a ∈ Z then wz σ a else 1 := by
  unfold wt wz
  by_cases h : a ∈ Z <;> simp [h, ha]

mutual
/-- **The special weight of `enh Z 𝒬`**: the product of `(−ζ_z π i)^{-1}` over the special candidates
in `Z`, for a dominant code placed with signs `(+, -)`. -/
theorem sw_enh (σ : Fin w → ℤˣ) (Z : Finset (Fin w × Path)) : (Q : RegCpl) → Q.dominant = true →
    (a b : Fin w × Path) → nodeSign σ a = 1 → nodeSign σ b = -1 →
    (enh Z Q a b).sw = ((cplSpecial Q a b).map fun z => if z ∈ Z then wz σ z else 1).prod
  | .triv, _, _, _, _, _ => by simp [enh, ECpl.sw, cplSpecial]
  | .type1 c Q₁ Q₂ Q₃, h, a, b, sa, sb => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    have s0 : ∀ i, nodeSign σ (addrExt a [i]) = slotSign 1 i := fun i => by
      rw [nodeSign_ext, sa, pathSign_singleton]
    have s1 : ∀ i, nodeSign σ (addrExt b [i]) = slotSign (-1) i := fun i => by
      rw [nodeSign_ext, sb, pathSign_singleton]
    have hp0 : c.partner 0 ≠ 1 := by fin_cases c <;> decide
    have hp2 : c.partner 2 ≠ 1 := by fin_cases c <;> decide
    have e₁ := sw_enh σ Z Q₁ h.1.1 (addrExt a [0]) (addrExt b [c.partner 0])
      (by rw [s0]; rfl) (by rw [s1]; simp [slotSign, hp0])
    have e₂ := sw_enh σ Z Q₂ h.1.2 (addrExt b [1]) (addrExt a [1])
      (by rw [s1]; simp [slotSign]) (by rw [s0]; simp [slotSign])
    have e₃ := sw_enh σ Z Q₃ h.2 (addrExt a [2]) (addrExt b [c.partner 2])
      (by rw [s0]; rfl) (by rw [s1]; simp [slotSign, hp2])
    simp only [enh, ECpl.sw, cplSpecial, List.map_append, List.prod_append, e₁, e₂, e₃]
  | .type2 Xp Xm Qlp, h, a, b, sa, sb => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    simp only [enh, ECpl.sw, cplSpecial, List.map_append, List.prod_append,
      sw_enhC σ Z Xp h.1.1 1 a sa, sw_enhC σ Z Xm h.1.2 (-1) b sb,
      sw_enh σ Z Qlp h.2 (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) (by rw [nodeSign_spine, sa])
        (by rw [nodeSign_spine, sb])]

theorem sw_enhC (σ : Fin w → ℤˣ) (Z : Finset (Fin w × Path)) : (X : RegChain) → X.dominant = true →
    (ζ : ℤˣ) → (a : Fin w × Path) → nodeSign σ a = ζ →
    (enhC Z X ζ a).sw ζ = ((chainSpecial X ζ a).map fun z => if z ∈ Z then wz σ z else 1).prod
  | .nil, _, _, _, _ => by simp [enhC, EChain.sw, chainSpecial]
  | .pair m Qr Qg inner rest, h, ζ, a, sa => by
    simp only [RegChain.dominant, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hi, hr⟩, hg⟩, hs⟩ := h
    have hin : inner = .nil := by cases inner <;> simp_all [RegChain.isNil]
    subst hin
    obtain ⟨r1, r2, g1, g2⟩ := placed_signs σ a ζ sa m
    have eR : (if slotSign ζ m.red.1 = 1 then
        enh Z Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
      else enh Z Qr (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1])).sw = ((if slotSign ζ m.red.1 = 1 then
        cplSpecial Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
      else cplSpecial Qr (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1])).map fun z => if z ∈ Z then wz σ z else 1).prod := by
      split_ifs with hc
      · exact sw_enh σ Z Qr hr _ _ (by rw [r1, hc]) (by rw [r2, hc])
      · exact sw_enh σ Z Qr hr _ _ (by rw [r2, slotSign_eq_neg_one hc]; rfl)
          (by rw [r1, slotSign_eq_neg_one hc])
    have eG : (if slotSign ζ m.green.1 = 1 then
        enh Z Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
      else enh Z Qg (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1])).sw = ((if slotSign ζ m.green.1 = 1 then
        cplSpecial Qg (addrExt a [m.green.1])
          (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
      else cplSpecial Qg (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1])).map fun z => if z ∈ Z then wz σ z else 1).prod := by
      split_ifs with hc
      · exact sw_enh σ Z Qg hg _ _ (by rw [g1, hc]) (by rw [g2, hc])
      · exact sw_enh σ Z Qg hg _ _ (by rw [g2, slotSign_eq_neg_one hc]; rfl)
          (by rw [g1, slotSign_eq_neg_one hc])
    have sr : nodeSign σ (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.lone])) = ζ := by
      rw [nodeSign_chain_child, sa, slotSign_lone]
    simp only [enhC, EChain.sw, chainSpecial, RegChain.isNil, ↓reduceIte]
    rw [eR, eG, wt_decide σ Z a sa, slotSign_lone, sw_enhC σ Z rest hs ζ _ sr]
    simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
      List.prod_nil, List.singleton_append, mul_one]
    ring
end

end WaveTurbulence.Mexp
