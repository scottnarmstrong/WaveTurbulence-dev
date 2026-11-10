/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.MexpDraft.ECode

/-!
# DH21 Prop 7.7 (`multiexp`, L1814–L1837): `ℳ*_{(𝒬,Z)}` depends only on the equivalence class

The momentum factor `ℳ*_{(𝒬,Z)}(k)` of an enhanced dominant couple (B2 `RegCpl.Mstar`, T (regref3-0)–(regref3-4),
DH21 (defintegral)) is a function of the class data of `(𝒬, Z)` (ENHANCED `cplShape`):

* `Mshape F X`: the recursion (inductm01)–(inductm05) of DH21 Prop 7.7 on class data `X`. Type 1: the resonant
  integral of `∏_j ℳ*_{X_j}(k_j)`; type 2: `ℳ*_𝒴(k) ∏_j ℳ*_{(j)}(k)`, where `ℳ*_{(j)}` (`Npair`) integrates
  `ℳ*_{X_{j,1}} ℳ*_{X_{j,2}}` at the positions `(k₂,k₃)`, `(k₁,k₃)`, `(k₁,k₂)` for `𝚌_j = 1, 2, 3` against
  `δ(Ω)` (`𝙸_j = 0`) or `p.v. 1/Ω` (`𝙸_j = 1`).
* `mstar_eq_mshape`: for a dominant code, `ℳ*_{(𝒬,Z)} = Mshape F (cplShape Z 𝒬 a b)`.
* `mshape_congr`: `Mshape F` is constant on equivalence classes (`Shape.Equiv`: a permutation of the tuples
  permutes the factors `ℳ*_{(j)}`).
* **`prop77`**: equivalent enhanced dominant couples have the same `ℳ*`.
-/

@[expose] public section

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links

variable {d : ℕ}

/-- The position of the red leaf child of `𝔫_{2j-1}` under `𝔫_{2j-1}` for `𝚌 - 1 = c` (`k₂, k₁, k₁`). -/
def redSlot (c : Fin 3) : Fin 3 := if c = 0 then 1 else 0

/-- The position of the green leaf child of `𝔫_{2j-1}` for `𝚌 - 1 = c` (`k₃, k₃, k₂`). -/
def greenSlot (c : Fin 3) : Fin 3 := if c = 2 then 1 else 2

theorem red_fst (m : MiniTreeCode) : m.red.1 = redSlot m.c := by
  obtain ⟨c, b⟩ := m
  fin_cases c <;> fin_cases b <;> rfl

theorem green_fst (m : MiniTreeCode) : m.green.1 = greenSlot m.c := by
  obtain ⟨c, b⟩ := m
  fin_cases c <;> fin_cases b <;> rfl

/-- **The chain-pair factor `ℳ*_{(j)}`** (DH21 (inductm03)–(inductm05); T (regref3-2)–(regref3-4)): the
resonant integral (`𝙸 = 0`) or its principal value (`𝙸 = 1`) of `f(k_x) g(k_y)`, `(x, y)` the positions of
the red and green leaf children. -/
noncomputable def Npair (I : Bool) (c : Fin 3) (f g : Mom d → ℝ) (k : Mom d) : ℝ :=
  if I then pvResonantIntegral (fun k₁ k₂ k₃ => f (![k₁, k₂, k₃] (redSlot c)) * g (![k₁, k₂, k₃] (greenSlot c))) k
  else resIntegral (fun k₁ k₂ k₃ => f (![k₁, k₂, k₃] (redSlot c)) * g (![k₁, k₂, k₃] (greenSlot c))) k

mutual
/-- **`ℳ*_X(k)[F]` of a class `X`** (DH21 Prop 7.7, (inductm01)–(inductm05)). -/
noncomputable def Mshape (F : Mom d → ℝ) : Shape → Mom d → ℝ
  | .triv => F
  | .type1 X₁ X₂ X₃ => fun k =>
    resIntegral (fun k₁ k₂ k₃ => Mshape F X₁ k₁ * Mshape F X₂ k₂ * Mshape F X₃ k₃) k
  | .type2 L Y => fun k => Mshape F Y k * Mtuples F L k

/-- The product `∏_j ℳ*_{(j)}(k)` over a list of tuples. -/
noncomputable def Mtuples (F : Mom d → ℝ) : Tuples → Mom d → ℝ
  | .nil => fun _ => 1
  | .cons I c X₁ X₂ rest => fun k => Npair I c (Mshape F X₁) (Mshape F X₂) k * Mtuples F rest k
end

theorem mtuples_append (F : Mom d → ℝ) : (L L' : Tuples) → (k : Mom d) →
    Mtuples F (L.append L') k = Mtuples F L k * Mtuples F L' k
  | .nil, L', k => by simp [Tuples.append, Mtuples]
  | .cons I c X₁ X₂ rest, L', k => by
    simp only [Tuples.append, Mtuples, mtuples_append F rest L' k]
    ring

/-- `∏_j ℳ*_{(j)}` as a product over the tuple positions. -/
theorem mtuples_eq_prod (F : Mom d → ℝ) : (L : Tuples) → (k : Mom d) →
    Mtuples F L k = ∏ i, Npair (L.get i).1 (L.get i).2.1 (Mshape F (L.get i).2.2.1)
      (Mshape F (L.get i).2.2.2) k
  | .nil, k => by
    show (1 : ℝ) = ∏ i : Fin 0, _
    simp
  | .cons I c X₁ X₂ rest, k => by
    rw [Tuples.prod_cons I c X₁ X₂ rest (fun x => Npair x.1 x.2.1 (Mshape F x.2.2.1)
      (Mshape F x.2.2.2) k), ← mtuples_eq_prod F rest k]
    rfl

/-- **`Mshape` is constant on equivalence classes** (DH21 Prop 7.7, first claim; the recursion is invariant
under permuting the tuples). -/
theorem mshape_congr (F : Mom d → ℝ) {S S' : Shape} (h : Shape.Equiv S S') :
    Mshape F S = Mshape F S' := by
  induction h with
  | triv => rfl
  | type1 _ _ _ ih₁ ih₂ ih₃ =>
    funext k
    simp only [Mshape, ih₁, ih₂, ih₃]
  | @type2 L L' Y Y' e hI hc _ _ _ ih₁ ih₂ ihY =>
    funext k
    simp only [Mshape, ihY]
    congr 1
    rw [mtuples_eq_prod, mtuples_eq_prod]
    refine Fintype.prod_equiv e _ _ fun i => ?_
    rw [hI i, hc i, ih₁ i, ih₂ i]

/-! ### `ℳ*_{(𝒬,Z)}` of B2 is `Mshape` of the class data -/

variable {w : ℕ}

mutual
/-- **`ℳ*_{(𝒬,Z)}` is `Mshape` of the class data** (B2 `RegCpl.Mstar`, ENHANCED `cplShape`). -/
theorem mstar_eq_mshape (F : Mom d → ℝ) (Z : Finset (Fin w × Path)) : (Q : RegCpl) →
    Q.dominant = true → (a b : Fin w × Path) → Q.Mstar F Z a b = Mshape F (cplShape Z Q a b)
  | .triv, _, _, _ => rfl
  | .type1 c Q₁ Q₂ Q₃, h, a, b => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    funext k
    simp only [RegCpl.Mstar, cplShape, Mshape, mstar_eq_mshape F Z Q₁ h.1.1,
      mstar_eq_mshape F Z Q₂ h.1.2, mstar_eq_mshape F Z Q₃ h.2]
  | .type2 Xp Xm Qlp, h, a, b => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    funext k
    simp only [RegCpl.Mstar, cplShape, Mshape, mtuples_append, mstar_eq_mshape F Z Qlp h.2,
      nstar_eq_mtuples F Z Xp h.1.1, nstar_eq_mtuples F Z Xm h.1.2]
    ring

/-- `∏_j 𝒩*_{(j,ε)}` of a dominant chain is `Mtuples` of its tuples. -/
theorem nstar_eq_mtuples (F : Mom d → ℝ) (Z : Finset (Fin w × Path)) : (X : RegChain) →
    X.dominant = true → (ζ : ℤˣ) → (a : Fin w × Path) →
    X.Nstar F Z ζ a = Mtuples F (chainTuples Z X ζ a)
  | .nil, _, _, _ => rfl
  | .pair m Qr Qg inner rest, h, ζ, a => by
    simp only [RegChain.dominant, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hi, hr⟩, hg⟩, hs⟩ := h
    have hin : inner = .nil := by cases inner <;> simp_all [RegChain.isNil]
    subst hin
    have eR : (if slotSign ζ m.red.1 = 1 then
        Qr.Mstar F Z (addrExt a [m.red.1]) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
      else Qr.Mstar F Z (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1])) = Mshape F (if slotSign ζ m.red.1 = 1 then
        cplShape Z Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
      else cplShape Z Qr (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1])) := by
      split_ifs <;> exact mstar_eq_mshape F Z Qr hr _ _
    have eG : (if slotSign ζ m.green.1 = 1 then
        Qg.Mstar F Z (addrExt a [m.green.1])
          (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
      else Qg.Mstar F Z (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1])) = Mshape F (if slotSign ζ m.green.1 = 1 then
        cplShape Z Qg (addrExt a [m.green.1])
          (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
      else cplShape Z Qg (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1])) := by
      split_ifs <;> exact mstar_eq_mshape F Z Qg hg _ _
    funext k
    simp only [RegChain.Nstar, chainTuples, Mtuples]
    rw [eR, eG, nstar_eq_mtuples F Z rest hs, red_fst, green_fst]
    simp only [Npair, decide_eq_true_eq, mul_one]
end

end WaveTurbulence.Mexp
