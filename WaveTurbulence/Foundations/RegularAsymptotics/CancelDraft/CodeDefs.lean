/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.EnhancedDraft.NetSign
public import WaveTurbulence.Foundations.Cancel.MCBridge

/-!
# The time coefficients of regular couple codes (DH21 (newexp1), (newexp2)): data and the limit

DH21's time coefficient `B̃_Q(α, t, s)` of a regular couple is defined by the recursion (newexp1) for
type 1 and (newexp2) for type 2. wt-wke's MCB2 defines it on the B2 codes (not landed). Here:
* `RegChain.code`: the Catalan code of a chain (forgetful map, wt-wke's `RegChain → LegalCode`);
* `RegChain.pdata`: the pairs of a chain in preorder, each with its chosen node and its red and green
  couples with their root addresses (read off `RegChain.linksAt`);
* `BtRec Bt`: **the recursion (newexp1)/(newexp2) as hypotheses on a family `Bt Q a b`**, the named
  obligation discharged by MCB2's recursion lemmas. The time swaps (DH21 L924) are existential; the
  results do not depend on them;
* `RegCpl.Jc`: the limit of the regularized integrals (DH21 (recurtype1)/(recurtype2) with the F61
  signs).
-/

@[expose] public section

namespace WaveTurbulence.Cancel

open TTree WaveTurbulence.Reg WaveTurbulence.ClassJR WaveTurbulence.Links

/-- Node addresses of a couple. -/
abbrev Addr := Fin 2 × Path

/-- The node sign `ζ_𝔫` of an address of a couple (`+` tree `0`, `-` tree `1`). -/
def zetaA (v : Addr) : ℤ := ((nodeSign ![1, -1] v : ℤˣ) : ℤ)

theorem zetaA_pm (v : Addr) : zetaA v = 1 ∨ zetaA v = -1 := by
  unfold zetaA
  rcases Int.units_eq_one_or (nodeSign ![1, -1] v) with h | h <;> simp [h]

/-- The Catalan code of a chain (DH21 Prop 4.5(2)). -/
def chainCode : RegChain → LegalCode
  | .nil => .nil
  | .pair _ _ _ i r => .node (chainCode i) (chainCode r)

/-- The root addresses `(+, -)` of the red couple of a pair (as in `RegChain.linksAt`). -/
def redRoots (m : MiniTreeCode) (ζ : ℤˣ) (a : Addr) (i : RegChain) : Addr × Addr :=
  if slotSign ζ m.red.1 = 1 then (addrExt a [m.red.1], addrExt a ([m.c] ++ i.lonePath ++ [m.red.2]))
  else (addrExt a ([m.c] ++ i.lonePath ++ [m.red.2]), addrExt a [m.red.1])

/-- The root addresses `(+, -)` of the green couple of a pair. -/
def greenRoots (m : MiniTreeCode) (ζ : ℤˣ) (a : Addr) (i : RegChain) : Addr × Addr :=
  if slotSign ζ m.green.1 = 1 then (addrExt a [m.green.1], addrExt a ([m.c] ++ i.lonePath ++ [m.green.2]))
  else (addrExt a ([m.c] ++ i.lonePath ++ [m.green.2]), addrExt a [m.green.1])

/-- A pair of a chain: its chosen node, its red and its green couple with their roots. -/
abbrev PairDatum := Addr × (RegCpl × Addr × Addr) × (RegCpl × Addr × Addr)

/-- The default pair datum (never used inside a chain). -/
def dfltP : PairDatum := (((0 : Fin 2), []), (.triv, ((0 : Fin 2), []), ((0 : Fin 2), [])),
  (.triv, ((0 : Fin 2), []), ((0 : Fin 2), [])))

/-- **The pairs of a chain in preorder** (the order of DH21 §5.2, `ClassJR.chainT`). -/
def chainData : RegChain → ℤˣ → Addr → List PairDatum
  | .nil, _, _ => []
  | .pair m Qr Qg i r, ζ, a => (a, (Qr, redRoots m ζ a i), (Qg, greenRoots m ζ a i)) ::
      (chainData i (slotSign ζ m.c) (addrExt a [m.c]) ++
        chainData r (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ i.lonePath ++ [m.lone])))

theorem length_chainData : ∀ (X : RegChain) (ζ : ℤˣ) (a : Addr),
    (chainData X ζ a).length = (chainCode X).size
  | .nil, _, _ => rfl
  | .pair m _ _ i r, ζ, a => by
    simp only [chainData, List.length_cons, List.length_append, chainCode, LegalCode.size,
      length_chainData i, length_chainData r]

theorem linksAt_pair (m : MiniTreeCode) (Qr Qg : RegCpl) (i r : RegChain) (ζ : ℤˣ) (a : Addr) :
    (RegChain.pair m Qr Qg i r).linksAt ζ a = (a, addrExt a ([m.c] ++ i.lonePath)) ::
      (Qr.linksAt (redRoots m ζ a i).1 (redRoots m ζ a i).2 ++
        Qg.linksAt (greenRoots m ζ a i).1 (greenRoots m ζ a i).2 ++
        i.linksAt (slotSign ζ m.c) (addrExt a [m.c]) ++
        r.linksAt (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ i.lonePath ++ [m.lone]))) := by
  simp only [RegChain.linksAt, redRoots, greenRoots]
  split_ifs <;> rfl

/-! ### The recursion -/

/-- A time coefficient on the couple addresses. -/
abbrev TCoef := (Addr → ℝ) → ℝ → ℝ → ℂ

/-- The pair coefficient of DH21 (newexp2): the product of the coefficients of the red and green
couples, with time swaps. -/
def pairF (Bt : RegCpl → Addr → Addr → TCoef) (d : PairDatum) (sw : Bool × Bool) : TCoef :=
  fun α t s => swapT sw.1 (Bt d.2.1.1 d.2.1.2.1 d.2.1.2.2) α t s *
    swapT sw.2 (Bt d.2.2.1 d.2.2.2.1 d.2.2.2.2) α t s

/-- The pair variables of a chain. -/
def chainSig (L : List PairDatum) (j : ℕ) : Addr := (L.getD j dfltP).1

/-- **The recursion (newexp1)/(newexp2)** satisfied by DH21's time coefficients `B̃_Q`, as hypotheses
on a family `Bt Q a b` (`a`, `b` the roots of the `+` and `-` trees): the named obligation for MCB2.
* trivial couple: `1`;
* type 1 (DH21 (newexp1)): `type1F a sw (B̃_{Q₁}, B̃_{Q₂}, B̃_{Q₃})`, root variable `α_a`;
* type 2 (DH21 (newexp2), CPS form of wt-wke): `chainT⁺ t (t' ↦ chainT⁻ s (s' ↦ B̃_{Q_lp}(t', s')))`,
  pair variables the chosen nodes of the chain links, signs `ζ`, pair coefficients `pairF`. -/
structure BtRec (Bt : RegCpl → Addr → Addr → TCoef) : Prop where
  triv : ∀ a b, Bt .triv a b = fun _ _ _ => 1
  type1 : ∀ (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl) (a b : Addr), ∃ sw : Fin 3 → Bool,
    Bt (.type1 c Q₁ Q₂ Q₃) a b = type1F a sw ![Bt Q₁ (addrExt a [0]) (addrExt b [c.partner 0]),
      Bt Q₂ (addrExt b [1]) (addrExt a [1]), Bt Q₃ (addrExt a [2]) (addrExt b [c.partner 2])]
  type2 : ∀ (Xp Xm : RegChain) (Qlp : RegCpl) (a b : Addr),
    ∃ (swp swm : ℕ → Bool × Bool) (swl : Bool), Bt (.type2 Xp Xm Qlp) a b = fun α t s =>
      chainT (chainSig (chainData Xp 1 a)) (fun j => zetaA (chainSig (chainData Xp 1 a) j)) (chainCode Xp) 0
        (fun j => pairF Bt ((chainData Xp 1 a).getD j dfltP) (swp j)) α t
        (fun t' => chainT (chainSig (chainData Xm (-1) b)) (fun j => zetaA (chainSig (chainData Xm (-1) b) j))
          (chainCode Xm) 0 (fun j => pairF Bt ((chainData Xm (-1) b).getD j dfltP) (swm j)) α s
          (fun s' => swapT swl (Bt Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)) α t' s'))

/-! ### The limit -/

mutual
/-- **The limit of the regularized integrals of `B̃_Q`** with the weights of `Z`: DH21 (recurtype1),
(recurtype2), with the factor `-1` of each chain pair in `Z` (F61), `0` for a type 1 root in `Z` and `0`
for a non-adjacent pair. -/
noncomputable def cplJ (Z : Finset Addr) : RegCpl → Addr → Addr → ℝ → ℝ → ℂ
  | .triv, _, _, _, _ => 1
  | .type1 c Q₁ Q₂ Q₃, a, b, t, s => if a ∈ Z then 0 else
      2 * ∫ τ in (0 : ℝ)..min t s, cplJ Z Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) τ τ *
        cplJ Z Q₂ (addrExt b [1]) (addrExt a [1]) τ τ * cplJ Z Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) τ τ
  | .type2 Xp Xm Qlp, a, b, t, s => chainJ Z Xp 1 a t (fun t' => chainJ Z Xm (-1) b s
      (fun s' => cplJ Z Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) t' s'))

/-- The limit along a chain. -/
noncomputable def chainJ (Z : Finset Addr) : RegChain → ℤˣ → Addr → ℝ → (ℝ → ℂ) → ℂ
  | .nil, _, _, t, g => g t
  | .pair m Qr Qg .nil r, ζ, a, t, g => ∫ τ in (0 : ℝ)..t, (if a ∈ Z then (-1 : ℂ) else 1) *
      (cplJ Z Qr (redRoots m ζ a .nil).1 (redRoots m ζ a .nil).2 τ τ *
        cplJ Z Qg (greenRoots m ζ a .nil).1 (greenRoots m ζ a .nil).2 τ τ) *
      chainJ Z r (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.lone])) τ g
  | .pair _ _ _ (.pair _ _ _ _ _) _, _, _, _, _ => 0
end

end WaveTurbulence.Cancel
