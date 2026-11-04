/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCType2

/-!
# Codes of regular couples and their coefficients `B̃_Q`

**Copied definitions.** §1 and §2 below copy, verbatim up to the namespace, the code types and links
of the Wave B tier B2 draft `/home/scott/wt-scratch/waveb2/WaveB2-Regular.lean`
(sha256 `4d7f81efa32b54e5720aac452ea7d5e458cf6ee3052b9378763d37437cc5d052`): §1 (mini-couples and
mini-trees), the code types `RegCpl`/`RegChain` and `RegChain.lonePath` of §3, `wf`/`size` of §3, and
`linksAt`, `links`, `chosenSet` of §5. `Path` is Wave B's `TTree.Path = List (Fin 3)`. When B2 lands,
these copies are deleted and the coefficients below are restated on the landed types.

**The coefficients.** `RegCpl.Bt Q x y` is DH21's `B̃_Q(t, s, α[𝒩^ch])` for the code `Q` with `+` root
at the address `x` and `-` root at `y`, defined by the recursions (newexp1) and (newexp2) (DH21
L923–L937), as B2 defines `𝒥ℬ*` (`RegCpl.JB`). The variables are the addresses `Fin 2 × Path`; the
chosen nodes are the first components of `linksAt` (DH21 Def 4.11), and the chain signs are the node
signs `ζ_𝔫` (`nodeSgn`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

/-! ## §1 Mini-couples and mini-trees (copied from B2 §1) -/

/-- Node addresses: the path from the root (Wave B `TTree.Path`). -/
abbrev Path := List (Fin 3)

/-- The code of a `(1,1)`-mini-couple (T Def `defreg`, Figure `MiniCpl.png`; WAVE-B §3.1): `0` is code
`00` (straight: `L⁺ ↔ L⁻`, `R⁺ ↔ R⁻`), `1` is code `01` (crossed: `L⁺ ↔ R⁻`, `R⁺ ↔ L⁻`); always
`M⁺ ↔ M⁻`. Colours: red, green, blue = the pairs containing `L⁺`, `M⁺`, `R⁺` (first tree = the `+`
tree, figure-defs M1). -/
abbrev MiniCplCode := Fin 2

/-- The slot of the `-` tree paired with slot `x` of the `+` tree. -/
@[expose] def MiniCplCode.partner (c : MiniCplCode) (x : Fin 3) : Fin 3 := if c = 0 then x else 2 - x

/-- The code of a mini-tree (T Def `defreg`, Figure `MiniTree.png`; WAVE-B §3.2, figure-defs §5): a
root `ρ` with a branching child `ν` at slot `c` (`0, 1, 2` = L, M, R; first code digit `c + 1`) and
second digit `b`. -/
structure MiniTreeCode where
  /-- the slot of the inner node `ν` under the root `ρ` -/
  c : Fin 3
  /-- the second code digit -/
  b : Fin 2

/-- `MiniTreeCode ≃ Fin 3 × Fin 2`. -/
@[expose] def MiniTreeCode.equiv : MiniTreeCode ≃ Fin 3 × Fin 2 :=
  ⟨fun m => (m.c, m.b), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

@[expose, instance_reducible, instance] def instDecidableEqMiniTreeCode :
    DecidableEq MiniTreeCode :=
  MiniTreeCode.equiv.injective.decidableEq

@[expose, instance_reducible, instance] def instFintypeMiniTreeCode : Fintype MiniTreeCode :=
  Fintype.ofEquiv _ MiniTreeCode.equiv.symm

namespace MiniTreeCode

/-- The slot of the lone leaf under `ν` (table of WAVE-B §3.2): codes `10, 11, 20, 21, 30, 31` give
`L, R, M, M, R, L`. -/
@[expose] def lone (m : MiniTreeCode) : Fin 3 :=
  (![![0, 2], ![1, 1], ![2, 0]] : Fin 3 → Fin 2 → Fin 3) m.c m.b

/-- The red pair `(ρ-slot, ν-slot)`: the pair containing the leftmost leaf child of `ρ`. -/
@[expose] def red (m : MiniTreeCode) : Fin 3 × Fin 3 :=
  (![![(1, 2), (1, 0)], ![(0, 0), (0, 2)], ![(0, 1), (0, 1)]] : Fin 3 → Fin 2 → Fin 3 × Fin 3) m.c m.b

/-- The green pair `(ρ-slot, ν-slot)`: the pair containing the other leaf child of `ρ`. -/
@[expose] def green (m : MiniTreeCode) : Fin 3 × Fin 3 :=
  (![![(2, 1), (2, 1)], ![(2, 2), (2, 0)], ![(1, 0), (1, 2)]] : Fin 3 → Fin 2 → Fin 3 × Fin 3) m.c m.b

end MiniTreeCode

/-- The sign of the child at slot `i` of a node of sign `ζ`: `(ζ, -ζ, ζ)` (T L627). -/
@[expose] def slotSign (ζ : ℤˣ) (i : Fin 3) : ℤˣ := if i = 1 then -ζ else ζ

/-- The address `a` extended by the path `p`. -/
@[expose] def addrExt {w : ℕ} (a : Fin w × Path) (p : Path) : Fin w × Path := (a.1, a.2 ++ p)

/-! ## §2 Codes and links (copied from B2 §3, §5) -/

mutual
/-- **Codes of regular couples** (the structure data of T Prop `propstructure`, recommended form of
WAVE-B §2.7 item 3): trivial; type 1 = a mini-couple of code `c` whose red, green, blue leaf pairs
are replaced by `Q₁, Q₂, Q₃`; type 2 = two regular chains `𝒳⁺`, `𝒳⁻` (with their couples) whose lone
leaves are paired and replaced by `Q_lp`. -/
inductive RegCpl : Type
  | triv : RegCpl
  | type1 (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl) : RegCpl
  | type2 (Xp Xm : RegChain) (Qlp : RegCpl) : RegCpl

/-- **Codes of regular chains with their couples** (T Def `defregchain`, `propstructure`): a legal
(non-crossing) partition of `{1,…,2m}` in Catalan form. `pair m Qr Qg inner rest` pairs the first chain
node `𝔫_a` with `𝔫_b`, where `inner` codes the chain nodes strictly between them and `rest` those after
`𝔫_b`; `m` is the mini-tree code of the rearrangement of `𝔫_a, 𝔫_b`, and its red and green leaf
pairs are replaced by `Qr = 𝒬_{j,ε,1}`, `Qg = 𝒬_{j,ε,2}`. -/
inductive RegChain : Type
  | nil : RegChain
  | pair (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) : RegChain
end

/-- The path of the lone leaf of a chain (from its root `𝔫_1`). -/
@[expose] def RegChain.lonePath : RegChain → Path
  | .nil => []
  | .pair m _ _ inner rest => [m.c] ++ inner.lonePath ++ [m.lone] ++ rest.lonePath

/-- Is the code of type 2? -/
@[expose] def RegCpl.isType2 : RegCpl → Bool
  | .type2 .. => true
  | _ => false

/-- Is the chain empty? -/
@[expose] def RegChain.isNil : RegChain → Bool
  | .nil => true
  | _ => false

mutual
/-- **Well-formedness** (the uniqueness side conditions of T Prop `propstructure` (b)). -/
@[expose] def RegCpl.wf : RegCpl → Bool
  | .triv => true
  | .type1 _ Q₁ Q₂ Q₃ => Q₁.wf && Q₂.wf && Q₃.wf
  | .type2 Xp Xm Qlp => Xp.wf && Xm.wf && Qlp.wf && !Qlp.isType2 && !(Xp.isNil && Xm.isNil)

/-- Well-formedness of a chain code (its couples are well formed). -/
@[expose] def RegChain.wf : RegChain → Bool
  | .nil => true
  | .pair _ Qr Qg inner rest => Qr.wf && Qg.wf && inner.wf && rest.wf
end

mutual
/-- The order `n(𝒬)` of the decoded couple (number of branching nodes). -/
@[expose] def RegCpl.size : RegCpl → ℕ
  | .triv => 0
  | .type1 _ Q₁ Q₂ Q₃ => Q₁.size + Q₂.size + Q₃.size + 2
  | .type2 Xp Xm Qlp => Xp.size + Xm.size + Qlp.size

/-- The number of branching nodes of a chain with its couples. -/
@[expose] def RegChain.size : RegChain → ℕ
  | .nil => 0
  | .pair _ Qr Qg inner rest => Qr.size + Qg.size + inner.size + rest.size + 2
end

mutual
/-- **Links** of a couple code (T Prop `deflink`, L874–L882), as `(chosen, other)` pairs of branching
node addresses; the `+` tree is rooted at `a`, the `-` tree at `b`. -/
@[expose] def RegCpl.linksAt {w : ℕ} : RegCpl → (Fin w × Path) → (Fin w × Path) →
    List ((Fin w × Path) × (Fin w × Path))
  | .triv, _, _ => []
  | .type1 c Q₁ Q₂ Q₃, a, b =>
    (a, b) :: (Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0]) ++
      Q₂.linksAt (addrExt b [1]) (addrExt a [1]) ++
      Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2]))
  | .type2 Xp Xm Qlp, a, b =>
    Xp.linksAt 1 a ++ Xm.linksAt (-1) b ++
      Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)

/-- Links of a chain rooted at `a` with root sign `ζ` (and of its couples). -/
@[expose] def RegChain.linksAt {w : ℕ} : RegChain → ℤˣ → (Fin w × Path) →
    List ((Fin w × Path) × (Fin w × Path))
  | .nil, _, _ => []
  | .pair m Qr Qg inner rest, ζ, a =>
    (a, addrExt a ([m.c] ++ inner.lonePath)) ::
    ((if slotSign ζ m.red.1 = 1 then
        Qr.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Qr.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) ++
    (if slotSign ζ m.green.1 = 1 then
        Qg.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Qg.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) ++
    inner.linksAt (slotSign ζ m.c) (addrExt a [m.c]) ++
    rest.linksAt (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])))
end

/-- The links of a couple code (trees rooted at `(0, [])`, `(1, [])`). -/
@[expose] def RegCpl.links (Q : RegCpl) : List ((Fin 2 × Path) × (Fin 2 × Path)) :=
  Q.linksAt (0, []) (1, [])

/-- **`𝒩^ch`** (T Prop `deflink`, last paragraph; DH21 Def 4.11, review P6): one node of each link. -/
@[expose] def chosenSet {w : ℕ} (links : List ((Fin w × Path) × (Fin w × Path))) :
    Finset (Fin w × Path) :=
  (links.map Prod.fst).toFinset

/-! ## §3 The coefficients `B̃_Q` -/

/-- The variables of a couple: the node addresses. -/
abbrev Addr : Type := Fin 2 × Path

/-- The sign `ζ_𝔫` of the node at an address: the root sign (`+` for tree `0`, `-` for tree `1`)
times `(-1)^{#mid steps}` (children of a node of sign `ζ'` have signs `(ζ', -ζ', ζ')`, T L627). -/
@[expose] def nodeSgn (v : Addr) : ℤ := (if v.1 = 0 then 1 else -1) * (-1) ^ (v.2.count 1)

theorem nodeSgn_eq (v : Addr) : nodeSgn v = 1 ∨ nodeSgn v = -1 := by
  unfold nodeSgn
  rcases neg_one_pow_eq_or ℤ (v.2.count 1) with h | h <;> split_ifs <;> simp [h]

/-- The Catalan code (legal partition) of a chain. -/
@[expose] def RegChain.code : RegChain → LegalCode
  | .nil => .nil
  | .pair _ _ _ inner rest => .node inner.code rest.code

/-- The chosen node `𝔫_a` of each pair of a chain rooted at `x` (pairs numbered from `q`, in
preorder as in DH21 §5.2 and B2's `linksAt`). -/
@[expose] def RegChain.sigmaAt : RegChain → Addr → ℕ → ℕ → Addr
  | .nil, x, _ => fun _ => x
  | .pair m _ _ inner rest, x, q => fun j =>
    if j = q then x
    else if j < q + 1 + inner.code.size then inner.sigmaAt (addrExt x [m.c]) (q + 1) j
    else rest.sigmaAt (addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])) (q + inner.code.size + 1) j

mutual
/-- **The coefficient `B̃_Q(t, s, α[𝒩^ch])`** of a couple code with `+` root `x` and `-` root `y`,
by DH21 (newexp1) and (newexp2):
* trivial: `1`;
* type 1: `∫_0^t ∫_0^s e^{πiα_x(t₁ - s₁)} ∏_j B̃_{Q_j}` with the times of `Q₂` (whose `+` root is in
  the `-` tree) swapped;
* type 2: the `+` chain in `t`, the `-` chain in `s` (signs `ε_j = ζ_{𝔫_a}`), and `B̃_{Q_lp}` at the
  last times. -/
@[expose] noncomputable def RegCpl.Bt : RegCpl → Addr → Addr → (Addr → ℝ) → ℝ → ℝ → ℂ
  | .triv, _, _ => fun _ _ _ => 1
  | .type1 c Q₁ Q₂ Q₃, x, y => type1F x ![false, true, false]
      ![Q₁.Bt (addrExt x [0]) (addrExt y [c.partner 0]), Q₂.Bt (addrExt y [1]) (addrExt x [1]),
        Q₃.Bt (addrExt x [2]) (addrExt y [c.partner 2])]
  | .type2 Xp Xm Qlp, x, y => type2F (Xp.sigmaAt x 0) (fun j => nodeSgn (Xp.sigmaAt x 0 j))
      Xp.code (Xp.coefAt 1 x 0) (Xm.sigmaAt y 0) (fun j => nodeSgn (Xm.sigmaAt y 0 j)) Xm.code
      (Xm.coefAt (-1) y 0) (Qlp.Bt (addrExt x Xp.lonePath) (addrExt y Xm.lonePath))

/-- **The pair coefficients** `∏_ι B̃_{Q_{j,ι}}(t_a, t_b)` of a chain rooted at `x` with root sign `ζ`
(pairs numbered from `q`); the times of a couple are swapped when its `+` root hangs from `𝔫_b`. -/
@[expose] noncomputable def RegChain.coefAt :
    RegChain → ℤˣ → Addr → ℕ → ℕ → (Addr → ℝ) → ℝ → ℝ → ℂ
  | .nil, _, _, _ => fun _ _ _ _ => 0
  | .pair m Qr Qg inner rest, ζ, x, q => fun j =>
    if j = q then fun α ta tb =>
      (if slotSign ζ m.red.1 = 1 then
          Qr.Bt (addrExt x [m.red.1]) (addrExt x ([m.c] ++ inner.lonePath ++ [m.red.2])) α ta tb
        else Qr.Bt (addrExt x ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt x [m.red.1]) α tb ta) *
      (if slotSign ζ m.green.1 = 1 then
          Qg.Bt (addrExt x [m.green.1]) (addrExt x ([m.c] ++ inner.lonePath ++ [m.green.2])) α ta tb
        else Qg.Bt (addrExt x ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt x [m.green.1])
          α tb ta)
    else if j < q + 1 + inner.code.size then inner.coefAt (slotSign ζ m.c) (addrExt x [m.c]) (q + 1) j
    else rest.coefAt (slotSign (slotSign ζ m.c) m.lone)
      (addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])) (q + inner.code.size + 1) j
end

/-- The variables of the pair coefficients of a chain. -/
@[expose] def RegChain.varsAt : RegChain → ℤˣ → Addr → ℕ → ℕ → Finset Addr
  | .nil, _, _, _ => fun _ => ∅
  | .pair m Qr Qg inner rest, ζ, x, q => fun j =>
    if j = q then
      chosenSet (if slotSign ζ m.red.1 = 1 then
          Qr.linksAt (addrExt x [m.red.1]) (addrExt x ([m.c] ++ inner.lonePath ++ [m.red.2]))
        else Qr.linksAt (addrExt x ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt x [m.red.1])) ∪
      chosenSet (if slotSign ζ m.green.1 = 1 then
          Qg.linksAt (addrExt x [m.green.1]) (addrExt x ([m.c] ++ inner.lonePath ++ [m.green.2]))
        else Qg.linksAt (addrExt x ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt x [m.green.1]))
    else if j < q + 1 + inner.code.size then inner.varsAt (slotSign ζ m.c) (addrExt x [m.c]) (q + 1) j
    else rest.varsAt (slotSign (slotSign ζ m.c) m.lone)
      (addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])) (q + inner.code.size + 1) j

mutual
/-- **The constant of `B̃_Q`** produced by the recursion. -/
@[expose] noncomputable def RegCpl.NB (θ a b : ℝ) : RegCpl → ℝ
  | .triv => N1 θ
  | .type1 _ Q₁ Q₂ Q₃ => KC1 θ a b * (Q₁.NB θ a b * Q₂.NB θ a b * Q₃.NB θ a b)
  | .type2 Xp Xm Qlp => Nchain' θ a b Xp.code (Xp.NBAt θ a b 0)
      (Nchain' θ a b Xm.code (Xm.NBAt θ a b 0) (Qlp.NB θ a b))

/-- The constants of the pair coefficients of a chain. -/
@[expose] noncomputable def RegChain.NBAt (θ a b : ℝ) : RegChain → ℕ → ℕ → ℝ
  | .nil, _ => fun _ => 0
  | .pair _ Qr Qg inner rest, q => fun j =>
    if j = q then 4 * Qr.NB θ a b * Qg.NB θ a b
    else if j < q + 1 + inner.code.size then inner.NBAt θ a b (q + 1) j
    else rest.NBAt θ a b (q + inner.code.size + 1) j
end

end WaveTurbulence.ClassJR
