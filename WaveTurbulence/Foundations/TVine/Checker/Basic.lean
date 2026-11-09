/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Nat.Notation

/-!
# The compact T-vine checker: encodings and `Bool` primitives

Packet L2 (TVINE-CHECKER), PLAN §5(b). Everything here is a plain `Bool`/`ℕ` program by structural recursion
on `List`/`ℕ`, meant to be evaluated by the kernel (`decide +kernel` only; no compiled evaluation).

**Encodings.**
* A multigraph is a list of bond copies `(a, b) : ℕ × ℕ` (unordered; a pair occurring `m` times has
  multiplicity `m`).
* A vertex set is a bitmask `S : ℕ` (`v ∈ S` iff `S.testBit v`). Instances have at most 13 atoms.

The soundness theorems (into the pinned `TVine.Defs` API) are in the companion modules.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

/-- Bond copies of an undirected multigraph on `ℕ`. -/
abbrev Edges := List (ℕ × ℕ)

/-! ## Bitmask vertex sets -/

/-- The singleton bitmask `{v}`. -/
def bit (v : ℕ) : ℕ := 1 <<< v

/-- Membership in a bitmask. -/
def mem (v S : ℕ) : Bool := S.testBit v

/-- The bitmask `{0, …, n-1}`. -/
def full (n : ℕ) : ℕ := (1 <<< n) - 1

/-- Set difference of bitmasks. -/
def sdiff (S T : ℕ) : ℕ := S ^^^ (S &&& T)

/-- The least element of `S` below `32` (the instances have at most 13 atoms, named below `32`), if any. -/
def lowBit (S : ℕ) : Option ℕ := (List.range 32).find? fun v => mem v S

/-- The elements of `S` below `32`, increasing. -/
def elems (S : ℕ) : List ℕ := (List.range 32).filter fun v => mem v S

/-! ## Multiplicities and degrees -/

/-- `(x, y)` is a copy of the pair `{a, b}`. -/
def isPair (a b : ℕ) (e : ℕ × ℕ) : Bool := (e.1.beq a && e.2.beq b) || (e.1.beq b && e.2.beq a)

/-- The multiplicity of the pair `{a, b}`. -/
def mult (es : Edges) (a b : ℕ) : ℕ := (es.filter (isPair a b)).length

/-- `v` is an end of the bond copy `e`. -/
def touches (v : ℕ) (e : ℕ × ℕ) : Bool := e.1.beq v || e.2.beq v

/-- The degree of `v` (a loop would count twice; the instances are loopless). -/
def deg (es : Edges) (v : ℕ) : ℕ :=
  (es.filter fun e => e.1.beq v).length + (es.filter fun e => e.2.beq v).length

/-- The bond copies with both ends in `S`. -/
def inside (S : ℕ) (es : Edges) : Edges := es.filter fun e => mem e.1 S && mem e.2 S

/-- The far ends of the bond copies at `v` (with repetition). -/
def nbrs (es : Edges) (v : ℕ) : List ℕ :=
  es.filterMap fun e => if e.1.beq v then some e.2 else if e.2.beq v then some e.1 else none

/-- No loops. -/
def loopless (es : Edges) : Bool := es.all fun e => !e.1.beq e.2

/-- Every multiplicity is at most `2`. -/
def multLe2 (es : Edges) : Bool := es.all fun e => mult es e.1 e.2 ≤ 2

/-- Remove the first copy of the pair `{a, b}`. -/
def eraseOne : Edges → ℕ → ℕ → Edges
  | [], _, _ => []
  | e :: es, a, b => if isPair a b e then es else e :: eraseOne es a b

/-! ## Connectivity -/

/-- One pass over the bonds: add both ends of every bond that has an end in `R`. -/
def grow : Edges → ℕ → ℕ
  | [], R => R
  | e :: es, R => grow es (if mem e.1 R || mem e.2 R then R ||| bit e.1 ||| bit e.2 else R)

/-- Iterate `grow` (at most `k` passes, stopping at a fixed point). -/
def reach : ℕ → Edges → ℕ → ℕ
  | 0, _, R => R
  | k + 1, es, R => let R' := grow es R; if R'.beq R then R else reach k es R'

/-- The component of `s` in `es` (computed with 16 passes; enough for the instances). -/
def comp (es : Edges) (s : ℕ) : ℕ := reach 16 es (bit s)

/-- `R` is closed: no bond has exactly one end in `R`. -/
def closedB (es : Edges) (R : ℕ) : Bool := es.all fun e => mem e.1 R == mem e.2 R

/-- The vertex set `V` (nonempty) is connected by the bonds `es` (all inside `V`). -/
def connB (V : ℕ) (es : Edges) : Bool :=
  match lowBit V with
  | none => V.beq 0
  | some s => (comp es s).beq V

/-- The components of the vertex set `V` under `es` (fuel `k`). -/
def comps : ℕ → Edges → ℕ → List ℕ
  | 0, _, _ => []
  | k + 1, es, V =>
    match lowBit V with
    | none => []
    | some s => let X := comp es s; X :: comps k es (sdiff V X)

/-! ## Closure and (Y2) reduction -/

/-- The closure `cl(S; j₁, j₂)` of the bond list `es` (all bonds of the block), as a bond list on the other
atoms, if defined (`σ ≤ 1`, both joints of degree 2, no loop). -/
def closure (es : Edges) (j₁ j₂ : ℕ) : Option Edges :=
  let rest := es.filter fun e => !touches j₁ e && !touches j₂ e
  let isJ := fun x : ℕ => x.beq j₁ || x.beq j₂
  match mult es j₁ j₂, nbrs es j₁, nbrs es j₂ with
  | 0, [a, b], [c, d] =>
      if a.beq b || c.beq d || isJ a || isJ b || isJ c || isJ d then none else some (rest ++ [(a, b), (c, d)])
  | 1, n₁, n₂ =>
      match n₁.filter (fun x => !x.beq j₂), n₂.filter (fun x => !x.beq j₁) with
      | [x], [y] => if x.beq y || isJ x || isJ y then none else some (rest ++ [(x, y)])
      | _, _ => none
  | _, _, _ => none

/-- Delete the atoms `a, b` with their bonds and add the bond `{c, d}`. -/
def y2Apply (es : Edges) (a b c d : ℕ) : Edges :=
  (es.filter fun e => !touches a e && !touches b e) ++ [(c, d)]

/-- The (Y2) move at the triple pair `(a, b)`, if it applies: returns `(c, d)`. -/
def y2At (es : Edges) (a b : ℕ) : Option (ℕ × ℕ) :=
  if mult es a b == 3 then
    match (nbrs es a).filter (fun x => !x.beq b), (nbrs es b).filter (fun x => !x.beq a) with
    | [c], [d] =>
      if a.beq b || c.beq d || c.beq a || c.beq b || d.beq a || d.beq b then none else some (c, d)
    | _, _ => none
  else none

/-- Find some (Y2) move: the first bond copy `(a, b)` at which `y2At` applies. -/
def findY2 (es : Edges) : Option (ℕ × ℕ × ℕ × ℕ) :=
  es.findSome? fun e => (y2At es e.1 e.2).map fun cd => (e.1, e.2, cd.1, cd.2)

/-- Greedy (Y2) reduction with fuel: the moves made and the final bond list. -/
def y2Greedy : ℕ → Edges → List (ℕ × ℕ × ℕ × ℕ) × Edges
  | 0, es => ([], es)
  | k + 1, es =>
    match findY2 es with
    | none => ([], es)
    | some m => let r := y2Greedy k (y2Apply es m.1 m.2.1 m.2.2.1 m.2.2.2); (m :: r.1, r.2)

/-- The bond list is a doubled triangle on three distinct atoms. -/
def isDoubledTriangle (es : Edges) : Bool :=
  match es with
  | (a, b) :: _ =>
    match (nbrs es a).filter (fun x => !x.beq b) with
    | c :: _ => es.length == 6 && !a.beq b && !a.beq c && !b.beq c &&
        mult es a b == 2 && mult es b c == 2 && mult es a c == 2
    | [] => false
  | [] => false

/-- The closure is defined and reduces greedily to a doubled triangle. -/
def tvineB (es : Edges) (j₁ j₂ : ℕ) : Bool :=
  multLe2 es &&
  match closure es j₁ j₂ with
  | none => false
  | some cl => loopless cl && isDoubledTriangle (y2Greedy 16 cl).2

/-! ## Two-edge cuts and pieces -/

/-- All ways to remove at most one bond copy: `(removed, kept)`. -/
def splits1 : Edges → List (Edges × Edges)
  | [] => [([], [])]
  | e :: es => (splits1 es).map (fun p => (p.1, e :: p.2)) ++ [([e], es)]

/-- All ways to remove at most two bond copies: `(removed, kept)`. -/
def splits2 : Edges → List (Edges × Edges)
  | [] => [([], [])]
  | e :: es => (splits2 es).map (fun p => (p.1, e :: p.2)) ++ (splits1 es).map (fun p => (e :: p.1, p.2))

/-- The side of the first atom of `V` in the kept bonds `es'`, provided `es'` has at most two components on `V`
and the side is closed (else `none`). -/
def sideOf (V : ℕ) (es' : Edges) : Option ℕ :=
  match lowBit V with
  | none => none
  | some s =>
    let X := comp es' s
    let Y := sdiff V X
    match lowBit Y with
    | none => some X
    | some t => if (comp es' t).beq Y && closedB es' X then some X else none

/-- The sides of all removals of at most two bond copies (`none` if some removal fails `sideOf`). -/
def allSides (V : ℕ) (es : Edges) : Option (List ℕ) :=
  go ((splits2 es).map Prod.snd)
where
  /-- `mapM` by hand (kernel-friendly). -/
  go : List Edges → Option (List ℕ)
    | [] => some []
    | r :: rs => match sideOf V r, go rs with
      | some X, some Xs => some (X :: Xs)
      | _, _ => none

/-- The piece of `u` inside `W`: the atoms of `W` on the same side as `u` in every removal. -/
def pieceOf (sides : List ℕ) (W u : ℕ) : List ℕ :=
  (elems W).filter fun w => sides.all fun X => (mem u X).beq (mem w X)

/-- The core shape with `x = y` doubled (N2 Prop 1.17(b)): (B) `y–z`, `x–z` single; (C) `y = z`, no `x–z`;
(D) `y = z`, `x–z` single. -/
def shapeAt (es : Edges) (x y z : ℕ) : Bool :=
  mult es x y == 2 && ((mult es y z == 1 && mult es x z == 1) || (mult es y z == 2 && mult es x z == 0) ||
    (mult es y z == 2 && mult es x z == 1))

/-- A 3-atom core `{x, y, z}` has one of the shapes (B), (C), (D) in some labelling. -/
def coreShapeOK (es : Edges) (x y z : ℕ) : Bool :=
  shapeAt es x y z || shapeAt es y z x || shapeAt es z x y || shapeAt es x z y || shapeAt es z y x ||
    shapeAt es y x z

/-- One piece is acceptable: a 2-atom piece of internal multiplicity 1 or 2, or a core. -/
def pieceOK (es : Edges) : List ℕ → Bool
  | [x, y] => let m := mult es x y; m == 1 || m == 2
  | [x, y, z] => coreShapeOK es x y z
  | _ => false

/-- **F2** (piece shape) on the block `es` on `V` with joints `j₁, j₂`: every piece of `V ∖ {j₁, j₂}` is a
2-atom piece of multiplicity 1 or 2, or the core, and the core (a 3-atom piece) is unique. -/
def pieceShapeB (V : ℕ) (es : Edges) (j₁ j₂ : ℕ) : Bool :=
  match allSides V es with
  | none => false
  | some sides =>
    let W := sdiff V (bit j₁ ||| bit j₂)
    let ps := (elems W).map (pieceOf sides W)
    match ps.find? (fun p => p.length == 3) with
    | none => false
    | some c => ps.all fun p => pieceOK es p && (p.length != 3 || p == c)

/-- **F3**: the interior `V ∖ {j₁, j₂}` is connected. -/
def interiorConnB (V : ℕ) (es : Edges) (j₁ j₂ : ℕ) : Bool :=
  let W := sdiff V (bit j₁ ||| bit j₂)
  connB W (inside W es)

/-! ## Sub-objects -/

/-- A candidate sub-object: atom set `S`, joints `k₁ < k₂`, whether it is hyper (one adjoint copy of
`{k₁, k₂}` is removed from the core). -/
structure Sub where
  S : ℕ
  k₁ : ℕ
  k₂ : ℕ
  hyper : Bool
  deriving Repr

/-- The core bonds `U°` of a candidate. -/
def Sub.core (U : Sub) (es : Edges) : Edges :=
  if U.hyper then eraseOne (inside U.S es) U.k₁ U.k₂ else inside U.S es

/-- Degree conditions of the core: joints of degree 2, other atoms of degree 4 (connectivity is not tested here,
so that every sub-object is provably enumerated; the facts are checked on all degree-valid candidates). -/
def Sub.valid (U : Sub) (es : Edges) : Bool :=
  let c := U.core es
  (!U.hyper || mult (inside U.S es) U.k₁ U.k₂ != 0) &&
  (elems U.S).all (fun v => if v.beq U.k₁ || v.beq U.k₂ then deg c v == 2 else deg c v == 4)

/-- The union of the components of `cs` selected by the bits of `m`. -/
def selectComps : List ℕ → ℕ → ℕ
  | [], _ => 0
  | X :: cs, m => (if m % 2 == 1 then X else 0) ||| selectComps cs (m / 2)

/-- All valid proper sub-objects of the block `es` on `V`: interiors are unions of components of
`V ∖ {k₁, k₂}`. -/
def subObjects (V : ℕ) (es : Edges) : List Sub :=
  (elems V).flatMap fun k₁ => ((elems V).filter (k₁ < ·)).flatMap fun k₂ =>
    let W := sdiff V (bit k₁ ||| bit k₂)
    let cs := comps 16 (inside W es) W
    (List.range (2 ^ cs.length)).flatMap fun m =>
      let S := bit k₁ ||| bit k₂ ||| selectComps cs m
      if S.beq V then [] else
        ([false, true].map fun h => (⟨S, k₁, k₂, h⟩ : Sub)).filter fun U => U.valid es

/-- The type of a valid candidate is I, VC:I+I or T. -/
def Sub.typeOK (U : Sub) (es : Edges) : Bool :=
  let c := U.core es
  match elems U.S with
  | [_, _] => !U.hyper && mult c U.k₁ U.k₂ == 2
  | [x, y, z] =>
    let mid := if x.beq U.k₁ || x.beq U.k₂ then (if y.beq U.k₁ || y.beq U.k₂ then z else y) else x
    mult c U.k₁ mid == 2 && mult c mid U.k₂ == 2
  | _ => tvineB c U.k₁ U.k₂ && tvineB c U.k₂ U.k₁

/-- Removing the two core bonds at the joint `k` leaves the whole block connected (gap freeness). -/
def Sub.gapFreeAt (U : Sub) (V : ℕ) (es : Edges) (k : ℕ) : Bool :=
  match nbrs (U.core es) k with
  | [x, y] => connB V (eraseOne (eraseOne es k x) k y)
  | _ => false

/-- Remove a family of sub-objects (note semantics): delete their interiors and every bond inside their
atom sets. -/
def removeAll (V : ℕ) (es : Edges) (Us : List Sub) : ℕ × Edges :=
  let I := Us.foldl (fun acc U => acc ||| sdiff U.S (bit U.k₁ ||| bit U.k₂)) 0
  (sdiff V I, es.filter fun e => Us.all fun U => !(mem e.1 U.S && mem e.2 U.S))

/-- **F4** for one sub-object: allowed type, gap free at both joints, and connected after removal. -/
def Sub.checkB (U : Sub) (V : ℕ) (es : Edges) : Bool :=
  U.typeOK es && U.gapFreeAt V es U.k₁ && U.gapFreeAt V es U.k₂ &&
  let r := removeAll V es [U]; connB r.1 r.2

/-- All families (as lists) of pairwise atom-disjoint members of `Us`, with their union. -/
def families : List Sub → List (List Sub)
  | [] => [[]]
  | U :: Us =>
    let rest := families Us
    rest ++ (rest.filter fun F => F.all fun W => (U.S &&& W.S).beq 0).map (U :: ·)

/-- **F5**: every family of at least two pairwise disjoint sub-objects leaves the block connected. -/
def familiesB (V : ℕ) (es : Edges) (Us : List Sub) : Bool :=
  (families Us).all fun F => F.length < 2 || let r := removeAll V es F; connB r.1 r.2

/-- The masks of `cs` are pairwise disjoint. -/
def pairwiseDisj : List ℕ → Bool
  | [] => true
  | X :: cs => cs.all (fun Y => (X &&& Y).beq 0) && pairwiseDisj cs

/-- The component lists used by `subObjects` partition `V ∖ {k₁, k₂}`. -/
def compsOKAll (V : ℕ) (es : Edges) : Bool :=
  (elems V).all fun k₁ => ((elems V).filter (k₁ < ·)).all fun k₂ =>
    let W := sdiff V (bit k₁ ||| bit k₂)
    let cs := comps 16 (inside W es) W
    (cs.foldr (· ||| ·) 0).beq W && pairwiseDisj cs

/-- All the sub-object facts on one instance. -/
def subFactsB (V : ℕ) (es : Edges) : Bool :=
  let Us := subObjects V es
  compsOKAll V es && Us.all (fun U => U.checkB V es) && familiesB V es Us

end WaveTurbulence.TVine.Checker
