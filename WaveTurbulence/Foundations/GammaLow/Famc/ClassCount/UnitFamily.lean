/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.ClassCount.UnitFamily` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Stage1.ClassCount.WList
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitFamily


/-!
# CLASSCOUNT: decoding unit codes into arc lists, and the family of unit arc functions

`unitArcs cs` is the arc list of the vine Fama.chain with ingredient codes `cs` on the labels `0 … W` (`W` = weight):
the Fama.chain joints `J_0 … J_m` are the labels `0 … m`, the interior atoms of ingredient `i` follow in order.
`allArcs` places a list of units in the global labelling: the representative atom of unit `u` (at its canonical
position `ρ_u`) keeps the global label `p_u`, the other atoms of the units take the labels `n_sb, n_sb + 1, …`
in order.  `unitFamily n nsb r E` is the finite set of all resulting arc count functions, for at most `r` units with
total weight `E`; its size is at most `(2^44)^E n^r` (`card_unitFamily_le`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence Finset WaveTurbulence.GammaLow.FinalCount

/-- The label of the expanded template atom `t` of an ingredient of size `sz` whose first joint has label `p`:
the Fama.chain is laid out as `J_0, int_0, J_1, int_1, …, J_m` so that appending an ingredient does not move the
labels of the earlier ones (the first joint has label `p`, the second `p + sz - 1`, interior atom `t` has `p + t - 1`). -/
def unitArcsAux : ℕ → List IngCodeG → List (ℕ × ℕ)
  | _, [] => []
  | p, c :: cs => ingArcsG c (ingPosOf p c.size c.swap) ++ unitArcsAux (p + c.size - 1) cs

/-- The arc list of the vine Fama.chain with ingredient codes `cs` (labels `0 … unitWeight cs`). -/
def unitArcs (cs : List IngCodeG) : List (ℕ × ℕ) := unitArcsAux 0 cs

/-- A unit: ingredient codes and the canonical position `ρ` of the representative atom. -/
structure UnitData where
  cs : List IngCodeG
  ρ : ℕ
deriving DecidableEq

/-- Weight of a unit (`#atoms - 1`). -/
def UnitData.W (u : UnitData) : ℕ := unitWeight u.cs

/-- Global label of the canonical position `j`: the representative keeps `p`, the others are shifted to `base`. -/
def globArcs (u : UnitData) (p base : ℕ) : List (ℕ × ℕ) :=
  (unitArcs u.cs).map (fun a => (glob u.ρ p base a.1, glob u.ρ p base a.2))

/-- Arc list of a list of units: unit `idx` has representative label `p idx`, interior labels from `base`. -/
def allArcs (p : ℕ → ℕ) : ℕ → ℕ → List UnitData → List (ℕ × ℕ)
  | _, _, [] => []
  | idx, base, u :: us => globArcs u (p idx) base ++ allArcs p (idx + 1) (base + u.W) us

/-- Unit data of weight `W`. -/
noncomputable def unitDataAt (W : ℕ) : Finset UnitData :=
  ((unitCodes W) ×ˢ (Finset.range (W + 1))).image (fun q => ⟨q.1, q.2⟩)

theorem card_unitDataAt_le (W : ℕ) (hW : 1 ≤ W) : (unitDataAt W).card ≤ (2 ^ 104) ^ W := by
  unfold unitDataAt
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Finset.card_range]
  have h1 := card_unitCodes_le W
  have h2 : W + 1 ≤ 2 ^ W := Nat.lt_two_pow_self
  calc (unitCodes W).card * (W + 1) ≤ (2 ^ 103) ^ W * 2 ^ W := Nat.mul_le_mul h1 h2
    _ = (2 ^ 104) ^ W := by rw [← mul_pow]; norm_num

/-- The lists of units of total weight `E`. -/
noncomputable def unitLists (E : ℕ) : Finset (List UnitData) := wlists unitDataAt E

theorem card_unitLists_le (E : ℕ) : (unitLists E).card ≤ (2 ^ 105) ^ E := by
  have := card_wlists_le unitDataAt (2 ^ 104) (fun w hw => card_unitDataAt_le w hw) E
  simpa [unitLists, pow_succ, ← mul_assoc, show (2 : ℕ) * 2 ^ 104 = 2 ^ 105 by norm_num] using this

/-- The unit arc count functions on `Fin n` for at most `r` units of total weight `E` with interior labels from `nsb`. -/
noncomputable def unitFamily (n nsb r E : ℕ) : Finset (Fin n × Fin n → ℕ) :=
  ((unitLists E) ×ˢ (Finset.univ : Finset (Fin r → Fin n))).image
    (fun t x => (allArcs (fun i => if h : i < r then ((t.2 ⟨i, h⟩ : Fin n) : ℕ) else 0) 0 nsb t.1).count
      (x.1.1, x.2.1))

theorem card_unitFamily_le (n nsb r E : ℕ) : (unitFamily n nsb r E).card ≤ (2 ^ 105) ^ E * n ^ r := by
  unfold unitFamily
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  exact Nat.mul_le_mul (card_unitLists_le E) le_rfl

theorem mem_unitFamily {n nsb r E : ℕ} {us : List UnitData} (hus : us ∈ unitLists E) (p : Fin r → Fin n) :
    (fun x : Fin n × Fin n => (allArcs (fun i => if h : i < r then ((p ⟨i, h⟩ : Fin n) : ℕ) else 0) 0 nsb us).count
      (x.1.1, x.2.1)) ∈ unitFamily n nsb r E := by
  unfold unitFamily
  exact Finset.mem_image.mpr ⟨(us, p), Finset.mem_product.mpr ⟨hus, Finset.mem_univ _⟩, rfl⟩

end WaveTurbulence.GammaLow.Famc.ClassCount
