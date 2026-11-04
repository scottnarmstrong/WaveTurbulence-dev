/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.MiniCplCode
public import WaveTurbulence.Frozen.Defs.MiniTreeCode
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# RegCpl, RegChain (mutual)

Wave B tier B2 (WaveB2-Regular.lean): one `mutual` block, frozen as one file because Lean cannot
split it; each declaration keeps its own manifest entry. Sources:
- `RegCpl`: T Prop `propstructure`; WAVE-B §2.7
- `RegChain`: T Def `defregchain`; T L855

Frozen by ruling D8 (`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

mutual
/-- **Codes of regular couples** (the structure data of T Prop `propstructure`, recommended form of
WAVE-B §2.7 item 3): trivial; type 1 = a mini-couple of code `c` whose red, green, blue leaf pairs
are replaced by `Q₁, Q₂, Q₃`; type 2 = two regular chains `𝒳⁺`, `𝒳⁻` (with their couples) whose lone
leaves are paired and replaced by `Q_lp`. Well-formedness (`RegCpl.WF`) adds the uniqueness side
conditions of `propstructure` (b): `Q_lp` is trivial or of type 1 and `𝒬₀` is nontrivial. -/
inductive RegCpl : Type
  | triv : RegCpl
  | type1 (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl) : RegCpl
  | type2 (Xp Xm : RegChain) (Qlp : RegCpl) : RegCpl

/-- **Codes of regular chains with their couples** (T Def `defregchain`, `propstructure`): a legal
(non-crossing) partition of `{1,…,2m}` in Catalan form. `pair m Qr Qg inner rest` pairs the first chain
node `𝔫_a` with `𝔫_b`, where `inner` codes the chain nodes strictly between them and `rest` those after
`𝔫_b`; `m` is the mini-tree code of the rearrangement of `𝔫_a, 𝔫_b` (`m.c` = the slot of `𝔫_{a+1}` under
`𝔫_a`, `m.lone` = the slot of `𝔫_{b+1}` or of the lone leaf under `𝔫_b`), and its red and green leaf
pairs are replaced by `Qr = 𝒬_{j,ε,1}`, `Qg = 𝒬_{j,ε,2}`. Pairs are listed in increasing `a` (preorder),
as in T L855. -/
inductive RegChain : Type
  | nil : RegChain
  | pair (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) : RegChain
end

end WaveTurbulence
