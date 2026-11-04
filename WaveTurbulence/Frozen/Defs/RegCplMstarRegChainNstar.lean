/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.AddrExt
public import WaveTurbulence.Frozen.Defs.MiniCplCode
public import WaveTurbulence.Frozen.Defs.MiniCplCodePartner
public import WaveTurbulence.Frozen.Defs.MiniTreeCode
public import WaveTurbulence.Frozen.Defs.MiniTreeCodeGreen
public import WaveTurbulence.Frozen.Defs.MiniTreeCodeLone
public import WaveTurbulence.Frozen.Defs.MiniTreeCodeRed
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.PvResonantIntegral
public import WaveTurbulence.Frozen.Defs.RegChainLonePath
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.ResIntegral
public import WaveTurbulence.Frozen.Defs.SlotSign
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# RegCpl.Mstar, RegChain.Nstar (mutual)

Wave B tier B2 (WaveB2-Regular.lean): one `mutual` block, frozen as one file because Lean cannot
split it; each declaration keeps its own manifest entry. Sources:
- `RegCpl.Mstar`: T Prop `regref3`
- `RegChain.Nstar`: T (regref3-2); T (regref3-4)

Frozen by ruling D8 (`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

mutual
/-- **`ℳ*_{(𝒬,Z)}(k)[F]`** for a dominant couple code placed with its `+` tree at `a` and `-` tree at
`b` (T Prop `regref3`): trivial `F(k)`; type 1 (regref3-0) the resonant integral of
`∏_j ℳ*_{𝒬_j}(k_j)`; type 2 (regref3-1) `ℳ*_{𝒬_lp}(k) ∏_{ε,j} 𝒩*_{(j,ε)}(k)`. `Z` is a set of node
addresses (the special subset). -/
noncomputable def RegCpl.Mstar {d w : ℕ} (F : Mom d → ℝ) (Z : Finset (Fin w × Path)) :
    RegCpl → (Fin w × Path) → (Fin w × Path) → Mom d → ℝ
  | .triv, _, _ => F
  | .type1 c Q₁ Q₂ Q₃, a, b => fun k => resIntegral (fun k₁ k₂ k₃ =>
      Q₁.Mstar F Z (addrExt a [0]) (addrExt b [c.partner 0]) k₁ *
        Q₂.Mstar F Z (addrExt b [1]) (addrExt a [1]) k₂ *
        Q₃.Mstar F Z (addrExt a [2]) (addrExt b [c.partner 2]) k₃) k
  | .type2 Xp Xm Qlp, a, b => fun k =>
      Qlp.Mstar F Z (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) k *
        Xp.Nstar F Z 1 a k * Xm.Nstar F Z (-1) b k

/-- **`∏_j 𝒩*_{(j,ε)}(k)`** along a chain rooted at `a` with root sign `ζ` (T (regref3-2)–(regref3-4)):
`𝒩*_{(j,ε)}(k) = ∫ δ(k₁-k₂+k₃-k)·(Factor 1)·(Factor 2)`, Factor 1 `= δ(Ω)` if `𝔫_a ∉ Z` (`𝙸 = 0`) and
`p.v. 1/Ω` if `𝔫_a ∈ Z` (`𝙸 = 1`); Factor 2 `= ℳ*_{𝒳_{j,1}}(k_x) ℳ*_{𝒳_{j,2}}(k_y)` with `x < y` the
positions of the two leaf children of `𝔫_a` in the rearranged mini-tree (red at `x`, green at `y`):
`(k₂, k₃)`, `(k₁, k₃)`, `(k₁, k₂)` for `𝚌 = 1, 2, 3` (T (regref3-4)). -/
noncomputable def RegChain.Nstar {d w : ℕ} (F : Mom d → ℝ) (Z : Finset (Fin w × Path)) :
    RegChain → ℤˣ → (Fin w × Path) → Mom d → ℝ
  | .nil, _, _ => fun _ => 1
  | .pair m Qr Qg inner rest, ζ, a => fun k =>
    let Mr : Mom d → ℝ := if slotSign ζ m.red.1 = 1 then
        Qr.Mstar F Z (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Qr.Mstar F Z (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])
    let Mg : Mom d → ℝ := if slotSign ζ m.green.1 = 1 then
        Qg.Mstar F Z (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Qg.Mstar F Z (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])
    let Ψ : Mom d → Mom d → Mom d → ℝ := fun k₁ k₂ k₃ =>
      Mr (![k₁, k₂, k₃] m.red.1) * Mg (![k₁, k₂, k₃] m.green.1)
    (if a ∈ Z then pvResonantIntegral Ψ k else resIntegral Ψ k) *
      inner.Nstar F Z (slotSign ζ m.c) (addrExt a [m.c]) k *
      rest.Nstar F Z (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) k
end

end WaveTurbulence
