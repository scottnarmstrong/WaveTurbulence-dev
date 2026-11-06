/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseKernel
public import WaveTurbulence.Foundations.Spine.ExplicitCoherentApps
/-! Leafwise B2 momentum factors: the same source recursions with a separate profile at each actual positive leaf. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.LeafApp
open Finset TTree
mutual
/-- **`ℳ*_{(𝒬,Z)}(k)[F]`** for a dominant couple code placed with its `+` tree at `a` and `-` tree at
`b` (T Prop `regref3`): trivial `F(k)`; type 1 (regref3-0) the resonant integral of
`∏_j ℳ*_{𝒬_j}(k_j)`; type 2 (regref3-1) `ℳ*_{𝒬_lp}(k) ∏_{ε,j} 𝒩*_{(j,ε)}(k)`. `Z` is a set of node
addresses (the special subset). -/
noncomputable def cplMstar {d w : ℕ} (H : LeafProfiles w d) (Z : Finset (Fin w × Path)) :
    RegCpl → (Fin w × Path) → (Fin w × Path) → Mom d → ℝ
  | .triv, a, _ => H a
  | .type1 c Q₁ Q₂ Q₃, a, b => fun k => resIntegral (fun k₁ k₂ k₃ =>
      cplMstar H Z Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) k₁ *
        cplMstar H Z Q₂ (addrExt b [1]) (addrExt a [1]) k₂ *
        cplMstar H Z Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) k₃) k
  | .type2 Xp Xm Qlp, a, b => fun k =>
      cplMstar H Z Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) k *
        chainNstar H Z Xp 1 a k * chainNstar H Z Xm (-1) b k

/-- **`∏_j 𝒩*_{(j,ε)}(k)`** along a chain rooted at `a` with root sign `ζ` (T (regref3-2)–(regref3-4)):
`𝒩*_{(j,ε)}(k) = ∫ δ(k₁-k₂+k₃-k)·(Factor 1)·(Factor 2)`, Factor 1 `= δ(Ω)` if `𝔫_a ∉ Z` (`𝙸 = 0`) and
`p.v. 1/Ω` if `𝔫_a ∈ Z` (`𝙸 = 1`); Factor 2 `= ℳ*_{𝒳_{j,1}}(k_x) ℳ*_{𝒳_{j,2}}(k_y)` with `x < y` the
positions of the two leaf children of `𝔫_a` in the rearranged mini-tree (red at `x`, green at `y`):
`(k₂, k₃)`, `(k₁, k₃)`, `(k₁, k₂)` for `𝚌 = 1, 2, 3` (T (regref3-4)). -/
noncomputable def chainNstar {d w : ℕ} (H : LeafProfiles w d) (Z : Finset (Fin w × Path)) :
    RegChain → ℤˣ → (Fin w × Path) → Mom d → ℝ
  | .nil, _, _ => fun _ => 1
  | .pair m Qr Qg inner rest, ζ, a => fun k =>
    let Mr : Mom d → ℝ := if slotSign ζ m.red.1 = 1 then
        cplMstar H Z Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else cplMstar H Z Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])
    let Mg : Mom d → ℝ := if slotSign ζ m.green.1 = 1 then
        cplMstar H Z Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else cplMstar H Z Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])
    let Ψ : Mom d → Mom d → Mom d → ℝ := fun k₁ k₂ k₃ =>
      Mr (![k₁, k₂, k₃] m.red.1) * Mg (![k₁, k₂, k₃] m.green.1)
    (if a ∈ Z then pvResonantIntegral Ψ k else resIntegral Ψ k) *
      chainNstar H Z inner (slotSign ζ m.c) (addrExt a [m.c]) k *
      chainNstar H Z rest (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) k
end

noncomputable def couple {d : ℕ} (δ r : ℝ) (H : LeafProfiles 2 d) (Q : RegCpl)
    (t s : ℝ) (k : Mom d) : ℂ :=
  if Q.dominant then
    ((2 : ℂ)⁻¹ ^ Q.size * (δ : ℂ) ^ (Q.size / 2) *
      zetaOfTrees ![1, -1] ![Q.trees.1, Q.trees.2]) *
      ∑ Z ∈ specialSets Q.links, specialWeight ![1, -1] Z * (Q.JB r t s : ℂ) *
        (cplMstar H Z Q (0, []) (1, []) k : ℂ)
  else 0

noncomputable def tree {d : ℕ} (δ r : ℝ) (H : LeafProfiles 1 d) (X : RegChain) (ζ : ℤˣ)
    (t s : ℝ) (k : Mom d) : ℂ :=
  if X.dominant then
    ((2 : ℂ)⁻¹ ^ X.size * (δ : ℂ) ^ (X.size / 2) * zetaOfTrees ![ζ] ![X.plug ζ .leaf]) *
      ∑ Z ∈ specialSets (X.treeLinks ζ), specialWeight ![ζ] Z * (X.JBtree r t s : ℂ) *
        (chainNstar H Z X ζ (0, []) k : ℂ)
  else 0

end WaveTurbulence.LGSpine.LeafApp
