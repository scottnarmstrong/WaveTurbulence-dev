/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.StarGate
public import WaveTurbulence.Foundations.Flower.IncTop.TopWeight

/-! # INC-TOP: Lemma 4.1 with per-arm frontier weights, in the form the weighted Stage-1 gate consumes

**Export.** `topIncoherentDecayGateR : Stage1W.TopIncoherentDecayGateR` — STAGE1W's input statement (S-STAGE1W SCOPE
§1.6, verbatim in `Flower/Stage1W/Inputs.lean`): main's leafwise B2.2 gate `LeafwiseIncoherentDecayGate` for the
kernels carrying the per-arm top weight `rowTopWeightR p g LG ![q, q']` (couples: one weight `g i` per arm, F1) and
`rowTopWeight p (g 0) LG ![q]` (trees), each `g i` `GPresented (32d)` with constant `cψ ≥ 1`, at the cost
`cψ ^ (4n+2)` (couples) / `cψ ^ (4n+1)` (trees).  No realness premise is needed (F2: real weights are a special
case; the statement is proved for complex `g`).

**Proof.** `topIncoherentDecayAtR_of_star`: the per-arm top weight is the star weight on the top set
(`rowTopWeightR_eq_starWeight`), each `g i` gives a star presentation of order `30d` (`topStar_presented`), the
top set is an antichain with at most `2·order + w` nodes (`card_topSet_le`), and `order = 2n`; then
`starIncoherentDecay` (the star-weighted gate) applies at every record.

Source: supplement Lemma 4.1 (/home/scott/wt-scratch/flower-open/SUPPLEMENT-v1.md L171–189) with the referee's fix
for trees (ref/REFEREE.md L42–50: T1062–T1092); `h ≤ #leaves` inserted factors, `C_χ^{h+1}` paid by `cψ^{h}` and the
`d`-only constant `rootJetConstant (30d)` (absorbed in `C₁`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal Classical
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.IncohInst WaveTurbulence.Incoh WaveTurbulence.Links WaveTurbulence.LGSpine

/-- `WTPrefix` is monotone in its record predicate. -/
theorem wtPrefix_imp {Q Q' : WTParams → Prop} (h : WTPrefix Q) (hQ : ∀ P, Q P → Q' P) : WTPrefix Q' := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => hQ _ (H L hL)⟩

/-- The per-arm top-weighted couple kernel is the star-weighted kernel on the top set. -/
theorem coupleLeavesTopR_eq_star {d : ℕ} (L γ δ : ℝ) (p : ℕ) (g : Fin 2 → Mom d → ℂ) (q q' : ℕ)
    (LG : LayeredGarden 2) (H : LeafProfiles 2 d) (t s : ℝ) (k : Mom d) :
    Stage1W.coupleLeavesTopR L γ δ p g q q' LG H t s k =
      coupleLeavesStar L γ δ LG (topSet p LG ![q, q']) (topStar g) H t s k := by
  unfold Stage1W.coupleLeavesTopR coupleLeavesStar
  rw [show Stage1W.rowTopWeightR p g LG ![q, q'] = starWeight (topSet p LG ![q, q']) (topStar g) from
    funext (rowTopWeightR_eq_starWeight p g LG ![q, q'])]

/-- The top-weighted tree kernel is the star-weighted kernel on the top set. -/
theorem treeLeavesTop_eq_star {d : ℕ} (L γ δ : ℝ) (p : ℕ) (g : Mom d → ℂ) (q : ℕ)
    (LG : LayeredGarden 1) (H : LeafProfiles 1 d) (t s : ℝ) (k : Mom d) :
    Stage1W.treeLeavesTop L γ δ p g q LG H t s k =
      treeLeavesStar L γ δ LG (topSet p LG ![q]) (topStar (fun _ => g)) H t s k := by
  unfold Stage1W.treeLeavesTop treeLeavesStar
  rw [show Stage1W.rowTopWeight p g LG ![q] = starWeight (topSet p LG ![q]) (topStar (fun _ => g)) from
    funext fun κ => (Stage1W.rowTopWeightR_const p g LG ![q] κ).symm.trans
      (rowTopWeightR_eq_starWeight p (fun _ => g) LG ![q] κ)]

/-- **Per record**: the star-weighted gate body gives STAGE1W's per-arm top-weighted gate body. -/
theorem topIncoherentDecayAtR_of_star (P : WTParams) (h : StarIncoherentDecayAt P) :
    Stage1W.TopIncoherentDecayAtR P := by
  intro p hp n hn g cψ hcψ hg
  obtain ⟨hc, ht⟩ := h p hp n hn
  constructor
  · intro Q hwf hs LG hQ hlay q q' hq hq' hr hr' hgi H B hctrl
    have hk := hc Q hwf hs LG hQ hlay q q' hq hq' hr hr' hgi (topSet p LG ![q, q']) (topStar g)
      (fun _ => cψ) (fun a _ => topStar_presented g hg a) H B hctrl
    have heq : (fun (ts : Fin 2 → ℝ) (k : Mom P.d) =>
        Stage1W.coupleLeavesTopR P.L P.γ P.δ p g q q' LG H (ts 0) (ts 1) k) =
        fun (ts : Fin 2 → ℝ) (k : Mom P.d) => coupleLeavesStar P.L P.γ P.δ LG (topSet p LG ![q, q']) (topStar g) H (ts 0) (ts 1) k := by
      funext ts k
      exact coupleLeavesTopR_eq_star P.L P.γ P.δ p g q q' LG H (ts 0) (ts 1) k
    rw [heq]
    refine hk.trans ?_
    have hord : 2 * LG.garden.order + 2 ≤ 4 * n + 2 := by
      have h1 := couple_order_eq_twice_links hQ
      have h2 := couple_linksAt_length Q ((0 : Fin 2), []) (1, [])
      change Q.links.length * 2 = Q.size at h2
      omega
    exact mul_le_mul_left (mul_le_mul_left (prod_topSet_cost_le p LG ![q, q'] hcψ hord) _) _
  · intro X hwf hs LG hX hlay q q' hq'q hq hr hlone hgi H B hctrl
    have hk := ht X hwf hs LG hX hlay q q' hq'q hq hr hlone hgi (topSet p LG ![q]) (topStar (fun _ => g 0))
      (fun _ => cψ) (fun a _ => topStar_presented (fun _ => g 0) (fun _ => hg 0) a) H B hctrl
    have heq : (fun (ts : Fin 2 → ℝ) (k : Mom P.d) =>
        Stage1W.treeLeavesTop P.L P.γ P.δ p (g 0) q LG H (ts 0) (ts 1) k) =
        fun (ts : Fin 2 → ℝ) (k : Mom P.d) => treeLeavesStar P.L P.γ P.δ LG (topSet p LG ![q]) (topStar (fun _ => g 0)) H
          (ts 0) (ts 1) k := by
      funext ts k
      exact treeLeavesTop_eq_star P.L P.γ P.δ p (g 0) q LG H (ts 0) (ts 1) k
    rw [heq]
    refine hk.trans ?_
    have hord : 2 * LG.garden.order + 1 ≤ 4 * n + 1 := by
      have h1 := tree_order_eq_twice_links hX
      have h2 := chain_linksAt_length X (LG.garden.sig 0) ((0 : Fin 1), [])
      change (X.treeLinks (LG.garden.sig 0)).length * 2 = X.size at h2
      omega
    exact mul_le_mul_left (mul_le_mul_left (prod_topSet_cost_le p LG ![q] hcψ hord) _) _

/-- **INC-TOP export: supplement Lemma 4.1 with per-arm frontier weights** — STAGE1W's
`TopIncoherentDecayGateR`. -/
theorem topIncoherentDecayGateR : Stage1W.TopIncoherentDecayGateR :=
  wtPrefix_imp starIncoherentDecay topIncoherentDecayAtR_of_star

end WaveTurbulence.Flower.IncTop
