/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.KCont
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.GateH

/-! # P4-W2 (session 8, R-SUPPLY, R95): the exact kernels are time-constant beyond the top layer

`kDomain_congr_up`, `kernelK_up_congr`: the time domain of `kernelK` depends on the upper times `up` only through `τ b < up b`, which is vacuous when
`up b ≥ layer b + 1`.  `KQstar_const_above`, `KTstar_const_above`: hence `K*_𝒬(t, s, k)` (`K*_𝒯`) is constant in `t ≥ q + 1` when every `+`-tree node of the
carrier lies in a layer `≤ q`.  `coherentCouple_layer_le_q`: every node of a coherent couple at `(q, q')` lies in a layer `≤ q` (the `high` facts of
`cohFacts_of_coherent` with `q` in place of `p`). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.PL234 TTree WaveTurbulence.Reg WaveTurbulence.Links

theorem kDomain_congr_up {w : ℕ} (LG : LayeredGarden w) (up up' : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (h : ∀ b, ((LG.layer b.toNode : ℝ) + 1 ≤ up b ∧ (LG.layer b.toNode : ℝ) + 1 ≤ up' b) ∨ up b = up' b) :
    kDomain LG up s = kDomain LG up' s := by
  ext τ
  simp only [kDomain, Set.mem_ofPred_eq]
  refine forall_congr' fun b => ?_
  rcases h b with ⟨h1, h2⟩ | h
  · constructor
    · rintro ⟨a1, a2, a3, a4, a5, a6⟩
      exact ⟨a1, a2, a3, lt_of_lt_of_le a2 h2, a5, a6⟩
    · rintro ⟨a1, a2, a3, a4, a5, a6⟩
      exact ⟨a1, a2, a3, lt_of_lt_of_le a2 h1, a5, a6⟩
  · rw [h]

theorem kernelK_up_congr {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (up up' : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (h : ∀ b, ((LG.layer b.toNode : ℝ) + 1 ≤ up b ∧ (LG.layer b.toNode : ℝ) + 1 ≤ up' b) ∨ up b = up' b) :
    kernelK L γ δ F LG up s k₀ nroot nfl = kernelK L γ δ F LG up' s k₀ nroot nfl := by
  unfold kernelK
  rw [kDomain_congr_up LG up up' s h]

/-- The couple kernel is constant in `t` beyond the top layer of the `+` tree. -/
theorem KQstar_const_above {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) {q : ℕ}
    (hlay : ∀ b : GBranch LG.garden.tree, b.1.1 = 0 → LG.layer b.toNode ≤ q) {t t' : ℝ}
    (ht : (q : ℝ) + 1 ≤ t) (ht' : (q : ℝ) + 1 ≤ t') (s : ℝ) (k : Mom d) :
    KQstar L γ δ F LG t s k = KQstar L γ δ F LG t' s k := by
  unfold KQstar
  refine kernelK_up_congr L γ δ F LG _ _ 0 k _ 0 fun b => ?_
  by_cases hb : b.1.1 = 0
  · left
    have := hlay b hb
    simp only [hb, ite_true]
    constructor <;> linarith [(show ((LG.layer b.toNode : ℕ) : ℝ) ≤ q from by exact_mod_cast this)]
  · right; simp [hb]

theorem KTstar_const_above {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1) {q : ℕ}
    (hlay : ∀ b : GBranch LG.garden.tree, LG.layer b.toNode ≤ q) {t t' : ℝ}
    (ht : (q : ℝ) + 1 ≤ t) (ht' : (q : ℝ) + 1 ≤ t') (s : ℝ) (k : Mom d) :
    KTstar L γ δ F LG t s k = KTstar L γ δ F LG t' s k := by
  unfold KTstar
  refine kernelK_up_congr L γ δ F LG _ _ s k _ 0 fun b => ?_
  left
  have := hlay b
  constructor <;> linarith [(show ((LG.layer b.toNode : ℕ) : ℝ) ≤ q from by exact_mod_cast this)]


theorem cohHigh_le_q {p q q' : ℕ} {Xp Xm : RegChain} {Qlp : RegCpl} {LG : LayeredGarden 2}
    (hqq : q' ≤ q) (h : IsCoherentCoupleAt p q q' (.type2 Xp Xm Qlp) LG) :
    ∀ z ∈ chainNodesSet Xp 1 ((0 : Fin 2), []), layerAt LG z ≤ q := by
  obtain ⟨hwf, hQ, w, HH, a, b, hcan, hE, -, -, hcoh, hpa, hpb, hlay⟩ := h
  obtain ⟨hL, hPLp, -, hXp, hXm⟩ := layerreg1_type2 hcan.2.2 hcan.1 hwf hE hcoh
  have hmin : min (parAt HH p a) (parAt HH p b) = q' := by rw [hpa, hpb]; exact min_eq_right hqq
  rw [hmin] at hXp
  rw [hpa] at hXp
  have hf := rootEmb_hom a b
  have hlf := layerAt_rootEmb hQ hE hlay
  obtain ⟨Cp, -, -⟩ := hE.type2
  have hmapX : chainNodesSet Xp 1 a = (chainNodesSet Xp 1 ((0 : Fin 2), [])).image (rootEmb a b) := by
    have := chainNodesSet_map Xp (rootEmb a b) hf 1 ((0 : Fin 2), [])
    rwa [rootEmb_zero] at this
  intro z hz
  rw [hlf]
  have hz' : rootEmb a b z ∈ chainNodesSet Xp 1 a := by
    rw [hmapX]
    exact Finset.mem_image_of_mem _ hz
  exact (hXp _ hz').2

/-- Every node of a coherent couple carrier lies in a layer `≤ q`. -/
theorem coherentCouple_layer_le_q {p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2} (hqq : q' ≤ q) (hqp : q ≤ p)
    (hcoh : IsCoherentCoupleAt p q q' Q LG) (z : GNode LG.garden.tree) : LG.layer z ≤ q := by
  have hQ := hcoh.2.1
  cases Q with
  | triv => rw [layers_type1 hqq hcoh rfl z]; exact hqq
  | type1 c Q₁ Q₂ Q₃ => rw [layers_type1 hqq hcoh rfl z]; exact hqq
  | type2 Xp Xm Qlp =>
    have F := cohFacts_of_coherent (p := p) hqq hqp hcoh
    have FH := cohHigh_le_q hqq hcoh
    rw [← layerAt_node]
    have ha := addrExt_mem_cplNodes hQ ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) z
    have hae : addrExt (if z.1.1 = 0 then ((0 : Fin 2), ([] : Path)) else ((1 : Fin 2), ([] : Path))) z.1.2 =
        z.1 := by
      obtain ⟨⟨j, q⟩, _⟩ := z
      fin_cases j <;> simp [addrExt]
    rw [hae] at ha
    rcases mem_cplNodes_type2.mp ha with h | h | h
    · exact FH _ h
    · rw [F.minus _ h]; exact hqq
    · rw [F.lp _ h]; exact hqq

end WaveTurbulence.VineEstS5C.P4.W2
