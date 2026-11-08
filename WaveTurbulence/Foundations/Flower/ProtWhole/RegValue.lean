/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtWhole.RegWeight

/-! # D6b: the value of a wholly regular component is a protected kernel

`CapG.compValue_capG`: for a cap couple (`CapG`, `J = {c}`) with the D2b geometry (`CapGeo`, `StemChain`), the
component value of `MarkedComponentBoundAtI` is

`C · selConst · [roots c = roots j0] · kernelProt T1 H1 mult (fun _ => t) 0 (objCfg.fix X s t t) (latticePoint L (roots j0)) 0 0`

with `‖C‖ ≤ 1` (the selection indicator `selOK` and the constant removed phase), `mult` in the exact multiplier
shape of D3/D6a (star weights × two filter layers × dagger), `H1` the relocated pair-type profiles. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open scoped Classical

namespace WaveTurbulence.Flower.ProtWhole

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtGeo
open WaveTurbulence.Flower.MkDefs

namespace CapG

variable {LG : LayeredGarden 2} {j0 c : Fin 2} {X : RegChain} {ζ : ℤˣ} (D : CapG LG j0 c X ζ)
include D

variable {d : ℕ}

/-- The protected multiplier of a wholly regular component, on the paired tree. -/
def mult (p : ℕ) (L : ℝ) (Rf : Fin 2 → Option ℝ) (σ : Fin 2 → Option ℕ) (Rs : Fin 2 → ℝ)
    (kSel : Fin 2 → Option ℕ) (dag : Option (Fin 2 → Fin 3 → Mom d)) (K : GNode D.T1.garden.tree → Mom d) : ℂ :=
  IncTop.starWeight (D.frontS p) (IncTop.topStar (fun _ => Stage1W.frontierG (Rf j0))) K *
    filtWeight (D.selF kSel ∪ objSelT (J := ({c} : Finset (Fin 2))) D.emb kSel)
      (fun b => decide (b ∈ objSelT (J := ({c} : Finset (Fin 2))) D.emb kSel))
      (fun b => if b ∈ objSelT (J := ({c} : Finset (Fin 2))) D.emb kSel then Rs j0 else Rs j0) K *
    filtWeight (D.stemF σ) (fun _ => false) (fun _ => regStemScale j0 σ L) K * (D.ind1 dag K : ℂ)

theorem markedWeight_eq (p : ℕ) (L : ℝ) (Rf : Fin 2 → Option ℝ) (σ : Fin 2 → Option ℕ) (Rs : Fin 2 → ℝ)
    (kSel : Fin 2 → Option ℕ) (h : ℕ → Fin 2 → Fin 2 → Mom d → ℝ) (dag : Option (Fin 2 → Fin 3 → Mom d))
    (K : GNode D.T1.garden.tree → Mom d) :
    ((markedWeight LG {c} p L Rf σ (selCap LG {c} kSel) Rs h dag (fun a => K (D.ρ a)) : ℝ) : ℂ) =
      (regSelConst LG c j0 Rs kSel : ℂ) *
        (D.mult p L Rf σ Rs kSel dag K * ∏ ℓ ∈ inputLeaves D.T1.garden, (regH1 LG j0 h ℓ.1 (K ℓ.toNode) : ℂ)) := by
  unfold markedWeight
  simp only [Complex.ofReal_mul]
  rw [D.frontierW_eq, D.stemFilterCap_eq, D.selWeightCap_eq, D.leafProdCap_eq]
  have hi : ((dag.elim 1 fun cs => sibWeightCap LG {c} cs (fun a => K (D.ρ a)) : ℝ) : ℂ) = (D.ind1 dag K : ℂ) := rfl
  rw [hi]
  unfold mult
  ring

theorem offCap_pinned (pat : Fin 2 → FixPat) (t s : ℝ) (dag : Bool) :
    ∀ b ∈ offCap LG {c} dag, (fixCap LG {c} pat t s b).isSome := by
  intro b hb
  unfold offCap at hb
  split_ifs at hb
  · have hfp := (Finset.mem_filter.1 hb).2
    unfold fixCap
    rw [if_pos hfp]
    rfl
  · simp at hb

theorem selOK_cases (kSel : Fin 2 → Option ℕ) : selOK LG {c} kSel = 0 ∨ selOK LG {c} kSel = 1 := by
  unfold selOK
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **The value of a wholly regular component.** -/
theorem compValue_capG (P : WTParams) {p : ℕ} (hG : CapGeo LG {c} p) (hS : StemChain LG {c} X ζ (j0, []) .leaf)
    (pat : Fin 2 → FixPat) (t s : ℝ) (kSel : Fin 2 → Option ℕ) (Rf : Fin 2 → Option ℝ) (σ : Fin 2 → Option ℕ)
    (Rs : Fin 2 → ℝ) (h : ℕ → Fin 2 → Fin 2 → Mom P.d → ℝ) (dag : Option (Fin 2 → Fin 3 → Mom P.d))
    (roots : Fin 2 → (Fin P.d → ℤ)) :
    ∃ C : ℂ, ‖C‖ ≤ 1 ∧
      compValue P (R := 1) LG (fixCap LG {c} pat t s) (offCap LG {c} dag.isSome)
          (fun k => selOK LG {c} kSel * markedWeight LG {c} p P.L Rf σ (selCap LG {c} kSel) Rs h dag k) t roots =
        C * (regSelConst LG c j0 Rs kSel : ℂ) *
          (if roots c = roots j0 then
            kernelProt P.L P.γ P.δ D.T1 (regH1 LG j0 h) (D.mult p P.L Rf σ Rs kSel dag) (fun _ => t) 0
              ((objCfg LG {c} pat X (j0, [])).fix X s t t) (latticePoint P.L (roots j0)) (fun _ => 0) 0
          else 0) := by
  set k₀ : Mom P.d := latticePoint P.L (roots j0)
  set wt : (GNode LG.garden.tree → Mom P.d) → ℝ :=
    fun k => selOK LG {c} kSel * markedWeight LG {c} p P.L Rf σ (selCap LG {c} kSel) Rs h dag k
  -- the constant removed phase
  let offC : ℂ := match dag with
    | none => 1
    | some cs =>
      if hx : ∃ κ : GenDecoration D.T1.garden P.d (fun _ => 0) 0,
          D.ind1 (some cs) (cosetDecoration D.T1.garden P.L k₀ κ.1) ≠ 0 then
        offFactor P.L P.γ P.δ LG.garden (offCap LG {c} true) (fixCap LG {c} pat t s)
          (fun a => cosetDecoration D.T1.garden P.L k₀ hx.choose.1 (D.ρ a))
      else 1
  have hoffC : ‖offC‖ ≤ 1 := by
    cases dag with
    | none => simp [offC]
    | some cs =>
      simp only [offC]
      split_ifs
      · exact (norm_offFactor _ _ _ _ _ _ _).le
      · simp
  have hsel : ‖(selOK LG {c} kSel : ℂ)‖ ≤ 1 := by
    rcases D.selOK_cases kSel with h0 | h0 <;> simp [h0]
  refine ⟨(selOK LG {c} kSel : ℂ) * offC, ?_, ?_⟩
  · rw [norm_mul]
    exact mul_le_one₀ hsel (norm_nonneg _) hoffC
  unfold compValue
  rw [D.kernelKgen_capG P.L P.γ P.δ _ _ (D.offCap_pinned pat t s dag.isSome) wt _ roots]
  split_ifs with hr
  swap
  · ring
  have hfix : (fun b => fixCap LG {c} pat t s (D.βc b)) = (objCfg LG {c} pat X (j0, [])).fix X s t t := by
    funext b1
    exact fixCap_objTree hG hS pat t s t b1
  rw [hfix]
  -- the multiplier on decorations
  have hm : ∀ κ : GenDecoration D.T1.garden P.d (fun _ => 0) 0,
      D.capWt P.L P.γ P.δ (fixCap LG {c} pat t s) (offCap LG {c} dag.isSome) wt
          (cosetDecoration D.T1.garden P.L k₀ κ.1) =
        ((selOK LG {c} kSel : ℂ) * offC * (regSelConst LG c j0 Rs kSel : ℂ)) *
          (D.mult p P.L Rf σ Rs kSel dag (cosetDecoration D.T1.garden P.L k₀ κ.1) *
            ∏ ℓ ∈ inputLeaves D.T1.garden,
              (regH1 LG j0 h ℓ.1 (cosetDecoration D.T1.garden P.L k₀ κ.1 ℓ.toNode) : ℂ)) := by
    intro κ
    unfold capWt
    have hw : (wt (fun a => cosetDecoration D.T1.garden P.L k₀ κ.1 (D.ρ a)) : ℂ) =
        (selOK LG {c} kSel : ℂ) * ((regSelConst LG c j0 Rs kSel : ℂ) *
          (D.mult p P.L Rf σ Rs kSel dag (cosetDecoration D.T1.garden P.L k₀ κ.1) *
            ∏ ℓ ∈ inputLeaves D.T1.garden,
              (regH1 LG j0 h ℓ.1 (cosetDecoration D.T1.garden P.L k₀ κ.1 ℓ.toNode) : ℂ))) := by
      show ((selOK LG {c} kSel * markedWeight LG {c} p P.L Rf σ (selCap LG {c} kSel) Rs h dag
        (fun a => cosetDecoration D.T1.garden P.L k₀ κ.1 (D.ρ a)) : ℝ) : ℂ) = _
      rw [Complex.ofReal_mul, D.markedWeight_eq]
    have hoff : (wt (fun a => cosetDecoration D.T1.garden P.L k₀ κ.1 (D.ρ a)) : ℂ) *
        offFactor P.L P.γ P.δ LG.garden (offCap LG {c} dag.isSome) (fixCap LG {c} pat t s)
          (fun a => cosetDecoration D.T1.garden P.L k₀ κ.1 (D.ρ a)) =
        (wt (fun a => cosetDecoration D.T1.garden P.L k₀ κ.1 (D.ρ a)) : ℂ) * offC := by
      cases dag with
      | none => simp [offC, offFactor, offCap]
      | some cs =>
        by_cases hw0 : (wt (fun a => cosetDecoration D.T1.garden P.L k₀ κ.1 (D.ρ a)) : ℂ) = 0
        · rw [hw0, zero_mul, zero_mul]
        · have hind : D.ind1 (some cs) (cosetDecoration D.T1.garden P.L k₀ κ.1) ≠ 0 := by
            intro h0
            apply hw0
            rw [hw]
            unfold mult
            rw [h0]
            simp
          have hx : ∃ κ : GenDecoration D.T1.garden P.d (fun _ => 0) 0,
              D.ind1 (some cs) (cosetDecoration D.T1.garden P.L k₀ κ.1) ≠ 0 := ⟨κ, hind⟩
          simp only [offC, Option.isSome_some, dif_pos hx]
          congr 1
          exact D.offFactor_const P.L P.γ P.δ _ k₀ cs κ hx.choose hind hx.choose_spec
    rw [hoff, hw]
    ring
  rw [kernelProt_congr_m P.L P.γ P.δ D.T1 _ _
    (fun K => ((selOK LG {c} kSel : ℂ) * offC * (regSelConst LG c j0 Rs kSel : ℂ)) *
      (D.mult p P.L Rf σ Rs kSel dag K * ∏ ℓ ∈ inputLeaves D.T1.garden, (regH1 LG j0 h ℓ.1 (K ℓ.toNode) : ℂ)))
    _ _ _ _ _ _ hm, kernelProt_smul_m, kernelProt_moveH]

end CapG

end WaveTurbulence.Flower.ProtWhole
