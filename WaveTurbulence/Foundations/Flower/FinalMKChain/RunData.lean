/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKChain.NoSGL
public import WaveTurbulence.Foundations.Flower.FinalMKStep.Run2

/-! # C1b2 MK-CHAIN (8): the run data of the survivor run (`RunDataLE`) and the final component decorations

Copy-thread of main's GV14 (`RunDataL`, `vineLG_of_runL`, `finalDec_compL`): the per-decoration run data is a
`CollDataMK` with survivors `E`, `SubproOblGMK`, `TripleDesig`, `UnselOKF`, `forb = survAtomsM E` and the run `HRunLCE`.
The run facts come from C1a (`HRunLE.inv`, `HRunLE.prop95L`, `HRunLE.final`, via `HingeSG`), the joint LG bound from
`joint_LG2LE` (NoSGL). -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.Flower.FinalMKChain
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **The per-decoration run data with survivors** (main's `RunDataL`, GV14). -/
def RunDataLE (L γ η : ℝ) (M₀ : Molecule V D₀) (hf : HSt V D₀) (AdmRun : (D₀ → (Fin d → ℤ)) → Prop) : Prop :=
  ∀ κ, AdmRun κ → ∃ (C : CollDataMK M₀) (m : ℕ) (E : Fin m → Object M₀) (Unsel : Set (Object M₀)),
    SubproOblGMK C.toCollData E L γ η (0 : Mom d) κ ∧ TripleDesig C.toCollData ∧
    C.UnselOKF L γ η (0 : Mom d) κ Unsel ∧ C.forb = survAtomsM E ∧ HRunLCE L γ η (0 : Mom d) κ M₀ hf C E Unsel

variable {L γ η : ℝ} {R : ℕ} {M₀ : Molecule V D₀} {hf : HSt V D₀} {Tm : V → Prop}

theorem vineLG_of_runLE [Infinite V] (hS : SubHypL R M₀) (AdmRun : (D₀ → (Fin d → ℤ)) → Prop)
    (hrun : RunDataLE L γ η M₀ hf AdmRun) (hdeg : ∀ κ, AdmRun κ → DegenSGT M₀ L γ η (0 : Mom d) κ Tm)
    (h0 : ∀ κ, AdmRun κ → ∀ a ∈ M₀.atoms, M₀.deg a = 4 →
      ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0)
    {a₀ : V} (ha₀ : a₀ ∈ hf.s.M.atoms) (hT : TameFree hf Tm a₀) (hE : LowFree hf a₀) : VineLGAtL L γ η hf a₀ AdmRun := by
  intro hvine κ' ⟨κ, hκ, hκ'⟩ x y hxy hout
  subst hκ'
  obtain ⟨C, m, E, Unsel, obl, hT3, hU, hforb, hrC⟩ := hrun κ hκ
  have hr := hrC.toHRunLE
  obtain ⟨R', -, hI⟩ := FinalMKStep.HRunLE.inv hr (InvL.init hS (h0 κ hκ))
  have hC := (FinalMKStep.HRunLE.prop95L hr hS (SubproOblGMK.hingeSGP obl) hT3 (hdeg κ hκ) (h0 κ hκ)).toAtL
    (fun a ha => hI.good.2 a ha)
  obtain ⟨⟨hdp, hA, hdes⟩, -⟩ := FinalMKStep.HRunLE.final hr hS (SubproOblGMK.hingeSGP obl) (h0 κ hκ) rfl
  have hD := hI.rel
  have hrec := hI.hrec
  obtain ⟨hrem1, hrem2⟩ := HRunLCE.rem hrC
  have hxm := (mem_compMol _ _).1 ((compMol hf.s.M a₀).atom_mem x)
  have hx' : hf.s.M.atom x.1 = (compMol hf.s.M a₀).atom x := rfl
  by_cases hε : hf.s.cls (hf.s.M.atom x.1) = .eps
  · exact dec_epsLGL (hf := hf) (hC := hC) (a₀ := a₀) hxm.1 hε (hT.of_sc hxm.2) x y rfl (by rw [← hxy]) hout
  · obtain ⟨X, j₁, j₂, hv⟩ := vine_of_vineOrDoubleL hC ha₀ hE hvine
    have J := finalJoints_of_vineL hC.struct hE hv ha₀
    have hcomp := J.comp _ hxm.1 hxm.2
    have hy : hf.s.M.atom y.1 = hf.s.M.atom x.1 := by rw [show hf.s.M.atom y.1 = (compMol hf.s.M a₀).atom y from rfl, ← hxy]; rfl
    have hout' : hf.s.M.out x.1 ≠ hf.s.M.out y.1 := hout
    rcases hcomp with h | h | ⟨h, -⟩
    · exact joint_LG2LE hS hA hD hC hT hrec hdp obl hU hforb hrem1 hrem2 hdes J hv x.1 y.1 h (hy.trans h) hout'
    · exact joint_LG2LE hS hA hD hC hT hrec hdp obl hU hforb hrem1 hrem2 hdes J.symm (isVine_symm hv) x.1 y.1 h (hy.trans h) hout'
    · exact absurd h hε

theorem finalDec_compLE [Infinite V] (hS : SubHypL R M₀) (AdmRun : (D₀ → (Fin d → ℤ)) → Prop)
    (hrun : RunDataLE L γ η M₀ hf AdmRun) (hdeg : ∀ κ, AdmRun κ → DegenSGT M₀ L γ η (0 : Mom d) κ Tm)
    (h0 : ∀ κ, AdmRun κ → ∀ a ∈ M₀.atoms, M₀.deg a = 4 →
      ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0)
    (hne : ∃ κ, AdmRun κ) (hL : 1 ≤ L) (hη : 0 ≤ η) {a₀ : V} (ha₀ : a₀ ∈ hf.s.M.atoms) (hT : TameFree hf Tm a₀)
    (hE : LowFree hf a₀) :
    G8Copy.FinalDec (compMol hf.s.M a₀) (fun a => toCls (hf.s.cls a)) L γ η (compAdmL hf a₀ AdmRun) :=
  finalDec_comp_of_vineL AdmRun (fun κ hκ => by
      obtain ⟨C, m, E, Unsel, obl, hT3, -, -, hrC⟩ := hrun κ hκ
      obtain ⟨R', -, hI⟩ := FinalMKStep.HRunLE.inv hrC.toHRunLE (InvL.init hS (h0 κ hκ))
      exact (FinalMKStep.HRunLE.prop95L hrC.toHRunLE hS (SubproOblGMK.hingeSGP obl) hT3 (hdeg κ hκ) (h0 κ hκ)).toAtL
        (fun a ha => hI.good.2 a ha)) hne hL hη ha₀ hT
    (vineLG_of_runLE hS AdmRun hrun hdeg h0 ha₀ hT hE)

end WaveTurbulence.Flower.FinalMKChain
