/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3Steps`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3, part 2: Steps 1--4 of the stage-2 algorithm as relations between states**
(DH23 §9.3, L1773--L1783; TARGET Operations 1--4, L2138--L2148), and the algorithm's stopping conditions.
Each relation uses the literal operation data of FINALCOUNT-G2 (`VineCut`, `TriData`, `Molecule.cut`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*} {d : ℕ}

/-! ### Step 2 data: the triangle -/

/-! ### The four steps -/

noncomputable def vineSt (s : St.{u} V D₀) (K : Step1.VineCut Src.γL s.M) (c : Cls) : St.{u} V D₀ :=
  (((s.cutSt K.C.upper K.fa K.x₁ K.x₂ c c).cutSt K.C.lower K.fb K.y₁ K.y₂ c c).delSt
    (fun a => a ∉ K.C.atoms) K.closed)

/-- **Step 1** (DH23 L1775): remove an SG vine-like object `K.C`: cut both joints along the two bonds of the object
(`K.x₁,K.x₂` at `K.C.upper`, `K.y₁,K.y₂` at `K.C.lower`) and remove the VC. The two fresh joints `fa, fb` are
`α`-atoms labelled by the dyadic `R` with `|gap of the VC| ∼ R` (TARGET: `β`-atoms if a new component is created). -/
inductive Step1 (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : St.{u} V D₀ → St.{u} V D₀ → Prop
  | vine (s : St.{u} V D₀) (K : Step1.VineCut Src.γL s.M) (R : ℝ) (kp : ℕ) (hR : IsLabel L γ η R) (hkp : kp = 0 ∨ kp = 50)
      (hu : s.cls K.C.upper = .eps) (hl : s.cls K.C.lower = .eps)
      (ga : GapSim L w (κ ∘ s.down) K.x₁ K.x₂ R) (gb : GapSim L w (κ ∘ s.down) K.y₁ K.y₂ R)
      (h3a : 3 ≤ s.M.deg K.C.upper) (h3b : 3 ≤ s.M.deg K.C.lower) :
      Step1 L γ η w κ s
        (vineSt s K (alphaOrBeta K.post.numComponents s.M.numComponents R kp))

/-! ### Stopping conditions -/

/-- **A run of the stage-2 algorithm** from `s₀` to `s_f`: Steps 1, 2, 3, 4 in this order (TARGET "Order of these
operations", L2146), each carried out until its stopping condition holds. -/
def Run (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (s₀ sf : St.{u} V D₀) : Prop :=
  ∃ s₁ s₂ s₃ : St.{u} V D₀,
    Relation.ReflTransGen (Step1 L γ η w κ) s₀ s₁ ∧ NoTripleBond s₁.M ∧
    Relation.ReflTransGen (Step2 L γ η w κ) s₁ s₂ ∧ NoSGTriangle L γ η w κ s₂ ∧
    Relation.ReflTransGen (Step3 L γ η w κ) s₂ s₃ ∧ NoSGLeft L γ η w κ s₀ s₃ ∧
    Relation.ReflTransGen Step4 s₃ sf ∧ NoBetaCut L w κ sf

end WaveTurbulence.GammaLow.FinalCount.H
