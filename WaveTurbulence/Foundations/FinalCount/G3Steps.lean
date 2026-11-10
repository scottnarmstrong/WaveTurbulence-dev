/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3State
/-! **FINALCOUNT-G3, part 2: Steps 1--4 of the stage-2 algorithm as relations between states**
(DH23 §9.3, L1773--L1783; TARGET Operations 1--4, L2138--L2148), and the algorithm's stopping conditions.
Each relation uses the literal operation data of FINALCOUNT-G2 (`VineCut`, `TriData`, `Molecule.cut`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*} {d : ℕ}

/-! ### Step 2 data: the triangle -/

/-- The atoms kept after Step 2: the ghosts (isolated remainders of cuts of already cut degree-`2` atoms) are deleted. -/
def triKeep (s : St.{u} V D₀) (T : TriData s.M) : V → Prop :=
  fun a => ∀ j, s.cls (T.t j) ≠ .eps → a ≠ T.f j

/-- Classes of the three atoms `f_j` left by a triangle removal (DH23 L1777: `v_3` is a `β`-atom; `v_j` is `α`
(resp. `β`) if it is in the same (resp. a different) component as `v_3`, except that if `v_1, v_2` lie in one
component different from `v_3`, then `v_1` is `α` and `v_2` is `β`). Components are those of the molecule `T.kept`.
`v_1 = t 0`, `v_2 = t 1`, `v_3 = t 2`. -/
noncomputable def triCls (s : St.{u} V D₀) (T : TriData s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ) (a : V) : Cls :=
  if a = T.f 2 then (if s.cls (T.t 2) = .eps then .beta else .ghost)
  else if a = T.f 0 then
    (if s.cls (T.t 0) = .eps then
      (if T.kept.SameComponent (T.f 0) (T.f 2) ∨ T.kept.SameComponent (T.f 0) (T.f 1) then .alpha (Q 0) (kp 0) else .beta)
     else .ghost)
  else if a = T.f 1 then
    (if s.cls (T.t 1) = .eps then
      (if T.kept.SameComponent (T.f 1) (T.f 2) then .alpha (Q 1) (kp 1) else .beta)
     else .ghost)
  else s.cls a

/-! ### The four steps -/

/-- The state after Step 1 on `K` (two cuts with the class `c` of the joints, then removal of the VC). -/
noncomputable def vineSt (s : St.{u} V D₀) (K : VineCut s.M) (c : Cls) : St.{u} V D₀ :=
  (((s.cutSt K.C.upper K.fa K.x₁ K.x₂ c c).cutSt K.C.lower K.fb K.y₁ K.y₂ c c).delSt
    (fun a => a ∉ K.C.atoms) K.closed)

/-- The three cuts of a triangle (classes: `β,β` for an `ε` atom; for an already cut atom the isolated remainder is a ghost). -/
noncomputable def triCuts (s : St.{u} V D₀) (T : TriData s.M) : St.{u} V D₀ :=
  (((s.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta (if s.cls (T.t 0) = .eps then .beta else .ghost)).cutSt
    (T.t 1) (T.f 1) (T.a 1) (T.b 1) .beta (if s.cls (T.t 1) = .eps then .beta else .ghost)).cutSt
    (T.t 2) (T.f 2) (T.a 2) (T.b 2) .beta (if s.cls (T.t 2) = .eps then .beta else .ghost))

/-- The state after Step 2 on `T`: three cuts, removal of the triangle, the classes of DH23 L1777, deletion of ghosts. -/
noncomputable def triSt (s : St.{u} V D₀) (T : TriData s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
    (hcl : PClosed T.kept (triKeep s T)) : St.{u} V D₀ :=
  (((triCuts s T).delSt T.TP T.pclosed).withCls (triCls s T Q kp)).delSt (triKeep s T) hcl

/-- **Step 1** (DH23 L1775): remove an SG vine-like object `K.C`: cut both joints along the two bonds of the object
(`K.x₁,K.x₂` at `K.C.upper`, `K.y₁,K.y₂` at `K.C.lower`) and remove the VC. The two fresh joints `fa, fb` are
`α`-atoms labelled by the dyadic `R` with `|gap of the VC| ∼ R` (TARGET: `β`-atoms if a new component is created). -/
inductive Step1 (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : St.{u} V D₀ → St.{u} V D₀ → Prop
  | vine (s : St.{u} V D₀) (K : VineCut s.M) (R : ℝ) (kp : ℕ) (hR : IsLabel L γ η R) (hkp : kp = 0 ∨ kp = 50)
      (hu : s.cls K.C.upper = .eps) (hl : s.cls K.C.lower = .eps)
      (ga : GapSim L w (κ ∘ s.down) K.x₁ K.x₂ R) (gb : GapSim L w (κ ∘ s.down) K.y₁ K.y₂ R)
      (h3a : 3 ≤ s.M.deg K.C.upper) (h3b : 3 ≤ s.M.deg K.C.lower) :
      Step1 L γ η w κ s
        (vineSt s K (alphaOrBeta K.post.numComponents s.M.numComponents R kp))

/-- **Step 2** (DH23 L1777): remove a triangle `t 0, t 1, t 2` of which `t 0, t 1` are SG triples (for the triangle
darts `(a j, b j)`), labelled `Q j`. Atoms `t j` that are already cut (classified, hence of degree `2`) leave a ghost,
which is deleted. -/
inductive Step2 (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : St.{u} V D₀ → St.{u} V D₀ → Prop
  | tri (s : St.{u} V D₀) (T : TriData s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
      (hQ : ∀ j : Fin 2, IsLabel L γ η (Q j)) (hkp : ∀ j : Fin 2, kp j = 0 ∨ kp j = 50)
      (hsg : ∀ j : Fin 2, Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ s.down) (T.a j.castSucc) (T.b j.castSucc)) = .SG)
      (hsim : ∀ j : Fin 2, GapSim L w (κ ∘ s.down) (T.a j.castSucc) (T.b j.castSucc) (Q j))
      (hcl : PClosed T.kept (triKeep s T))
      (h3 : ∀ j, s.cls (T.t j) = .eps → 3 ≤ s.M.deg (T.t j)) :
      Step2 L γ η w κ s (triSt s T Q kp hcl)

/-- **Step 3** (DH23 L1779): cut an SG atom `v` of degree `≥ 3` along its designated bonds `(x₁, x₂)` (an SG triple,
`|gap| ∼ R`); `α`- or `β`-cut. -/
inductive Step3 (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : St.{u} V D₀ → St.{u} V D₀ → Prop
  | cut (s : St.{u} V D₀) (v v₂ : V) (x₁ x₂ : s.D) (h : s.M.IsCutData v v₂ x₁ x₂) (R : ℝ) (kp : ℕ)
      (hR : IsLabel L γ η R) (hkp : kp = 0 ∨ kp = 50) (hε : s.cls v = .eps)
      (hsg : Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ s.down) x₁ x₂) = .SG)
      (hsim : GapSim L w (κ ∘ s.down) x₁ x₂ R) (h3 : 3 ≤ s.M.deg v) :
      Step3 L γ η w κ s
        (s.cutSt v v₂ x₁ x₂
          (if s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta)
          (if s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta))

/-- **Step 4** (DH23 L1781): a `β`-cut of an atom of degree `3` or `4`. -/
inductive Step4 : St.{u} V D₀ → St.{u} V D₀ → Prop
  | cut (s : St.{u} V D₀) (v v₂ : V) (x₁ x₂ : s.D) (h : s.M.IsCutData v v₂ x₁ x₂)
      (hε : s.cls v = .eps) (hβ : ¬ s.M.IsAlphaCut v v₂ x₁ x₂) (h3 : 3 ≤ s.M.deg v) :
      Step4 s (s.cutSt v v₂ x₁ x₂ .beta .beta)

/-! ### Stopping conditions -/

/-- Step 1 is complete: it collected and destroyed all the triple bonds (DH23 L1816, "any triple bond is destroyed in
Step 1"; subpro (c): a triple bond is among the collected objects). -/
def NoTripleBond {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) : Prop :=
  ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ b → M.bondsBetween a b < 3

/-- Step 3 is complete: no `ε`-atom is SG (an atom of `M_sub = s₀.M` is SG if it has an SG triple, TARGET `defdiff`). -/
def NoSGLeft (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (s₀ s : St.{u} V D₀) : Prop :=
  ∀ v ∈ s.M.atoms, s.cls v = .eps → ¬ SGat s₀.M L γ η w (κ ∘ s₀.down) v

/-- Step 4 is complete: no atom of degree `3` or `4` admits a `β`-cut with a nonzero gap (DH23 L1781 with the Remark
`remtame` / L1985: a cut at a degenerate (ZG) atom is not performed, so only cuts with a nonzero gap are excluded). -/
def NoBetaCut (L : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (s : St.{u} V D₀) : Prop :=
  ∀ v ∈ s.M.atoms, 3 ≤ s.M.deg v → ∀ v₂ x₁ x₂, s.M.IsCutData v v₂ x₁ x₂ →
    Molecule.gapAt L w (κ ∘ s.down) x₁ x₂ ≠ 0 → s.M.IsAlphaCut v v₂ x₁ x₂

end WaveTurbulence.FinalCountG3
