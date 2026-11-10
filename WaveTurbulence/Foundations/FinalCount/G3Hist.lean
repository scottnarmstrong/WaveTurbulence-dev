/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3EpsLG
/-! **FINALCOUNT-G3: the cutting history** (DH23 Remark `remiota` = L1782, TARGET Remark `remiota` L2150, and the
cut gaps).  An `HSt` is a state `s` together with the chronological list `hist` of the dart pairs of every cut
performed so far (newest first) and, for every atom produced by a cut, a record `(pair, vis)`: the pair of darts of
`M_sub` that the cut used (its gap is *the gap of the atom*) and the list `vis` of the cuts that happened *before* it.
`ι_v ≠ 0` is `IotaHit`: some earlier cut *that is still alive when `v` is cut* (R38(4), DEAD-HIT: it is carried by an atom
present at that moment) has gap `r'` with `0 < |r ± r'| ≤ L^{-50η} R_v` (sign `±`); `κ_v = 50` iff `ι_v ≠ 0`, `κ_v = 0`
otherwise (DH23 Prop `excessprop1`, L1786).  The `vis` of a record is the list of the cuts alive at the time (`HSt.alive`,
plus the earlier cuts of the same operation); `κ_v` is fixed at the creation of `v` and stored in its class.  Cuts of one operation are ordered as in the text
(triangle: `v₁, v₂, v₃`; vine: the two joints), and a cut sees all earlier cuts of the same operation.

The step relations `HStep1..HStep4` are the relations `Step1..Step4` of `G3Steps` with extra data:
* the nonzero gap of every cut (DH23 L1985: no cut at a degenerate atom; the `v₃` of a triangle and the atom of
  Step 4 are not ZG, TARGET Remark `remtame`);
* the two joints of a vine have the same gap up to sign (the *gap of the VC*, TARGET `defdiff`);
* the `ι/κ` relation `κ_v = 50 ↔ ι_v ≠ 0`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The gap of a recorded cut (a pair of darts of `M_sub`). -/
noncomputable def pgap (L : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (p : D₀ × D₀) : Mom d :=
  Molecule.gapAt L w κ p.1 p.2

/-- **`ι_v ≠ 0`** (L1782): an earlier cut `q ∈ vis` has gap `r'` with `0 < |r ± r'| ≤ L^{-50η} R`. -/
def IotaHit (L η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (vis : List (D₀ × D₀)) (p : D₀ × D₀) (R : ℝ) : Prop :=
  ∃ q ∈ vis, ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧ 0 < ‖pgap L w κ p + sg • pgap L w κ q‖ ∧
    ‖pgap L w κ p + sg • pgap L w κ q‖ ≤ L ^ (-50 * η) * R

/-- A state with its cutting history. -/
structure HSt (V : Type*) (D₀ : Type u) where
  s : St.{u} V D₀
  hist : List (D₀ × D₀)
  crec : V → Option ((D₀ × D₀) × List (D₀ × D₀))
  /-- the ancestor atom of `M_sub` of each atom (cut halves map to the atom they were cut from) -/
  anc : V → V

/-- **The cuts that are alive** (R38(4)): the recorded cuts that are still carried by a present atom. -/
noncomputable def HSt.alive (h : HSt V D₀) : List (D₀ × D₀) :=
  h.hist.filter fun q => decide (∃ a ∈ h.s.M.atoms, ∃ vis, h.crec a = some (q, vis))

theorem HSt.mem_alive {h : HSt V D₀} {q : D₀ × D₀} :
    q ∈ h.alive ↔ q ∈ h.hist ∧ ∃ a ∈ h.s.M.atoms, ∃ vis, h.crec a = some (q, vis) := by
  simp [HSt.alive]

/-- The initial history. -/
def HSt.init (M₀ : Molecule V D₀) : HSt V D₀ := ⟨St.init M₀, [], fun _ => none, id⟩

/-- The dart pair (in `M_sub`) of a pair of current darts. -/
def St.pr (s : St.{u} V D₀) (x y : s.D) : D₀ × D₀ := (s.down x, s.down y)

/-- The cuts alive when the second cut `v₂` of a triangle is made: the alive cuts, and the first cut of the triangle unless
its atom is a ghost (DH23 L1777 does not cut a ghost). -/
noncomputable def HSt.triVis1 (h : HSt V D₀) (T : TriData h.s.M) : List (D₀ × D₀) :=
  if h.s.cls (T.t 0) = .eps then h.s.pr (T.a 0) (T.b 0) :: h.alive else h.alive

/-- The cuts alive when the third cut `v₃` of a triangle is made. -/
noncomputable def HSt.triVis2 (h : HSt V D₀) (T : TriData h.s.M) : List (D₀ × D₀) :=
  if h.s.cls (T.t 1) = .eps then h.s.pr (T.a 1) (T.b 1) :: h.triVis1 T else h.triVis1 T

theorem HSt.alive_sub_triVis1 (h : HSt V D₀) (T : TriData h.s.M) : ∀ q ∈ h.alive, q ∈ h.triVis1 T := by
  intro q hq; unfold HSt.triVis1; split_ifs <;> simp [hq]

theorem HSt.triVis1_sub_triVis2 (h : HSt V D₀) (T : TriData h.s.M) : ∀ q ∈ h.triVis1 T, q ∈ h.triVis2 T := by
  intro q hq; unfold HSt.triVis2; split_ifs <;> simp [hq]

variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

/-- **Step 1** with history (DH23 L1775). -/
inductive HStep1 (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : HSt V D₀ → HSt V D₀ → Prop
  | vine (h : HSt V D₀) (K : VineCut h.s.M) (R : ℝ) (kp : ℕ) (hR : IsLabel L γ η R) (hkp : kp = 0 ∨ kp = 50)
      (hu : h.s.cls K.C.upper = .eps) (hl : h.s.cls K.C.lower = .eps)
      (ga : GapSim L w (κ ∘ h.s.down) K.x₁ K.x₂ R) (gb : GapSim L w (κ ∘ h.s.down) K.y₁ K.y₂ R)
      (htwin : pgap L w κ (h.s.pr K.y₁ K.y₂) = pgap L w κ (h.s.pr K.x₁ K.x₂) ∨
        pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂))
      (hι₁ : kp = 50 ↔ IotaHit L η w κ h.alive (h.s.pr K.x₁ K.x₂) R)
      (hι₂ : kp = 50 ↔ IotaHit L η w κ (h.s.pr K.x₁ K.x₂ :: h.alive) (h.s.pr K.y₁ K.y₂) R)
      (hsg : Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG)
      (h3a : 3 ≤ h.s.M.deg K.C.upper) (h3b : 3 ≤ h.s.M.deg K.C.lower) :
      HStep1 L γ η w κ h
        ⟨vineSt h.s K (alphaOrBeta K.post.numComponents h.s.M.numComponents R kp),
         h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist,
         Function.update (Function.update (Function.update (Function.update h.crec K.C.upper
           (some (h.s.pr K.x₁ K.x₂, h.alive))) K.fa (some (h.s.pr K.x₁ K.x₂, h.alive))) K.C.lower
           (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive))) K.fb
           (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive)),
         Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower)⟩

/-- **Step 2** with history (DH23 L1777): the cuts are performed in the order `v₁, v₂, v₃`. -/
inductive HStep2 (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : HSt V D₀ → HSt V D₀ → Prop
  | tri (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
      (hQ : ∀ j : Fin 2, IsLabel L γ η (Q j)) (hkp : ∀ j : Fin 2, kp j = 0 ∨ kp j = 50)
      (hsg : ∀ j : Fin 2, Molecule.gapKind L γ η
        (Molecule.gapAt L w (κ ∘ h.s.down) (T.a j.castSucc) (T.b j.castSucc)) = .SG)
      (hsim : ∀ j : Fin 2, GapSim L w (κ ∘ h.s.down) (T.a j.castSucc) (T.b j.castSucc) (Q j))
      (hcl : PClosed T.kept (triKeep h.s T))
      (hnz : pgap L w κ (h.s.pr (T.a 2) (T.b 2)) ≠ 0)
      (hι₀ : h.s.cls (T.t 0) = .eps → (kp 0 = 50 ↔ IotaHit L η w κ h.alive (h.s.pr (T.a 0) (T.b 0)) (Q 0)))
      (hι₁ : h.s.cls (T.t 1) = .eps → (kp 1 = 50 ↔ IotaHit L η w κ (h.triVis1 T) (h.s.pr (T.a 1) (T.b 1)) (Q 1)))
      (h3 : ∀ j, h.s.cls (T.t j) = .eps → 3 ≤ h.s.M.deg (T.t j)) :
      HStep2 L γ η w κ h
        ⟨triSt h.s T Q kp hcl,
         h.s.pr (T.a 2) (T.b 2) :: h.s.pr (T.a 1) (T.b 1) :: h.s.pr (T.a 0) (T.b 0) :: h.hist,
         Function.update (Function.update (Function.update h.crec (T.f 0) (some (h.s.pr (T.a 0) (T.b 0), h.alive)))
           (T.f 1) (some (h.s.pr (T.a 1) (T.b 1), h.triVis1 T)))
           (T.f 2) (some (h.s.pr (T.a 2) (T.b 2), h.triVis2 T)),
         Function.update (Function.update (Function.update h.anc (T.f 0) (h.anc (T.t 0))) (T.f 1) (h.anc (T.t 1)))
           (T.f 2) (h.anc (T.t 2))⟩

/-- **Step 3** with history (DH23 L1779). -/
inductive HStep3 (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : HSt V D₀ → HSt V D₀ → Prop
  | cut (h : HSt V D₀) (v v₂ : V) (x₁ x₂ : h.s.D) (hc : h.s.M.IsCutData v v₂ x₁ x₂) (R : ℝ) (kp : ℕ)
      (hR : IsLabel L γ η R) (hkp : kp = 0 ∨ kp = 50) (hε : h.s.cls v = .eps)
      (hsg : Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) x₁ x₂) = .SG)
      (hsim : GapSim L w (κ ∘ h.s.down) x₁ x₂ R)
      (hι : kp = 50 ↔ IotaHit L η w κ h.alive (h.s.pr x₁ x₂) R) (h3 : 3 ≤ h.s.M.deg v) :
      HStep3 L γ η w κ h
        ⟨h.s.cutSt v v₂ x₁ x₂ (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta)
          (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta),
         h.s.pr x₁ x₂ :: h.hist,
         Function.update (Function.update h.crec v (some (h.s.pr x₁ x₂, h.alive))) v₂
           (some (h.s.pr x₁ x₂, h.alive)),
         Function.update h.anc v₂ (h.anc v)⟩

/-- **Step 4** with history (DH23 L1781): a `β`-cut with a nonzero gap (no cut at a degenerate atom, L1985). -/
inductive HStep4 (L : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : HSt V D₀ → HSt V D₀ → Prop
  | cut (h : HSt V D₀) (v v₂ : V) (x₁ x₂ : h.s.D) (hc : h.s.M.IsCutData v v₂ x₁ x₂)
      (hε : h.s.cls v = .eps) (hβ : ¬ h.s.M.IsAlphaCut v v₂ x₁ x₂) (hnz : pgap L w κ (h.s.pr x₁ x₂) ≠ 0)
      (h3 : 3 ≤ h.s.M.deg v) :
      HStep4 L w κ h ⟨h.s.cutSt v v₂ x₁ x₂ .beta .beta, h.s.pr x₁ x₂ :: h.hist,
        Function.update (Function.update h.crec v (some (h.s.pr x₁ x₂, h.alive))) v₂
          (some (h.s.pr x₁ x₂, h.alive)),
        Function.update h.anc v₂ (h.anc v)⟩


/-! ### Forgetting the history -/

theorem HStep1.step {h h' : HSt V D₀} (hs : HStep1 L γ η w κ h h') : Step1 L γ η w κ h.s h'.s := by
  cases hs with
  | vine K R kp hR hkp hu hl ga gb htwin hι₁ hι₂ hsg h3a h3b => exact Step1.vine h.s K R kp hR hkp hu hl ga gb h3a h3b

theorem HStep2.step {h h' : HSt V D₀} (hs : HStep2 L γ η w κ h h') : Step2 L γ η w κ h.s h'.s := by
  cases hs with
  | tri T Q kp hQ hkp hsg hsim hcl hnz hι₀ hι₁ h3 => exact Step2.tri h.s T Q kp hQ hkp hsg hsim hcl h3

theorem HStep3.step {h h' : HSt V D₀} (hs : HStep3 L γ η w κ h h') : Step3 L γ η w κ h.s h'.s := by
  cases hs with
  | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 => exact Step3.cut h.s v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim h3

theorem HStep4.step {h h' : HSt V D₀} (hs : HStep4 L w κ h h') : Step4 h.s h'.s := by
  cases hs with
  | cut v v₂ x₁ x₂ hc hε hβ hnz h3 => exact Step4.cut h.s v v₂ x₁ x₂ hc hε hβ h3

end WaveTurbulence.FinalCountG3
