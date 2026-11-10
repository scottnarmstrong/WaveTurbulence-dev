/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmP1Rho
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Step5b
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3URun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3UStep
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Vine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAdm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCoords
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCDict
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCFlow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCGain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCInj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCLadProd
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCScale
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Gamma
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmPhase1`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY, phase 1: nodes, classes and uniform steps of the Step-1 phase (vine removals).**
A vine node of `h` is `(x₁,x₂,y₁,y₂,z,b,a,sg)`: the four darts of `VineCut` (fresh names `fresh3 h 0, 1`), the label `R = 2^z`, `kp = 50` iff `b`,
and the alive-cut witness `(a, sg)`.  Its class is the set of `κ ∈ A` for which the step data are valid (`UStep1` is then uniform).
All state-level properties of the cut `K` that `excessprop1` needs are collected in `VFacts` (proved by the existence part). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The collected objects of Step 1 for the decoration `κ`: `C₁` and `C₂ = C2Can κ (Unsel κ)` (one designation per atom set, R50) (L2101). -/
def Collected {M₀ : Molecule V D₀} (C : CollData M₀) (Un : Set (Src.Object Src.γL M₀)) (L γ η : ℝ) (w : Mom d)
    (κ : D₀ → (Fin d → ℤ)) (U : Src.Object Src.γL M₀) : Prop :=
  (∃ i, U = C.collection i) ∨ U ∈ C.C2Can L γ η w κ Un

/-- No dart of the object `U` of `M₀` remains in the state `h`. -/
def Dartless {M₀ : Molecule V D₀} (U : Src.Object Src.γL M₀) (h : HSt V D₀) : Prop :=
  ∀ x : h.s.D, ¬ U.ContainsDart (h.s.down x)

/-- **The restricted Step 1 (R49, Finding 1).**  Vine steps only for a collected object `U` (`K.C.atoms = U.atoms`), and only
once the first-stage objects `Fst` (CN / root-CL vines) are gone unless `U ∈ Fst`; triple steps only after every collected
object is dartless. -/
inductive HStep1R {M₀ : Molecule V D₀} (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀))
    (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : HSt V D₀ → HSt V D₀ → Prop
  | vine (h : HSt V D₀) (K : Step1.VineCut Src.γL h.s.M) (R : ℝ) (kp : ℕ) (hs : HStep1C C L γ η w κ h (h.vinePostL K R kp))
      (U : Src.Object Src.γL M₀) (hU : Collected C (Un κ) L γ η w κ U) (hUK : U.atoms = K.C.atoms)
      (hUD : U.ContainsDart (h.s.down K.x₁) ∧ U.ContainsDart (h.s.down K.x₂) ∧ U.ContainsDart (h.s.down K.y₁) ∧
        U.ContainsDart (h.s.down K.y₂))
      (hUJ : (M₀.atom (h.s.down K.x₁) = U.upper ∧ M₀.atom (h.s.down K.y₁) = U.lower) ∨
        (M₀.atom (h.s.down K.x₁) = U.lower ∧ M₀.atom (h.s.down K.y₁) = U.upper))
      (hord : U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' h) : HStep1R C Un Fst L γ η w κ h (h.vinePostL K R kp)
  | triple (h h' : HSt V D₀) (hs : HStep1C C L γ η w κ h h') (hs3 : HStep3C C L γ η w κ h h')
      (hall : ∀ U, Collected C (Un κ) L γ η w κ U → Dartless U h)
      (hF : h'.s.M.numComponents ≤ h.s.M.numComponents) : HStep1R C Un Fst L γ η w κ h h'

theorem HStep1R.toC {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
    {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {h h' : HSt V D₀} (hs : HStep1R C Un Fst L γ η w κ h h') :
    HStep1C C L γ η w κ h h' := by
  cases hs with
  | vine K R kp hs _ _ _ _ _ _ => exact hs
  | triple _ hs _ _ _ => exact hs

/-- The reach relation of Step 1 (restricted, R49). -/
def Reach1 {M₀ : Molecule V D₀} (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀))
    (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  Relation.ReflTransGen (HStep1R C Un Fst L γ η w κ) (HSt.init M₀) h

theorem HStep1C.toAny {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {h h' : HSt V D₀}
    (hs : HStep1C C L γ η w κ h h') : HAny L γ η w κ h h' := by
  rcases hs.cases with h1 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inr (Or.inl h3.toHStep3))

theorem Reach1.toC {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
    {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {h : HSt V D₀} (hr : Reach1 C Un Fst L γ η w κ h) :
    Relation.ReflTransGen (HStep1C C L γ η w κ) (HSt.init M₀) h :=
  Relation.ReflTransGen.mono (fun _ _ hs => hs.toC) _ _ hr

theorem Reach1.toAny {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
    {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {h : HSt V D₀}
    (hr : Reach1 C Un Fst L γ η w κ h) : Relation.ReflTransGen (HAny L γ η w κ) (HSt.init M₀) h :=
  Relation.ReflTransGen.mono (p := HAny L γ η w κ) (fun a b hs => HStep1C.toAny hs) _ _ hr.toC

abbrev Inv1 (M₀ : Molecule V D₀) (Rn : ℕ) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀))
    (Fst : Set (Src.Object Src.γL M₀)) (L γ η : ℝ) (w : Mom d) (A0 A : Set (D₀ → (Fin d → ℤ)))
    (h : HSt V D₀) : Prop :=
  Inv3 M₀ Rn (fun κ h => Reach1 C Un Fst L γ η w κ h) L w A0 A h

theorem Inv1.mono {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d} {A0 A B : Set (D₀ → (Fin d → ℤ))}
    {h : HSt V D₀} (hA : Inv1 M₀ Rn C Un Fst L γ η w A0 A h) (hB : B ⊆ A) : Inv1 M₀ Rn C Un Fst L γ η w A0 B h :=
  Inv3.mono hA hB

/-- The state-level facts about a removed object `K` used by the Step-1 bounds. -/
structure VFacts {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (h : HSt V D₀) (K : Step1.VineCut Src.γL h.s.M) : Prop where
  hu : h.s.cls K.C.upper = .eps
  hl : h.s.cls K.C.lower = .eps
  h3a : 3 ≤ h.s.M.deg K.C.upper
  h3b : 3 ≤ h.s.M.deg K.C.lower
  hdu : Desig C (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂)
  hdl : Desig C (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂)
  /-- `excessprop1` hypothesis `hcls`, for every cut with the same post state -/
  hcls : ∀ (R : ℝ) (kp : ℕ) (K' : Step1.VineCut Src.γL h.s.M) (R' : ℝ) (kp' : ℕ), h.vinePostL K R kp = h.vinePostL K' R' kp' →
    Step1.SingleVineVCGamma K' ∨ Nonempty (Step1.DoubleShape K')
  hconn : ∀ (R : ℝ) (kp : ℕ) (K' : Step1.VineCut Src.γL h.s.M) (R' : ℝ) (kp' : ℕ), h.vinePostL K R kp = h.vinePostL K' R' kp' →
    Nonempty (Step1.DoubleShape K') → ∃ G : Finset h.s.D, (∀ z ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K' G
  hnl : ∀ x, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x)
  hrho : h.s.M.rho ≤ K.post.rho + 86
  hint : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a

/-- A vine node. -/
def Node1 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀) (t : T1 h) : Prop :=
  ∃ K : Step1.VineCut Src.γL h.s.M, K.x₁ = t.1 ∧ K.x₂ = t.2.1 ∧ K.y₁ = t.2.2.1 ∧ K.y₂ = t.2.2.2.1 ∧ K.fa = fresh3 h 0 ∧ K.fb = fresh3 h 1 ∧
    VFacts C crit h K ∧ IsLabel L γ η ((2 : ℝ) ^ t.2.2.2.2.1) ∧ t.2.2.2.2.2.2.1 ∈ h.s.M.atoms ∧
    (t.2.2.2.2.2.1 = true → ∃ q vis, h.crec t.2.2.2.2.2.2.1 = some (q, vis) ∧ q ∈ h.hist)

noncomputable def nodes1 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀) : Finset (T1 h) :=
  ((Finset.univ : Finset h.s.D) ×ˢ ((Finset.univ : Finset h.s.D) ×ˢ ((Finset.univ : Finset h.s.D) ×ˢ ((Finset.univ : Finset h.s.D) ×ˢ
    ((Finset.Icc (-(⌈2 * Real.log L⌉₊ : ℤ)) 0) ×ˢ ((Finset.univ : Finset Bool) ×ˢ (h.s.M.atoms ×ˢ (Finset.univ : Finset Bool)))))))).filter
    fun t => Node1 C crit L γ η h t

theorem nodes1_card [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀) :
    (nodes1 C crit L γ η h).card ≤ Fintype.card h.s.D * (Fintype.card h.s.D * (Fintype.card h.s.D * (Fintype.card h.s.D *
      ((⌈2 * Real.log L⌉₊ + 1) * (2 * (h.s.M.atoms.card * 2)))))) := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool, Int.card_Icc]
  have : (0 + 1 - -(⌈2 * Real.log L⌉₊ : ℤ)).toNat = ⌈2 * Real.log L⌉₊ + 1 := by omega
  rw [this]

/-- The post state of a node (junk `h` if the node is not valid). -/
noncomputable def post1 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀)
    (t : T1 h) : HSt V D₀ :=
  if hn : Node1 C crit L γ η h t then h.vinePostL (Classical.choose hn) ((2 : ℝ) ^ t.2.2.2.2.1) (if t.2.2.2.2.2.1 then 50 else 0) else h

/-- The decorations of `A` for which the vine node with darts `x₁ x₂ y₁ y₂` is a restricted Step-1 move: some object `U` collected for
`κ` has exactly the atoms of every vine cut with these data, and the first-stage order holds. -/
def Avine [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀))
    (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (x₁ x₂ y₁ y₂ : h.s.D) : Set (D₀ → (Fin d → ℤ)) :=
  {k | k ∈ A ∧ ∃ U : Src.Object Src.γL M₀, Collected C (Un k) L γ η w k U ∧
    (∀ K : Step1.VineCut Src.γL h.s.M, K.x₁ = x₁ → K.x₂ = x₂ → K.y₁ = y₁ → K.y₂ = y₂ → K.fa = fresh3 h 0 → K.fb = fresh3 h 1 →
      U.atoms = K.C.atoms) ∧
    (U.ContainsDart (h.s.down x₁) ∧ U.ContainsDart (h.s.down x₂) ∧ U.ContainsDart (h.s.down y₁) ∧
      U.ContainsDart (h.s.down y₂)) ∧
    ((M₀.atom (h.s.down x₁) = U.upper ∧ M₀.atom (h.s.down y₁) = U.lower) ∨
      (M₀.atom (h.s.down x₁) = U.lower ∧ M₀.atom (h.s.down y₁) = U.upper)) ∧
    (U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' h)}

theorem Avine_sub [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
    {L γ η : ℝ} {w : Mom d} {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {x₁ x₂ y₁ y₂ : h.s.D} :
    Avine C Un Fst L γ η w h A x₁ x₂ y₁ y₂ ⊆ A := fun _ hk => hk.1

/-- The decorations of `A` for which every collected object is dartless (the triple-cut stage). -/
def Atrip {M₀ : Molecule V D₀} (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀))
    (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) : Set (D₀ → (Fin d → ℤ)) :=
  {k | k ∈ A ∧ ∀ U, Collected C (Un k) L γ η w k U → Dartless U h}

theorem Atrip_sub {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {L γ η : ℝ} {w : Mom d} {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} : Atrip C Un L γ η w h A ⊆ A := fun _ hk => hk.1

end WaveTurbulence.GammaLow.FinalCount.H
