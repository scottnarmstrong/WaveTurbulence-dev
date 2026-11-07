/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3N12
public import WaveTurbulence.Foundations.FinalCount.G3Final2
public import WaveTurbulence.Foundations.FinalCount.G3Bal
/-! # DH23 Proposition 9.5 (`finalmole`, L1806) and TARGET `finalmol` (L2182): the statement (FINALCOUNT-G3)

Source (DH23 L1806-L1817, `Revision_Submit.tex`):

> There is only one component, the *odd component*, that contains two atoms of degree `1` and `3`. All the other
> atoms have degree `2` and `4`. The atoms of degree `1` and `2` are classified as `α`- or `β`-atoms. Each `α`-atom `v`
> is labeled by a dyadic number `R_v ∈ [L⁻¹, L^{-γ+η}]`, such that if `v` has two bonds `(ℓ₁,ℓ₂)` then
> `|k_{ℓ₁} - k_{ℓ₂}| ∼ R_v` in the decoration; recall also `ι_v` and `κ_v`. Atoms that are neither `α`- nor `β`-atoms are
> called `ε`-atoms; any `ε`-atom in `𝕄_fin` *must* be LG in the decoration. Moreover `𝕄_fin` contains no triple bond.
> Any even component has at least one `β`-atom. If an even component is a cycle, then it is either a double bond, or a
> cycle of length at least `4`, or a triangle with at most one `α`-atom. If it is not a cycle, then all its `α`- and
> `β`-atoms form several disjoint chains, such that each chain has two distinct `ε`-atoms at both ends. Finally, if any
> component is a *vine* (with two joints of degree `2`), then it *must* be LG in the decoration.

TARGET `finalmol` (L2182-L2190) adds: at most `R` imperfect components (`FinalStruct.imperfect`).  Ruling R18 adds
(N1) every `β`-atom has a nonzero gap and (N2) the `ι/κ` property used in case (6) of Prop 9.6.

**Model.** A run is `HRun L γ η w κ (HSt.init M₀) hf` (`G3Hist`): Steps 1-4 with the cutting history.  The conclusion
is `Prop95Concl`.  Fields and the files proving them:
* `struct` (`FinalStruct`: degrees `1..4`, `2R` odd atoms of degree `1`/`3`, classification, even components contain a
  `β`-atom, at most `R` imperfect components, one odd component if `R = 1`): `G3Final2`, `Run.finalStruct`;
* `eps_LG`: `G3EpsLG`, `Run.eps_LG` (premise `DegenSG`: Prop 9.1 (c),(d), hinge atoms are SG);
* `label`: `IsLabel`, `κ ∈ {0,50}` (`HInv`) and, for degree-`2` `α`-atoms, `|gap| ∼ R_v`;
* `N1`, `N2`: `G3N12`.
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V D : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The atoms of the component of `a`. -/
noncomputable def compAtoms (M : Molecule V D) [Fintype D] [DecidableEq D] (a : V) : Finset V :=
  M.atoms.filter (fun b => M.SameComponent a b)

/-- `a` lies in an even component (no atom of odd degree). -/
def EvenComp (M : Molecule V D) [Fintype D] [DecidableEq D] (a : V) : Prop :=
  ∀ b ∈ M.atoms, M.SameComponent a b → Even (M.deg b)

/-- The chain of `a`: the atoms reachable from `a` through `α`/`β`-atoms (the maximal connected set of non-`ε`
atoms containing `a`). -/
noncomputable def chainOf (s : St.{u} V D₀) (a : V) : Finset V :=
  s.M.atoms.filter (fun c => s.cls c ≠ .eps ∧
    Relation.ReflTransGen (fun x y => s.M.Adj x y ∧ s.cls y ≠ .eps) a c)

/-- A *cycle* component: a double bond, or at least `4` atoms, or a triangle with at most one `α`-atom. -/
def CycleShape (s : St.{u} V D₀) (a : V) : Prop :=
  (compAtoms s.M a).card = 2 ∨ 4 ≤ (compAtoms s.M a).card ∨
    ((compAtoms s.M a).card = 3 ∧ ((compAtoms s.M a).filter fun c => ∃ ρ kp, s.cls c = .alpha ρ kp).card ≤ 1)

/-- The chain of `a` has exactly two boundary darts, and they lead to two distinct `ε`-atoms. -/
def ChainEnds (s : St.{u} V D₀) (a : V) : Prop :=
  ∃ d₁ d₂ : s.D, d₁ ≠ d₂ ∧ s.M.atom d₁ ∈ chainOf s a ∧ s.M.atom d₂ ∈ chainOf s a ∧
    s.cls (s.M.atom (s.M.mate d₁)) = .eps ∧ s.cls (s.M.atom (s.M.mate d₂)) = .eps ∧
    s.M.atom (s.M.mate d₁) ≠ s.M.atom (s.M.mate d₂) ∧
    ∀ e : s.D, s.M.atom e ∈ chainOf s a → s.M.atom (s.M.mate e) ∉ chainOf s a → e = d₁ ∨ e = d₂

/-- **The conclusions of DH23 Prop 9.5 / TARGET `finalmol` / ruling R18 for the final state `hf` of a run.** -/
structure Prop95Concl (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (R : ℕ) (hf : HSt V D₀) : Prop where
  /-- degrees, classification, parity, `β`-atoms of even components, at most `R` imperfect components (L1806, L2182) -/
  struct : FinalStruct R hf.s
  /-- every `α`-atom is labeled by a dyadic `R_v ∈ [L⁻¹, L^{-γ+η}]`, `κ_v ∈ {0,50}`, and `|k_{ℓ₁} - k_{ℓ₂}| ∼ R_v` at
  its two bonds (L1806) -/
  label : ∀ a ∈ hf.s.M.atoms, ∀ ρ kp, hf.s.cls a = .alpha ρ kp → IsLabel L γ η ρ ∧ (kp = 0 ∨ kp = 50) ∧
    ∀ x y : hf.s.D, hf.s.M.atom x = a → hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true →
      y ≠ hf.s.M.mate x → GapSim L w (κ ∘ hf.s.down) x y ρ
  /-- every `ε`-atom is LG (L1806) -/
  eps_LG : ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → ∀ x y : hf.s.D, hf.s.M.atom x = a → hf.s.M.atom y = a →
    hf.s.M.out x = false → hf.s.M.out y = true → y ≠ hf.s.M.mate x →
    Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .LG
  /-- no triple bond (L1806) -/
  no_triple : NoTripleBond hf.s.M
  /-- an even component without `ε`-atom is a cycle: double bond, length `≥ 4`, or a triangle with `≤ 1` `α`-atom
  (L1807) -/
  cycles : ∀ a ∈ hf.s.M.atoms, EvenComp hf.s.M a → (∀ b ∈ compAtoms hf.s.M a, hf.s.cls b ≠ .eps) →
    CycleShape hf.s a
  /-- in an even component with an `ε`-atom, the `α`/`β`-atoms form chains with two distinct `ε`-atoms at the ends
  (L1807) -/
  chains : ∀ a ∈ hf.s.M.atoms, EvenComp hf.s.M a → hf.s.cls a ≠ .eps → (∃ b ∈ compAtoms hf.s.M a, hf.s.cls b = .eps) →
    ChainEnds hf.s a
  /-- the degree bounds and the balance of the degree-`2` atoms (one incoming, one outgoing bond; L1777) -/
  bal : BalM hf.s.M
  /-- no bond joins an atom to itself (irreducibility of `M_sub`, preserved by the operations) -/
  noloop : ∀ x : hf.s.D, hf.s.M.atom x ≠ hf.s.M.atom (hf.s.M.mate x)
  /-- every `α`-atom has an SG gap at its two darts (`0 < |gap| ≤ L^{-γ+η}`: `α`-atoms are SG atoms of `M_sub`, L1806) -/
  alpha_sg : ∀ b ∈ hf.s.M.atoms, ∀ ρ kp, hf.s.cls b = .alpha ρ kp → ∀ x y : hf.s.D, hf.s.M.atom x = b →
    hf.s.M.atom y = b → hf.s.M.out x = false → hf.s.M.out y = true →
    Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .SG
  /-- the dart gap of every `α`/`β`-atom is, up to sign, the gap of its recorded cut -/
  dartGap : ∀ a ∈ hf.s.M.atoms, hf.s.cls a ≠ .eps → ∀ x y : hf.s.D, hf.s.M.atom x = a → hf.s.M.atom y = a →
    hf.s.M.out x = false → hf.s.M.out y = true → ∃ g, AtomGap L w κ hf a g ∧
      (Molecule.gapAt L w (κ ∘ hf.s.down) x y = g ∨ Molecule.gapAt L w (κ ∘ hf.s.down) x y = -g)
  /-- no `β`-cut with a nonzero gap is possible (Step 4 is complete; L1781, L1985) -/
  noBetaCut : NoBetaCut L w κ hf.s
  /-- (N1, R18) every `β`-atom is the product of a cut with nonzero gap (L1985: no cut at a degenerate atom) -/
  N1 : ∀ b ∈ hf.s.M.atoms, hf.s.cls b = .beta → ∃ g, AtomGap L w κ hf b g ∧ g ≠ 0
  /-- (N2, R18; L1782, L1895) if `κ_{v₁} = κ_{v₂} = 0` and the three gaps sum to zero, the gap of the `β`-atom is
  `≥ L^{-50η} min(R₁,R₂)` -/
  N2 : 1 ≤ L → 0 ≤ η → ∀ v₁ ∈ hf.s.M.atoms, ∀ v₂ ∈ hf.s.M.atoms, ∀ b ∈ hf.s.M.atoms, ∀ R₁ R₂ : ℝ,
    hf.s.cls v₁ = .alpha R₁ 0 → hf.s.cls v₂ = .alpha R₂ 0 → hf.s.cls b = .beta →
    ∀ g₁ g₂ gb : Mom d, AtomGap L w κ hf v₁ g₁ → AtomGap L w κ hf v₂ g₂ → AtomGap L w κ hf b gb →
    ∀ s₁ s₂ : ℝ, (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) → gb = s₁ • g₁ + s₂ • g₂ →
    L ^ (-50 * η) * min R₁ R₂ ≤ ‖gb‖


/-- The component of `a` has no tame `ε`-atom. -/
def TameFree (hf : HSt V D₀) (Tm : V → Prop) (a : V) : Prop :=
  ∀ e ∈ hf.s.M.atoms, hf.s.M.SameComponent a e → hf.s.cls e = .eps → ¬ Tm e

theorem TameFree.of_sc {hf : HSt V D₀} {Tm : V → Prop} {a c : V} (h : TameFree hf Tm a)
    (hc : hf.s.M.SameComponent a c) : TameFree hf Tm c :=
  fun e he hce hae => h e he (Relation.EqvGen.trans _ _ _ hc hce) hae

/-- **`Prop95Concl` relative to the tame atoms** (R29 item 2, A2): all fields of `Prop95Concl` except that the `ε`-atoms are LG, and the
chains clause holds, in the components WITHOUT tame atoms (`TameFree`).  For `Tm = False` this is `Prop95Concl`. -/
structure Prop95ConclAt (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (R : ℕ) (hf : HSt V D₀) (Tm : V → Prop) : Prop where
  struct : FinalStruct R hf.s
  label : ∀ a ∈ hf.s.M.atoms, ∀ ρ kp, hf.s.cls a = .alpha ρ kp → IsLabel L γ η ρ ∧ (kp = 0 ∨ kp = 50) ∧
    ∀ x y : hf.s.D, hf.s.M.atom x = a → hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true →
      y ≠ hf.s.M.mate x → GapSim L w (κ ∘ hf.s.down) x y ρ
  eps_LG : ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → TameFree hf Tm a → ∀ x y : hf.s.D, hf.s.M.atom x = a →
    hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true → y ≠ hf.s.M.mate x →
    Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .LG
  no_triple : NoTripleBond hf.s.M
  cycles : ∀ a ∈ hf.s.M.atoms, EvenComp hf.s.M a → (∀ b ∈ compAtoms hf.s.M a, hf.s.cls b ≠ .eps) →
    CycleShape hf.s a
  chains : ∀ a ∈ hf.s.M.atoms, EvenComp hf.s.M a → hf.s.cls a ≠ .eps → (∃ b ∈ compAtoms hf.s.M a, hf.s.cls b = .eps) →
    TameFree hf Tm a → ChainEnds hf.s a
  bal : BalM hf.s.M
  noloop : ∀ x : hf.s.D, hf.s.M.atom x ≠ hf.s.M.atom (hf.s.M.mate x)
  alpha_sg : ∀ b ∈ hf.s.M.atoms, ∀ ρ kp, hf.s.cls b = .alpha ρ kp → ∀ x y : hf.s.D, hf.s.M.atom x = b →
    hf.s.M.atom y = b → hf.s.M.out x = false → hf.s.M.out y = true →
    Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .SG
  dartGap : ∀ a ∈ hf.s.M.atoms, hf.s.cls a ≠ .eps → ∀ x y : hf.s.D, hf.s.M.atom x = a → hf.s.M.atom y = a →
    hf.s.M.out x = false → hf.s.M.out y = true → ∃ g, AtomGap L w κ hf a g ∧
      (Molecule.gapAt L w (κ ∘ hf.s.down) x y = g ∨ Molecule.gapAt L w (κ ∘ hf.s.down) x y = -g)
  noBetaCut : NoBetaCut L w κ hf.s
  N1 : ∀ b ∈ hf.s.M.atoms, hf.s.cls b = .beta → ∃ g, AtomGap L w κ hf b g ∧ g ≠ 0
  N2 : 1 ≤ L → 0 ≤ η → ∀ v₁ ∈ hf.s.M.atoms, ∀ v₂ ∈ hf.s.M.atoms, ∀ b ∈ hf.s.M.atoms, ∀ R₁ R₂ : ℝ,
    hf.s.cls v₁ = .alpha R₁ 0 → hf.s.cls v₂ = .alpha R₂ 0 → hf.s.cls b = .beta →
    ∀ g₁ g₂ gb : Mom d, AtomGap L w κ hf v₁ g₁ → AtomGap L w κ hf v₂ g₂ → AtomGap L w κ hf b gb →
    ∀ s₁ s₂ : ℝ, (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) → gb = s₁ • g₁ + s₂ • g₂ →
    L ^ (-50 * η) * min R₁ R₂ ≤ ‖gb‖

/-- The global `Prop95Concl` is `Prop95ConclAt` for every `Tm`. -/
theorem Prop95Concl.toAt {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {hf : HSt V D₀}
    (h : Prop95Concl L γ η w κ R hf) (Tm : V → Prop) : Prop95ConclAt L γ η w κ R hf Tm where
  struct := h.struct
  label := h.label
  eps_LG := fun a ha hae _ => h.eps_LG a ha hae
  no_triple := h.no_triple
  cycles := h.cycles
  chains := fun a ha hev hne hex _ => h.chains a ha hev hne hex
  bal := h.bal
  noloop := h.noloop
  alpha_sg := h.alpha_sg
  dartGap := h.dartGap
  noBetaCut := h.noBetaCut
  N1 := h.N1
  N2 := h.N2

end WaveTurbulence.FinalCountG3
