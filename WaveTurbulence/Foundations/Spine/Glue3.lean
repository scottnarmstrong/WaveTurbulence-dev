/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Glue2
import Mathlib.Tactic
/-! Per-class data: rails, the `lincomblem` selections, the paired rungs. -/
@[expose] public section
open WaveTurbulence.Induct
open Finset
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
variable {w d : ℕ} (G : Garden w)

/-- Class data fixed by a representative presentation family. -/
structure CD (D : SplicedKernelData G d) (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (hp : G.IsPlain) (π0 : PF G) (εS : LQ G → ℝ) where
  uR : LQ G → ℕ → GardenDart G
  vR : LQ G → ℕ → GardenDart G
  huR : ∀ S, ∀ j < π0.m S, neighborDarts G.molecule (rowN (π0.u S) j) (rowN (π0.u S) (j + 1)) = {uR S j} ∧
    neighborDarts G.molecule (rowN (π0.v S) j) (rowN (π0.v S) (j + 1)) = {vR S j}
  q : LQ G → ℕ
  r' : ∀ S, Fin (q S) → ℕ
  cc : ∀ S, ℕ → Fin (q S) → ℝ
  dd : LQ G → ℕ → ℝ
  hq : ∀ S, q S ≤ d
  hrI : ∀ S l, r' S l ∈ Finset.Icc 1 (π0.m S - 1)
  hcc : ∀ S, ∀ j ∈ Finset.Icc 1 (π0.m S - 1), ∀ l, |cc S j l| ≤ (2 : ℝ) ^ (d - 1)
  hprop : ∀ S (Sv E : ℕ → ℝ) (ψ : Mom d), (∀ j ∈ Finset.Icc 1 (π0.m S - 1), |E j| ≤ εS S) →
    (∀ j ∈ Finset.Icc 1 (π0.m S - 1), Sv j = inner ℝ ψ (Y0rung G D (uR S) (vR S) j) +
      Crung G hp D L γ δ base roots (rowN (π0.u S) j) (rowN (π0.v S) j) + E j) →
    ∀ j ∈ Finset.Icc 1 (π0.m S - 1),
      |Sv j - ∑ l, cc S j l * Sv (r' S l) - dd S j| ≤ (1 + d * (2 : ℝ) ^ (d - 1)) * |εS S|

theorem exists_CD (D : SplicedKernelData G d) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (hp : G.IsPlain) (π0 : PF G) (εS : LQ G → ℝ) :
    Nonempty (CD G D L γ δ base roots hp π0 εS) := by
  classical
  have h1 : ∀ S : LQ G, ∃ uR vR : ℕ → GardenDart G, ∀ j < π0.m S,
      neighborDarts G.molecule (rowN (π0.u S) j) (rowN (π0.u S) (j + 1)) = {uR j} ∧
      neighborDarts G.molecule (rowN (π0.v S) j) (rowN (π0.v S) (j + 1)) = {vR j} :=
    fun S => exists_rails G.molecule (π0.ladder S)
  choose uR vR huR using h1
  have h2 : ∀ S : LQ G, ∃ (q : ℕ) (r : Fin q → ℕ) (cc : ℕ → Fin q → ℝ) (dd : ℕ → ℝ), q ≤ d ∧
      (∀ i, r i ∈ Finset.Icc 1 (π0.m S - 1)) ∧
      (∀ j ∈ Finset.Icc 1 (π0.m S - 1), ∀ i, |cc j i| ≤ (2 : ℝ) ^ (d - 1)) ∧
      ∀ (Sv E : ℕ → ℝ) (ψ : Mom d), (∀ j ∈ Finset.Icc 1 (π0.m S - 1), |E j| ≤ εS S) →
        (∀ j ∈ Finset.Icc 1 (π0.m S - 1), Sv j = inner ℝ ψ (Y0rung G D (uR S) (vR S) j) +
          Crung G hp D L γ δ base roots (rowN (π0.u S) j) (rowN (π0.v S) j) + E j) →
        ∀ j ∈ Finset.Icc 1 (π0.m S - 1),
          |Sv j - ∑ i, cc j i * Sv (r i) - dd j| ≤ (1 + d * (2 : ℝ) ^ (d - 1)) * |εS S| :=
    fun S => loc_alg (Finset.Icc 1 (π0.m S - 1)) (Y0rung G D (uR S) (vR S))
      (fun j => Crung G hp D L γ δ base roots (rowN (π0.u S) j) (rowN (π0.v S) j)) (εS S)
  choose q r' cc dd hq hrI hcc hprop using h2
  exact ⟨⟨uR, vR, huR, q, r', cc, dd, hq, hrI, hcc, hprop⟩⟩

variable {G}
variable {D : SplicedKernelData G d} {L γ δ : ℝ} {base : Mom d} {roots : Fin w → (Fin d → ℤ)}
  {hp : G.IsPlain} {π0 : PF G} {εS : LQ G → ℝ}

/-- The selected rungs of `S`. -/
def CD.sel (cd : CD G D L γ δ base roots hp π0 εS) (S : LQ G) : Finset ℕ :=
  Finset.univ.image (cd.r' S)

/-- The paired rungs of `S`: the interior rungs that are not selected, when `S` is small. -/
noncomputable def CD.JS (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop) (S : LQ G) :
    Finset ℕ := by
  classical
  exact if isSmall S then Finset.Icc 1 (π0.m S - 1) \ cd.sel S else ∅

noncomputable def CD.Kn (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop) (S : LQ G) : ℕ :=
  (cd.JS isSmall S).card

noncomputable def CD.enum (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop) (S : LQ G) :
    Fin (cd.Kn isSmall S) → ℕ := fun i => (cd.JS isSmall S).orderEmbOfFin rfl i

theorem CD.enum_strictMono (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop) (S : LQ G) :
    StrictMono (cd.enum isSmall S) := (cd.JS isSmall S).orderEmbOfFin rfl |>.strictMono

theorem CD.enum_mem (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop) (S : LQ G)
    (i : Fin (cd.Kn isSmall S)) : cd.enum isSmall S i ∈ cd.JS isSmall S :=
  Finset.orderEmbOfFin_mem _ _ _

theorem CD.JS_sub (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop) (S : LQ G) {j : ℕ}
    (hj : j ∈ cd.JS isSmall S) : (1 ≤ j ∧ j < π0.m S) ∧ j ∉ cd.sel S ∧ isSmall S := by
  unfold CD.JS at hj
  by_cases h : isSmall S
  · rw [if_pos h] at hj
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hj
    exact ⟨⟨hj.1.1, by omega⟩, hj.2, h⟩
  · rw [if_neg h] at hj; simp at hj

end WaveTurbulence.Ladder
