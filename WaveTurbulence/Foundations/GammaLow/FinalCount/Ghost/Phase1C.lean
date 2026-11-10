/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase2C
/-! **Ghost assembly, Phase 1 (C): the split of a creation step with two twin atoms** (design: `CHAIN-DESIGN.md`).

A Phase-1 creation step (Operation 1: the joints `fa`, `fb`; a triple α-cut: `v`, `v₂`) creates two atoms `n 0`, `n 1`
whose gap vectors are `± g k0` for one common gap `g` (the joint gap / the cut gap). Survivors `X` come with a survivor
map `F : SurvMap h h' X`. The status `s ∈ Fin 3` of `n j` under `k0`: `0` — `g k0` is (T-TR) to every critical survivor
adjacent to `n j`; `i+1` — `g k0` lies in the cone around the gap of the `i`-th neighbour of `n j`, a critical survivor.
`split1 … B0 σ` (`σ ∈ Fin 3 × Fin 3`) cover `B0` (`split1_cover`); the new edges of the child are covered by
`cov1Of n σ` (`edge_cover1`, given that the twin pair itself is no edge in the class `(0,0)`); a class with some `s ≠ 0`
has one cone around a critical present atom (`stat1_cone`), paid by `k1Of σ = 2` (one cone covers both twins). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The split index of a Phase-1 creation step. -/
abbrev Sig1 := Fin 3 × Fin 3

/-- The status of `n j` in the index `σ`. -/
def sOf (σ : Sig1) (j : Fin 2) : Fin 3 := if j = 0 then σ.1 else σ.2

section
variable (L γ η : ℝ) (w : Mom d) (h h' : HSt V D₀) (X : Set V) (n : Fin 2 → V)
  (g : (D₀ → (Fin d → ℤ)) → Mom d)

/-- The status `s` of the new atom `n j` under `k0`. -/
def stat1 (j : Fin 2) (s : Fin 3) (k0 : D₀ → (Fin d → ℤ)) : Prop :=
  if IsCritA L γ η h' (n j) then
    (s = 0 → ∀ y ∈ X, IsCritA L γ η h' y → h'.s.M.Adj (n j) y → TRpt L η (g k0) (gvec h L w k0 y)) ∧
      (∀ i : Fin 2, s = i.succ → ∃ y, nbrAt h' (n j) i = some y ∧ y ∈ X ∧ IsCritA L γ η h' y ∧
        InCone (L ^ (-6 * η)) (g k0) (gvec h L w k0 y))
  else s = 0

/-- **The split class `σ`** of a class `B0`. -/
def split1 (B0 : Set (D₀ → (Fin d → ℤ))) (σ : Sig1) : Set (D₀ → (Fin d → ℤ)) :=
  {k0 | k0 ∈ B0 ∧ ∀ j : Fin 2, stat1 L γ η w h h' X n g j (sOf σ j) k0}

end

/-- The cone exponent of the class `σ`: `0` if no cone, else `2` (one cone for both twins). -/
def k1Of (σ : Sig1) : ℕ := if σ.1 = 0 ∧ σ.2 = 0 then 0 else 2

/-- The new atoms covering the new edges of the class `σ`. -/
def cov1Of (n : Fin 2 → V) (σ : Sig1) : Finset V :=
  (if σ.1 = 0 then ∅ else {n 0}) ∪ (if σ.2 = 0 then ∅ else {n 1})

theorem card_cov1Of_le (n : Fin 2 → V) (σ : Sig1) : (cov1Of n σ).card ≤ k1Of σ := by
  unfold cov1Of k1Of
  refine (card_union_le _ _).trans ?_
  by_cases h1 : σ.1 = 0 <;> by_cases h2 : σ.2 = 0 <;> simp [h1, h2]

theorem mem_cov1Of (n : Fin 2 → V) {σ : Sig1} {j : Fin 2} (hs : sOf σ j ≠ 0) : n j ∈ cov1Of n σ := by
  unfold cov1Of
  fin_cases j
  · have h1 : σ.1 ≠ 0 := by simpa [sOf] using hs
    simp [h1]
  · have h2 : σ.2 ≠ 0 := by simpa [sOf] using hs
    simp [h2]

theorem k1Of_eq_zero {σ : Sig1} (h : ∀ j, sOf σ j = 0) : k1Of σ = 0 := by
  have h1 : σ.1 = 0 := by simpa [sOf] using h 0
  have h2 : σ.2 = 0 := by simpa [sOf] using h 1
  unfold k1Of; simp [h1, h2]

theorem k1Of_eq_two {σ : Sig1} (h : ∃ j, sOf σ j ≠ 0) : k1Of σ = 2 := by
  obtain ⟨j, hj⟩ := h
  unfold k1Of
  rw [ite_eq_right]
  rintro ⟨h1, h2⟩
  fin_cases j
  · exact hj (by simpa [sOf] using h1)
  · exact hj (by simpa [sOf] using h2)

theorem NCEdge.symm {L γ η : ℝ} {w : Mom d} {h : HSt V D₀} {B : Set (D₀ → (Fin d → ℤ))} {x y : V}
    (hE : NCEdge L γ η w h B x y) : NCEdge L γ η w h B y x := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hE
  obtain ⟨a, ha, hb⟩ := h4
  exact ⟨Ne.symm h1, h3, h2, ⟨h.s.M.mate a, hb, by rw [Molecule.mate_mate]; exact ha⟩,
    fun hT => h5 hT.symm', h7, h6⟩

section cover
variable {L γ η : ℝ} {w : Mom d} {h h' : HSt V D₀} {X : Set V} (n : Fin 2 → V)
  (g : (D₀ → (Fin d → ℤ)) → Mom d)

theorem stat1_exists (hL : 0 < L) (j : Fin 2) (k0 : D₀ → (Fin d → ℤ)) :
    ∃ s, stat1 L γ η w h h' X n g j s k0 := by
  unfold stat1
  by_cases hc : IsCritA L γ η h' (n j)
  · simp only [hc, ite_true]
    by_cases hTR : ∀ y ∈ X, IsCritA L γ η h' y → h'.s.M.Adj (n j) y → TRpt L η (g k0) (gvec h L w k0 y)
    · exact ⟨0, fun _ => hTR, fun i hi => absurd hi (Fin.succ_ne_zero i).symm⟩
    · push Not at hTR
      obtain ⟨y, hyX, hyc, hadj, hnt⟩ := hTR
      obtain ⟨i, hi⟩ := nbrAt_cover hc.2.1 hadj
      refine ⟨i.succ, fun h0 => absurd h0 (Fin.succ_ne_zero i), fun i' hi' => ?_⟩
      have e : i' = i := (Fin.succ_injective _ hi'.symm)
      subst e
      exact ⟨y, hi, hyX, hyc, inCone_of_not_TRpt hL hnt⟩
  · simp only [hc, ite_false]
    exact ⟨0, rfl⟩

/-- **The split classes cover the class.** -/
theorem split1_cover (hL : 0 < L) (B0 : Set (D₀ → (Fin d → ℤ))) :
    B0 ⊆ ⋃ σ : Sig1, split1 L γ η w h h' X n g B0 σ := by
  intro k0 hk0
  obtain ⟨s0, h0⟩ := stat1_exists (h := h) (h' := h') (X := X) (w := w) (γ := γ) n g hL 0 k0
  obtain ⟨s1, h1⟩ := stat1_exists (h := h) (h' := h') (X := X) (w := w) (γ := γ) n g hL 1 k0
  refine Set.mem_iUnion.2 ⟨(s0, s1), hk0, fun j => ?_⟩
  fin_cases j
  · simpa [sOf] using h0
  · simpa [sOf] using h1

variable (F : SurvMap h h' X)
include F

/-- An edge from `n j` to a survivor forces the status of `n j` to be nonzero. -/
theorem sOf_ne_of_edge {σ : Sig1} {B0 B : Set (D₀ → (Fin d → ℤ))} (hB : B ⊆ split1 L γ η w h h' X n g B0 σ)
    (j : Fin 2) (hgv : ∀ k0 ∈ B, IsCritA L γ η h' (n j) →
      gvec h' L w k0 (n j) = g k0 ∨ gvec h' L w k0 (n j) = -g k0)
    {y : V} (hy : y ∈ X) (hE : NCEdge L γ η w h' B (n j) y) : sOf σ j ≠ 0 := by
  intro h0
  obtain ⟨-, hxc, hyc, hadj, hnt, -⟩ := hE
  apply hnt
  intro k0 hk0
  have hs := (hB hk0).2 j
  unfold stat1 at hs
  simp only [hxc, ite_true] at hs
  have := hs.1 h0 y hy hyc hadj
  rw [F.gvec_eq L w k0 hy]
  rcases hgv k0 hk0 hxc with e | e
  · rw [e]; exact this
  · rw [e]; exact this.neg_left

/-- **New edges are covered by `cov1Of n σ`.** -/
theorem edge_cover1 {σ : Sig1} {B0 B : Set (D₀ → (Fin d → ℤ))} (hB : B ⊆ split1 L γ η w h h' X n g B0 σ)
    (hnew : ∀ x, IsCritA L γ η h' x → x ∉ X → ∃ j, x = n j)
    (hgv : ∀ k0 ∈ B, ∀ j, IsCritA L γ η h' (n j) →
      gvec h' L w k0 (n j) = g k0 ∨ gvec h' L w k0 (n j) = -g k0)
    (hpair : NCEdge L γ η w h' B (n 0) (n 1) → n 0 ∈ cov1Of n σ ∨ n 1 ∈ cov1Of n σ)
    (x y : V) (hE : NCEdge L γ η w h' B x y) (hXY : x ∉ X ∨ y ∉ X) : x ∈ cov1Of n σ ∨ y ∈ cov1Of n σ := by
  have newcase : ∀ u v, NCEdge L γ η w h' B u v → u ∉ X → u ∈ cov1Of n σ ∨ v ∈ cov1Of n σ := by
    intro u v huv hu
    obtain ⟨j, rfl⟩ := hnew u huv.2.1 hu
    by_cases hv : v ∈ X
    · exact Or.inl (mem_cov1Of n (sOf_ne_of_edge n g F hB j (fun k0 hk0 => hgv k0 hk0 j) hv huv))
    · obtain ⟨j', rfl⟩ := hnew v huv.2.2.1 hv
      fin_cases j <;> fin_cases j'
      · exact absurd rfl huv.1
      · exact hpair huv
      · exact (hpair huv.symm).symm
      · exact absurd rfl huv.1
  rcases hXY with hx | hy
  · exact newcase x y hE hx
  · exact (newcase y x hE.symm hy).symm

/-- **A cone status on a nonempty class**: `n j` is critical, and there is a critical survivor `y` around whose gap all
gaps `g k0` of the class lie. -/
theorem stat1_cone {σ : Sig1} {B0 B : Set (D₀ → (Fin d → ℤ))} (hB : B ⊆ split1 L γ η w h h' X n g B0 σ)
    (hne : B.Nonempty) (j : Fin 2) (hs : sOf σ j ≠ 0) :
    IsCritA L γ η h' (n j) ∧ ∃ y, y ∈ X ∧ IsCritA L γ η h y ∧
      ∀ k0 ∈ B, InCone (L ^ (-6 * η)) (g k0) (gvec h L w k0 y) := by
  obtain ⟨k1, hk1⟩ := hne
  have hc : IsCritA L γ η h' (n j) := by
    have := (hB hk1).2 j
    unfold stat1 at this
    by_contra hn
    simp only [hn, ite_false] at this
    exact hs this
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, sOf σ j = i.succ := ⟨(sOf σ j).pred hs, (Fin.succ_pred _ hs).symm⟩
  have hget : ∀ k0 ∈ B, ∃ y, nbrAt h' (n j) i = some y ∧ y ∈ X ∧ IsCritA L γ η h' y ∧
      InCone (L ^ (-6 * η)) (g k0) (gvec h L w k0 y) := by
    intro k0 hk0
    have := (hB hk0).2 j
    unfold stat1 at this
    simp only [hc, ite_true] at this
    exact this.2 i hi
  obtain ⟨y, hy1, hyX, hyc, -⟩ := hget k1 hk1
  refine ⟨hc, y, hyX, F.critA hyX hyc, fun k0 hk0 => ?_⟩
  obtain ⟨y', hy1', -, -, hcone⟩ := hget k0 hk0
  rw [hy1] at hy1'
  rw [Option.some.inj hy1']
  exact hcone

end cover

end WaveTurbulence.GammaLow.FinalCount.Ghost
