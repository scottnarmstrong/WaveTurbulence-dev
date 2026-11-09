/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase2B
/-! **Ghost assembly, Phase 2 (C): the (f′) split of a triangle step** (design: `CHAIN-DESIGN.md`).

The class of a node is split by `σ = (s₀, s₁, p) ∈ Fin 3 × Fin 3 × Fin 2` (`splitK = 18` classes): for a critical new
atom `f j`, `s_j = 0` means "transverse to every critical survivor neighbour", `s_j = i + 1` "in the cone around the
neighbour at its `i`-th dart"; `p` is "transverse" / "relative cone" between `f 0` and `f 1`. `kOf σ` is the number of
cones used and `covOf σ` (`|covOf σ| ≤ kOf σ`, `card_covOf_le`) covers every NC edge with a new end (`edge_cover`); the
classes cover the node class (`split_cover`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The gap of the `j`-th cut pair of a triangle under `k0`. -/
noncomputable def gcut (h : HSt V D₀) (T : TriData h.s.M) (L : ℝ) (w : Mom d) (k0 : D₀ → (Fin d → ℤ)) (j : Fin 3) :
    Mom d :=
  Molecule.gapAt L w (k0 ∘ h.s.down) (T.a j) (T.b j)

/-- The split index. -/
abbrev Sig := Fin 3 × Fin 3 × Fin 2

section
variable (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
  (hcl : PClosed T.kept (triKeep h.s T))

/-- The status `s` of the new atom `f j` under `k0`. -/
def statOK (j : Fin 2) (s : Fin 3) (k0 : D₀ → (Fin d → ℤ)) : Prop :=
  if IsCritA L γ η (h.triPost T Q kp hcl) (T.f j.castSucc) then
    (s = 0 → ∀ y ∈ triSurv h T Q kp hcl, IsCritA L γ η (h.triPost T Q kp hcl) y →
        (h.triPost T Q kp hcl).s.M.Adj (T.f j.castSucc) y → TRpt L η (gcut h T L w k0 j.castSucc) (gvec h L w k0 y)) ∧
      (∀ i : Fin 2, s = i.succ → ∃ y, nbrAt (h.triPost T Q kp hcl) (T.f j.castSucc) i = some y ∧
        y ∈ triSurv h T Q kp hcl ∧ IsCritA L γ η (h.triPost T Q kp hcl) y ∧
        InCone (L ^ (-6 * η)) (gcut h T L w k0 j.castSucc) (gvec h L w k0 y))
  else s = 0

/-- The status `p` of the pair `f 0`, `f 1` under `k0`. -/
def pairSt (p : Fin 2) (k0 : D₀ → (Fin d → ℤ)) : Prop :=
  if IsCritA L γ η (h.triPost T Q kp hcl) (T.f 0) ∧ IsCritA L γ η (h.triPost T Q kp hcl) (T.f 1) then
    (p = 0 → TRpt L η (gcut h T L w k0 0) (gcut h T L w k0 1)) ∧
      (p = 1 → InCone (L ^ (-6 * η)) (gcut h T L w k0 1) (gcut h T L w k0 0))
  else p = 0

/-- **The split class `σ`** of a class `B0`. -/
def splitCls (B0 : Set (D₀ → (Fin d → ℤ))) (σ : Sig) : Set (D₀ → (Fin d → ℤ)) :=
  {k0 | k0 ∈ B0 ∧ statOK L γ η w h T Q kp hcl 0 σ.1 k0 ∧ statOK L γ η w h T Q kp hcl 1 σ.2.1 k0 ∧
    pairSt L γ η w h T Q kp hcl σ.2.2 k0}

end

/-- The number of cones used by the class `σ`. -/
def kOf (σ : Sig) : ℕ :=
  (if σ.1 = 0 then 0 else 1) + (if σ.2.1 = 0 then 0 else 1) + (if σ.1 = 0 ∧ σ.2.1 = 0 ∧ σ.2.2 = 1 then 1 else 0)

/-- The new atoms covering the new edges of the class `σ`. -/
def covOf {M : Molecule V D₀} (T : TriData M) (σ : Sig) : Finset V :=
  (if σ.1 = 0 then ∅ else {T.f 0}) ∪ (if σ.2.1 = 0 then ∅ else {T.f 1}) ∪
    (if σ.1 = 0 ∧ σ.2.1 = 0 ∧ σ.2.2 = 1 then {T.f 0} else ∅)

theorem kOf_le_two (σ : Sig) : kOf σ ≤ 2 := by
  unfold kOf; split_ifs <;> simp_all

theorem card_covOf_le {M : Molecule V D₀} (T : TriData M) (σ : Sig) : (covOf T σ).card ≤ kOf σ := by
  unfold covOf kOf
  refine (card_union_le _ _).trans ?_
  refine add_le_add ((card_union_le _ _).trans (add_le_add ?_ ?_)) ?_ <;> split_ifs <;> simp

variable {L γ η : ℝ} {w : Mom d} (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
  (hcl : PClosed T.kept (triKeep h.s T))

theorem statOK_exists (hL : 0 < L) (j : Fin 2) (k0 : D₀ → (Fin d → ℤ)) :
    ∃ s, statOK L γ η w h T Q kp hcl j s k0 := by
  unfold statOK
  by_cases hc : IsCritA L γ η (h.triPost T Q kp hcl) (T.f j.castSucc)
  · simp only [hc, if_true]
    by_cases hTR : ∀ y ∈ triSurv h T Q kp hcl, IsCritA L γ η (h.triPost T Q kp hcl) y →
        (h.triPost T Q kp hcl).s.M.Adj (T.f j.castSucc) y → TRpt L η (gcut h T L w k0 j.castSucc) (gvec h L w k0 y)
    · exact ⟨0, fun _ => hTR, fun i hi => absurd hi (Fin.succ_ne_zero i).symm⟩
    · push Not at hTR
      obtain ⟨y, hyX, hyc, hadj, hnt⟩ := hTR
      obtain ⟨i, hi⟩ := nbrAt_cover hc.2.1 hadj
      refine ⟨i.succ, fun h0 => absurd h0 (Fin.succ_ne_zero i), fun i' hi' => ?_⟩
      have e : i' = i := (Fin.succ_injective _ hi'.symm)
      subst e
      exact ⟨y, hi, hyX, hyc, inCone_of_not_TRpt hL hnt⟩
  · simp only [hc, if_false]
    exact ⟨0, rfl⟩

theorem pairSt_exists (hL : 0 < L) (k0 : D₀ → (Fin d → ℤ)) : ∃ p, pairSt L γ η w h T Q kp hcl p k0 := by
  unfold pairSt
  split_ifs
  · by_cases ht : TRpt L η (gcut h T L w k0 0) (gcut h T L w k0 1)
    · exact ⟨0, fun _ => ht, fun h1 => absurd h1 (by decide)⟩
    · exact ⟨1, fun h0 => absurd h0 (by decide), fun _ => inCone_of_not_TRpt hL (fun ht' => ht ht'.symm |>.elim)⟩
  · exact ⟨0, rfl⟩

/-- **The split classes cover the class.** -/
theorem split_cover (hL : 0 < L) (B0 : Set (D₀ → (Fin d → ℤ))) :
    B0 ⊆ ⋃ σ : Sig, splitCls L γ η w h T Q kp hcl B0 σ := by
  intro k0 hk0
  obtain ⟨s0, h0⟩ := statOK_exists h T Q kp hcl (w := w) (γ := γ) hL 0 k0
  obtain ⟨s1, h1⟩ := statOK_exists h T Q kp hcl (w := w) (γ := γ) hL 1 k0
  obtain ⟨p, hp⟩ := pairSt_exists h T Q kp hcl (w := w) (γ := γ) hL k0
  exact Set.mem_iUnion.2 ⟨(s0, s1, p), hk0, h0, h1, hp⟩

theorem TRon.symm' {L η : ℝ} {w : Mom d} {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {x y : V}
    (hT : TRon L η w h A x y) : TRon L η w h A y x := fun k0 hk => TRpt.symm (hT k0 hk)

theorem f0_mem_covOf {M : Molecule V D₀} (T : TriData M) {σ : Sig} (h0 : σ.1 ≠ 0) : T.f 0 ∈ covOf T σ := by
  unfold covOf; simp [h0]

theorem f1_mem_covOf {M : Molecule V D₀} (T : TriData M) {σ : Sig} (h1 : σ.2.1 ≠ 0) : T.f 1 ∈ covOf T σ := by
  unfold covOf; simp [h1]

theorem f01_mem_covOf {M : Molecule V D₀} (T : TriData M) {σ : Sig} (hp : σ.2.2 = 1) :
    T.f 0 ∈ covOf T σ ∨ T.f 1 ∈ covOf T σ := by
  by_cases h0 : σ.1 = 0
  · by_cases h1 : σ.2.1 = 0
    · left; unfold covOf; simp [h0, h1, hp]
    · exact Or.inr (f1_mem_covOf T h1)
  · exact Or.inl (f0_mem_covOf T h0)

/-- An edge from a new atom `f 0` to a survivor forces `s₀ ≠ 0`. -/
theorem s0_ne_of_edge {σ : Sig} {B0 B : Set (D₀ → (Fin d → ℤ))} (hB : B ⊆ splitCls L γ η w h T Q kp hcl B0 σ)
    {y : V} (hy : y ∈ triSurv h T Q kp hcl) (hE : NCEdge L γ η w (h.triPost T Q kp hcl) B (T.f 0) y) : σ.1 ≠ 0 := by
  intro h0
  obtain ⟨-, hxc, hyc, hadj, hnt, -⟩ := hE
  apply hnt
  intro k0 hk0
  obtain ⟨-, hs0, -⟩ := hB hk0
  unfold statOK at hs0
  simp only [Fin.castSucc_zero, hxc, if_true] at hs0
  have := hs0.1 h0 y hy hyc hadj
  rw [gvec_triPost_f0, (triSurvMap h T Q kp hcl).gvec_eq L w k0 hy]
  exact this

/-- An edge from a new atom `f 1` to a survivor forces `s₁ ≠ 0`. -/
theorem s1_ne_of_edge {σ : Sig} {B0 B : Set (D₀ → (Fin d → ℤ))} (hB : B ⊆ splitCls L γ η w h T Q kp hcl B0 σ)
    {y : V} (hy : y ∈ triSurv h T Q kp hcl) (hE : NCEdge L γ η w (h.triPost T Q kp hcl) B (T.f 1) y) : σ.2.1 ≠ 0 := by
  intro h0
  obtain ⟨-, hxc, hyc, hadj, hnt, -⟩ := hE
  apply hnt
  intro k0 hk0
  obtain ⟨-, -, hs1, -⟩ := hB hk0
  unfold statOK at hs1
  have e : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
  simp only [e, hxc, if_true] at hs1
  have := hs1.1 h0 y hy hyc hadj
  rw [gvec_triPost_f1, (triSurvMap h T Q kp hcl).gvec_eq L w k0 hy]
  exact this

/-- An edge between the two new atoms forces `p = 1`. -/
theorem p_eq_of_edge {σ : Sig} {B0 B : Set (D₀ → (Fin d → ℤ))} (hB : B ⊆ splitCls L γ η w h T Q kp hcl B0 σ)
    (hE : NCEdge L γ η w (h.triPost T Q kp hcl) B (T.f 0) (T.f 1)) : σ.2.2 = 1 := by
  by_contra hp
  have hp0 : σ.2.2 = 0 := by omega
  obtain ⟨-, hxc, hyc, -, hnt, -⟩ := hE
  apply hnt
  intro k0 hk0
  obtain ⟨-, -, -, hps⟩ := hB hk0
  unfold pairSt at hps
  simp only [hxc, hyc, and_self, if_true] at hps
  rw [gvec_triPost_f0, gvec_triPost_f1]
  exact hps.1 hp0

/-- **New edges are covered by `covOf σ`.** -/
theorem edge_cover {σ : Sig} {B0 B : Set (D₀ → (Fin d → ℤ))} (hB : B ⊆ splitCls L γ η w h T Q kp hcl B0 σ)
    (x y : V) (hE : NCEdge L γ η w (h.triPost T Q kp hcl) B x y)
    (hXY : x ∉ triSurv h T Q kp hcl ∨ y ∉ triSurv h T Q kp hcl) : x ∈ covOf T σ ∨ y ∈ covOf T σ := by
  have hsymm : NCEdge L γ η w (h.triPost T Q kp hcl) B y x := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hE
    obtain ⟨a, ha, hb⟩ := h4
    exact ⟨Ne.symm h1, h3, h2, ⟨(h.triPost T Q kp hcl).s.M.mate a, hb, by rw [Molecule.mate_mate]; exact ha⟩,
      fun hT => h5 hT.symm', h7, h6⟩
  -- a new end is `f 0` or `f 1`
  have newcase : ∀ u v, NCEdge L γ η w (h.triPost T Q kp hcl) B u v → u ∉ triSurv h T Q kp hcl →
      u ∈ covOf T σ ∨ v ∈ covOf T σ := by
    intro u v huv hu
    rcases critA_f_cases h T Q kp hcl huv.2.1 hu with rfl | rfl
    · by_cases hv : v ∈ triSurv h T Q kp hcl
      · exact Or.inl (f0_mem_covOf T (s0_ne_of_edge h T Q kp hcl hB hv huv))
      · rcases critA_f_cases h T Q kp hcl huv.2.2.1 hv with rfl | rfl
        · exact absurd rfl huv.1
        · exact f01_mem_covOf T (p_eq_of_edge h T Q kp hcl hB huv)
    · by_cases hv : v ∈ triSurv h T Q kp hcl
      · exact Or.inl (f1_mem_covOf T (s1_ne_of_edge h T Q kp hcl hB hv huv))
      · rcases critA_f_cases h T Q kp hcl huv.2.2.1 hv with rfl | rfl
        · have hE' : NCEdge L γ η w (h.triPost T Q kp hcl) B (T.f 0) (T.f 1) := by
            obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := huv
            obtain ⟨a, ha, hb⟩ := h4
            exact ⟨Ne.symm h1, h3, h2, ⟨(h.triPost T Q kp hcl).s.M.mate a, hb, by rw [Molecule.mate_mate]; exact ha⟩,
              fun hT => h5 hT.symm', h7, h6⟩
          exact (f01_mem_covOf T (p_eq_of_edge h T Q kp hcl hB hE')).symm
        · exact absurd rfl huv.1
  rcases hXY with hx | hy
  · exact newcase x y hE hx
  · exact (newcase y x hsymm hy).symm

end WaveTurbulence.GammaLow.FinalCount.Ghost
