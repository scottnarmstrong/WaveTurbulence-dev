/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCShift
public import WaveTurbulence.Foundations.FinalCount.VCPair
public import WaveTurbulence.Foundations.FinalCount.VCTriple
public import WaveTurbulence.Foundations.FinalCount.VCSpecial2
/-! # VINE-COUNT part 15: the chart coordinates of a decoration are lattice points.

With the anchor `g = w`, each coordinate of the chart is a difference of two origins and equals
`latticePoint L (xint κ i)`, an integer vector built from the labels `κ` of the internal bonds and the integer gap
`rint κ = κ x₁ - κ x₂`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount WaveTurbulence.CountLemmas

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem real_core1 {σ I G β τ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hτ : 0 ≤ τ) (h : -G = 2 * σ * I)
    (hG : |G - β| ≤ τ) : |I - (-σ * β / 2)| ≤ τ := by
  rw [abs_le] at hG ⊢
  rcases hσ with rfl | rfl <;> constructor <;> linarith [hG.1, hG.2]

theorem real_core2 {σ s I G β τ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hs : s = 1 ∨ s = -1) (hτ : 0 ≤ τ)
    (h : -G = 2 * σ * (s * I)) (hG : |G - β| ≤ τ) : |I - (-σ * s * β / 2)| ≤ τ := by
  rw [abs_le] at hG ⊢
  rcases hσ with rfl | rfl <;> rcases hs with rfl | rfl <;> constructor <;> linarith [hG.1, hG.2]

section Coords
variable {M : Molecule V D} (K : VineCut M) (hB : M.IsBlock K.C.atoms K.C.upper K.C.lower) (hMol : M.IsMolecule)
  (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) {X : VineType} (A : FullVineChart M X K.C.atoms K.C.upper K.C.lower)

/-- The integer gap of the removed vine. -/
def rint (κ : D → (Fin d → ℤ)) : Fin d → ℤ := κ K.x₁ - κ K.x₂

theorem gapAt_eq_lattice (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) :
    Molecule.gapAt L w κ K.x₁ K.x₂ = latticePoint L (rint K κ) := by
  unfold Molecule.gapAt Molecule.kvec rint
  rw [latticePoint_sub]; abel

/-- Integer values of the origins `Bond ⊕ Fin 2`. -/
def Oint (κ : D → (Fin d → ℤ)) : Bond M K.C.atoms ⊕ Fin 2 → (Fin d → ℤ)
  | .inl e => κ e.1
  | .inr j => if j = 0 then 0 else -rint K κ

/-- The integer chart coordinates. -/
noncomputable def xint (κ : D → (Fin d → ℤ)) (i : Fin A.indexing.shape.n) : Fin d → ℤ :=
  Oint K κ (pq A i).1 - Oint K κ (pq A i).2

include hB hMol hM

theorem origin_eq (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hdec : M.IsDecoration L w c κ)
    (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) (p : Bond M K.C.atoms ⊕ Fin 2) :
    origin M K.C.atoms (kfibElt K hB hMol hM L w c κ hdec hc).1 w (Molecule.gapAt L w κ K.x₁ K.x₂) p =
      w + latticePoint L (Oint K κ p) := by
  rcases p with e | j
  · simp [origin, kfibElt, Oint, Molecule.kvec]
  · by_cases hj : j = 0
    · simp [origin, Oint, hj, latticePoint_zero]
    · simp [origin, Oint, hj, gapAt_eq_lattice, latticePoint_neg]
      abel

theorem chart_coord_eq (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hdec : M.IsDecoration L w c κ)
    (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) (i : Fin A.indexing.shape.n) :
    A.chart w (Molecule.gapAt L w κ K.x₁ K.x₂) (kfibElt K hB hMol hM L w c κ hdec hc) i =
      latticePoint L (xint K A κ i) := by
  rw [pq_spec A i w _ (kfibElt K hB hMol hM L w c κ hdec hc), origin_eq K hB hMol hM L w c κ hdec hc,
    origin_eq K hB hMol hM L w c κ hdec hc]
  unfold xint
  rw [latticePoint_sub]; abel

omit hB hMol hM in
/-- Centres of the origins. -/
def cenO (w : Mom d) (k0 : D → Mom d) (r₀ : Mom d) : Bond M K.C.atoms ⊕ Fin 2 → Mom d
  | .inl e => k0 e.1 - w
  | .inr j => if j = 0 then 0 else -r₀

omit hB hMol hM in
/-- Centres of the chart coordinates. -/
noncomputable def cenI (w : Mom d) (k0 : D → Mom d) (r₀ : Mom d) (i : Fin A.indexing.shape.n) : Mom d :=
  cenO K w k0 r₀ (pq A i).1 - cenO K w k0 r₀ (pq A i).2

omit hB hMol hM in
theorem near4_xint (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (k0 : D → Mom d) (r₀ : Mom d)
    (hres : ∀ x, ‖Molecule.kvec L w κ x - k0 x‖ ≤ 1) (hball : ‖Molecule.gapAt L w κ K.x₁ K.x₂ - r₀‖ ≤ 2)
    (i : Fin A.indexing.shape.n) : Near4 L (cenI K A w k0 r₀ i) (xint K A κ i) := by
  have hO : ∀ p : Bond M K.C.atoms ⊕ Fin 2, ‖latticePoint L (Oint K κ p) - cenO K w k0 r₀ p‖ ≤ 2 := by
    intro p
    rcases p with e | j
    · simp only [Oint, cenO]
      have := hres e.1
      have e1 : latticePoint L (κ e.1) - (k0 e.1 - w) = Molecule.kvec L w κ e.1 - k0 e.1 := by
        simp [Molecule.kvec]; abel
      rw [e1]; linarith
    · by_cases hj : j = 0
      · simp [Oint, cenO, hj, latticePoint_zero]
      · simp only [Oint, cenO, hj, if_false]
        have e1 : latticePoint L (-rint K κ) - -r₀ = -(Molecule.gapAt L w κ K.x₁ K.x₂ - r₀) := by
          rw [gapAt_eq_lattice, latticePoint_neg]; abel
        rw [e1, norm_neg]; exact hball
  unfold Near4 xint cenI
  rw [latticePoint_sub]
  have : latticePoint L (Oint K κ (pq A i).1) - latticePoint L (Oint K κ (pq A i).2) -
      (cenO K w k0 r₀ (pq A i).1 - cenO K w k0 r₀ (pq A i).2) =
      (latticePoint L (Oint K κ (pq A i).1) - cenO K w k0 r₀ (pq A i).1) -
        (latticePoint L (Oint K κ (pq A i).2) - cenO K w k0 r₀ (pq A i).2) := by abel
  rw [this]
  calc _ ≤ ‖latticePoint L (Oint K κ (pq A i).1) - cenO K w k0 r₀ (pq A i).1‖ +
        ‖latticePoint L (Oint K κ (pq A i).2) - cenO K w k0 r₀ (pq A i).2‖ := norm_sub_le _ _
    _ ≤ 4 := by linarith [hO (pq A i).1, hO (pq A i).2]

omit hB hMol hM in
theorem av_ne_b {i : Fin A.indexing.shape.n} (hi : i ≠ A.indexing.shape.x0) : av A i ≠ K.C.lower := by
  intro h
  exact hi (av_inj A (h.trans (av_x0 A).symm))

omit hB hMol hM in
theorem av_interior {i : Fin A.indexing.shape.n} (hi : i ≠ A.indexing.shape.x0) :
    av A i ∈ K.C.atoms ∧ av A i ≠ K.C.upper ∧ av A i ≠ K.C.lower :=
  ⟨(av_mem A i).1, (av_mem A i).2, av_ne_b K A hi⟩

omit hB hMol hM in
theorem xSlot_ne_x0 (j : Fin A.indexing.shape.m) : A.indexing.shape.xSlot j ≠ A.indexing.shape.x0 := by
  intro h
  have := congrArg Fin.val h
  simp [Shape.xSlot, Shape.x0] at this

omit hB hMol hM in
theorem ySlot_ne_x0 (j : Fin A.indexing.shape.m) : A.indexing.shape.ySlot j ≠ A.indexing.shape.x0 := by
  intro h
  have := congrArg Fin.val h
  simp [Shape.ySlot, Shape.x0] at this

/-- **The two restricted-decoration constraints of one chart rung**, as membership in a `PairSet`. -/
theorem rung_mem_pairSet (L γ δ : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hdec : M.IsDecoration L w c κ) (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) (β : V → ℝ)
    (hres : ∀ v ∈ M.atoms, M.deg v = 4 → |M.Gamma L w κ v - β v| ≤ δ⁻¹ * L ^ (-2 * γ)) (hτ : 0 ≤ δ⁻¹ * L ^ (-2 * γ))
    (k0 : D → Mom d) (r₀ : Mom d) (hk0 : ∀ x, ‖Molecule.kvec L w κ x - k0 x‖ ≤ 1)
    (hball : ‖Molecule.gapAt L w κ K.x₁ K.x₂ - r₀‖ ≤ 2) (j : Fin A.indexing.shape.m) :
    (xint K A κ (A.indexing.shape.xSlot j), xint K A κ (A.indexing.shape.ySlot j)) ∈
      PairSet L (cenI K A w k0 r₀ (A.indexing.shape.xSlot j)) (cenI K A w k0 r₀ (A.indexing.shape.ySlot j))
        (latticePoint L (rint K κ)) (A.ζc j 0) (A.ζc j 1) (β (av A (A.indexing.shape.ySlot j)) / 2)
        (-(A.ζc j 2 : ℝ) * ‖latticePoint L (rint K κ)‖ ^ 2 -
          (β (av A (A.indexing.shape.xSlot j)) + β (av A (A.indexing.shape.ySlot j))) / 2) (δ⁻¹ * L ^ (-2 * γ)) := by
  have hk : ∀ x, κ (M.mate x) = κ x := hdec.1
  have hrl : Molecule.gapAt L w κ K.x₁ K.x₂ = latticePoint L (rint K κ) := gapAt_eq_lattice K L w κ
  have cx := chart_coord_eq K hB hMol hM A L w c κ hdec hc (A.indexing.shape.xSlot j)
  have cy := chart_coord_eq K hB hMol hM A L w c κ hdec hc (A.indexing.shape.ySlot j)
  have ht := A.rung_t_phase d w (Molecule.gapAt L w κ K.x₁ K.x₂)
    (A.chart w (Molecule.gapAt L w κ K.x₁ K.x₂) (kfibElt K hB hMol hM L w c κ hdec hc)) j
  have hs := A.rung_s_phase d w (Molecule.gapAt L w κ K.x₁ K.x₂)
    (A.chart w (Molecule.gapAt L w κ K.x₁ K.x₂) (kfibElt K hB hMol hM L w c κ hdec hc)) j
  rw [Equiv.symm_apply_apply] at ht hs
  unfold nodeResonance at ht hs
  rw [if_neg (xSlot_ne_x0 K A j), add_zero] at ht
  rw [if_neg (ySlot_ne_x0 K A j), add_zero] at hs
  obtain ⟨hmt, hta, htb⟩ := av_interior K A (xSlot_ne_x0 K A j)
  obtain ⟨hms, hsa, hsb⟩ := av_interior K A (ySlot_ne_x0 K A j)
  have et := energy_interior_eq hB hM hmt hta htb L w κ hk
  have es := energy_interior_eq hB hM hms hsa hsb L w κ hk
  have ktf : (kfibElt K hB hMol hM L w c κ hdec hc).1 = fun e : Bond M K.C.atoms => Molecule.kvec L w κ e.1 :=
    funext fun e => kfibElt_val K hB hMol hM L w c κ hdec hc e
  rw [ktf] at ht hs
  change energy M K.C.atoms (fun e : Bond M K.C.atoms => Molecule.kvec L w κ e.1)
    (av A (A.indexing.shape.xSlot j)) = _ at ht
  change energy M K.C.atoms (fun e : Bond M K.C.atoms => Molecule.kvec L w κ e.1)
    (av A (A.indexing.shape.ySlot j)) = _ at hs
  rw [et, cx, cy] at ht
  rw [es, cx, cy] at hs
  rw [hrl] at ht
  have hgt := hres _ (hB.1 hmt) (group_eq_all_of_interior hB hM hmt hta htb).2
  have hgs := hres _ (hB.1 hms) (group_eq_all_of_interior hB hM hms hsa hsb).2
  rw [abs_le] at hgt hgs
  refine ⟨near4_xint K A L w κ k0 r₀ hk0 hball _, near4_xint K A L w κ k0 r₀ hk0 hball _, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith [hgs.1, hgs.2]
  · have hexp : inner ℝ (latticePoint L (rint K κ))
          ((A.ζc j 0 : ℝ) • latticePoint L (xint K A κ (A.indexing.shape.xSlot j)) +
            (A.ζc j 1 : ℝ) • latticePoint L (xint K A κ (A.indexing.shape.ySlot j)) +
            (A.ζc j 2 : ℝ) • latticePoint L (rint K κ)) =
        inner ℝ (latticePoint L (rint K κ))
          ((A.ζc j 0 : ℝ) • latticePoint L (xint K A κ (A.indexing.shape.xSlot j)) +
            (A.ζc j 1 : ℝ) • latticePoint L (xint K A κ (A.indexing.shape.ySlot j))) +
          (A.ζc j 2 : ℝ) * ‖latticePoint L (rint K κ)‖ ^ 2 := by
      rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [hexp] at ht
    rw [abs_le]
    constructor <;> nlinarith [hgs.1, hgs.2, hgt.1, hgt.2]

/-- **The core constraints of a normal vine** as membership in a `TripleSet`. -/
theorem core_mem_tripleSet (hn : X.IsBad = false) (L γ δ : ℝ) (w : Mom d) (c : V → Mom d)
    (κ : D → (Fin d → ℤ)) (hdec : M.IsDecoration L w c κ) (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0)
    (β : V → ℝ) (hres : ∀ v ∈ M.atoms, M.deg v = 4 → |M.Gamma L w κ v - β v| ≤ δ⁻¹ * L ^ (-2 * γ))
    (hτ : 0 ≤ δ⁻¹ * L ^ (-2 * γ)) (k0 : D → Mom d) (r₀ : Mom d)
    (hk0 : ∀ x, ‖Molecule.kvec L w κ x - k0 x‖ ≤ 1) (hball : ‖Molecule.gapAt L w κ K.x₁ K.x₂ - r₀‖ ≤ 2) :
    (xint K A κ (A.indexing.shape.uSlot hn 0), xint K A κ (A.indexing.shape.uSlot hn 1),
      xint K A κ (A.indexing.shape.uSlot hn 2)) ∈
      TripleSet L (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 0)) (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 1))
        (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 2)) A.coreLinear
        (-((A.coreFirstSign : ℤ) : ℝ) * β (av A (A.indexing.shape.uSlot hn 0)) / 2)
        (-((A.coreFirstSign : ℤ) : ℝ) * (if A.coreLinear then 1 else ((A.coreSign : ℤ) : ℝ)) *
          β (av A (A.indexing.shape.uSlot hn 1)) / 2) (δ⁻¹ * L ^ (-2 * γ)) := by
  have hk : ∀ x, κ (M.mate x) = κ x := hdec.1
  have hrl : Molecule.gapAt L w κ K.x₁ K.x₂ = latticePoint L (rint K κ) := gapAt_eq_lattice K L w κ
  have hne : ∀ c' : Fin 3, A.indexing.shape.uSlot hn c' ≠ A.indexing.shape.x0 := by
    intro c' h
    have := congrArg Fin.val h
    simp [Shape.uSlot, Shape.x0] at this
  have cu0 := chart_coord_eq K hB hMol hM A L w c κ hdec hc (A.indexing.shape.uSlot hn 0)
  have cu1 := chart_coord_eq K hB hMol hM A L w c κ hdec hc (A.indexing.shape.uSlot hn 1)
  have cu2 := chart_coord_eq K hB hMol hM A L w c κ hdec hc (A.indexing.shape.uSlot hn 2)
  have h1 := A.core_first_phase hn d w (Molecule.gapAt L w κ K.x₁ K.x₂)
    (A.chart w (Molecule.gapAt L w κ K.x₁ K.x₂) (kfibElt K hB hMol hM L w c κ hdec hc))
  have h2 := A.core_second_phase hn d w (Molecule.gapAt L w κ K.x₁ K.x₂)
    (A.chart w (Molecule.gapAt L w κ K.x₁ K.x₂) (kfibElt K hB hMol hM L w c κ hdec hc))
  rw [Equiv.symm_apply_apply] at h1 h2
  unfold nodeResonance at h1 h2
  rw [if_neg (hne 0), add_zero] at h1
  rw [if_neg (hne 1), add_zero] at h2
  obtain ⟨hm0, ha0, hb0⟩ := av_interior K A (hne 0)
  obtain ⟨hm1, ha1, hb1⟩ := av_interior K A (hne 1)
  have e0 := energy_interior_eq hB hM hm0 ha0 hb0 L w κ hk
  have e1 := energy_interior_eq hB hM hm1 ha1 hb1 L w κ hk
  have ktf : (kfibElt K hB hMol hM L w c κ hdec hc).1 = fun e : Bond M K.C.atoms => Molecule.kvec L w κ e.1 :=
    funext fun e => kfibElt_val K hB hMol hM L w c κ hdec hc e
  rw [ktf] at h1 h2
  change energy M K.C.atoms (fun e : Bond M K.C.atoms => Molecule.kvec L w κ e.1)
    (av A (A.indexing.shape.uSlot hn 0)) = _ at h1
  change energy M K.C.atoms (fun e : Bond M K.C.atoms => Molecule.kvec L w κ e.1)
    (av A (A.indexing.shape.uSlot hn 1)) = _ at h2
  rw [e0, cu0, cu1] at h1
  rw [e1, cu0, cu1, cu2] at h2
  have g0 := hres _ (hB.1 hm0) (group_eq_all_of_interior hB hM hm0 ha0 hb0).2
  have g1 := hres _ (hB.1 hm1) (group_eq_all_of_interior hB hM hm1 ha1 hb1).2
  rw [abs_le] at g0 g1
  have hσ : ((A.coreFirstSign : ℤ) : ℝ) = 1 ∨ ((A.coreFirstSign : ℤ) : ℝ) = -1 := by
    rcases Int.units_eq_one_or A.coreFirstSign with h | h <;> simp [h]
  have hs : ((A.coreSign : ℤ) : ℝ) = 1 ∨ ((A.coreSign : ℤ) : ℝ) = -1 := by
    rcases Int.units_eq_one_or A.coreSign with h | h <;> simp [h]
  refine ⟨near4_xint K A L w κ k0 r₀ hk0 hball _, near4_xint K A L w κ k0 r₀ hk0 hball _,
    near4_xint K A L w κ k0 r₀ hk0 hball _, ?_, ?_⟩
  · exact real_core1 hσ hτ h1 (abs_le.mpr g0)
  · cases hl : A.coreLinear
    · rw [hl] at h2
      simp only [Bool.false_eq_true, if_false] at h2 ⊢
      have hcomm := real_inner_comm (latticePoint L (xint K A κ (A.indexing.shape.uSlot hn 0)) +
            latticePoint L (xint K A κ (A.indexing.shape.uSlot hn 1)) -
            latticePoint L (xint K A κ (A.indexing.shape.uSlot hn 2)))
          (latticePoint L (xint K A κ (A.indexing.shape.uSlot hn 2)))
      rw [hcomm] at h2
      exact real_core2 hσ hs hτ h2 (abs_le.mpr g1)
    · rw [hl] at h2
      simp only [if_true] at h2 ⊢
      have := real_core2 (σ := ((A.coreFirstSign : ℤ) : ℝ)) (s := 1)
        (I := inner ℝ (latticePoint L (xint K A κ (A.indexing.shape.uSlot hn 0)))
          (latticePoint L (xint K A κ (A.indexing.shape.uSlot hn 2)))) hσ (Or.inl rfl) hτ
        (by rw [h2]; ring) (abs_le.mpr g1)
      simpa using this

end Coords

end WaveTurbulence.VineCount
