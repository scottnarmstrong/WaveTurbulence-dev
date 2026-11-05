/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ClassCount
public import WaveTurbulence.Foundations.Spine.FinalArith
/-! # The ladder decay gate (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Sumint Finset

variable {w d : ℕ} {G : Garden w}

namespace LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (C : LadderDarts.Ctx G.molecule u v)

include C in
lemma card_ladderAtoms : (Molecule.ladderAtoms u v).card = 2 * n + 4 := by
  classical
  unfold Molecule.ladderAtoms
  have hd : Disjoint (Finset.univ.image u) (Finset.univ.image v) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hb
    exact C.hne _ _ hj.symm
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ C.huinj,
    Finset.card_image_of_injective _ C.hvinj]
  simp; ring

omit C in
/-- The incoherency counts the end rungs and the interior rungs on different layers. -/
lemma incoh_le (layer : GBranch G.tree → ℕ) :
    sourceLadderIncoherency G layer u v ≤
      (Finset.univ.filter (fun k : Fin n => layer (u (LadderDarts.ir k)) ≠ layer (v (LadderDarts.ir k)))).card + 2 := by
  classical
  unfold sourceLadderIncoherency
  set f : Fin (n + 1 + 1) → ℕ := fun j => if layer (u j) = layer (v j) then 0 else 1 with hf
  have hsub : (Finset.univ : Finset (Fin (n + 1 + 1))) ⊆
      ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1))) ∪
        (Finset.univ.image (LadderDarts.ir (n := n))) := by
    intro j _
    by_cases h0 : j = 0
    · simp [h0]
    · by_cases h1 : j = Fin.last (n + 1)
      · simp [h1]
      · apply Finset.mem_union_right
        have hj0 : j.1 ≠ 0 := fun h => h0 (Fin.ext (by simp [h]))
        have hj1 : j.1 ≠ n + 1 := fun h => h1 (Fin.ext (by simp [h]))
        have hjn := j.2
        refine Finset.mem_image.mpr ⟨⟨j.1 - 1, by omega⟩, Finset.mem_univ _, ?_⟩
        ext
        simp only [LadderDarts.ir]
        omega
  calc ∑ j : Fin (n + 1 + 1), f j ≤ ∑ j ∈ ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1))) ∪
        (Finset.univ.image (LadderDarts.ir (n := n))), f j :=
        Finset.sum_le_sum_of_subset hsub
    _ ≤ ∑ j ∈ ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1))), f j +
        ∑ j ∈ (Finset.univ.image (LadderDarts.ir (n := n))), f j := (by have := Finset.sum_union_inter (s₁ := ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1)))) (s₂ := (Finset.univ.image (LadderDarts.ir (n := n)))) (f := f); omega)
    _ ≤ 2 + (Finset.univ.filter (fun k : Fin n => layer (u (LadderDarts.ir k)) ≠ layer (v (LadderDarts.ir k)))).card := by
        refine add_le_add ?_ ?_
        · calc ∑ j ∈ ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1))), f j ≤
              ∑ _j ∈ ({0, Fin.last (n + 1)} : Finset (Fin (n + 1 + 1))), 1 := Finset.sum_le_sum (fun j _ => by
                simp only [hf]; split_ifs <;> simp)
            _ ≤ 2 := by simp
        · rw [Finset.sum_image (fun a _ b _ h => ir_injective h)]
          rw [Finset.card_filter]
          exact le_of_eq (Finset.sum_congr rfl (fun k _ => by simp only [hf]; split_ifs <;> simp_all))
    _ = _ := by ring

end LadderDarts.Ctx
/-- **The fixed-parameter ladder bound.** -/
theorem ladder_fixed (hd3 : 3 ≤ d) {γ η δ τ x C0 L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (hC0 : 0 ≤ C0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL1 : 1 ≤ L)
    (hRung : ∀ (a b : Fin d → ℝ) (χ : Pt d → ℝ), GoodTerm L (L ^ (1 - γ + η)) a b χ →
      RungOK γ x τ δ L C0 a b χ)
    {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (hlad : G.molecule.IsLadder u v)
    (hP : G.IsPlain) (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    (hlay : ∀ a, δ * ((D.layer a : ℝ) + 1) ≤ τ) (outside : GBranch G.tree → ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (boundary : GardenDart G → (Fin d → ℤ)) :
    ‖sourceLocalLadderKernel G D (Molecule.ladderAtoms u v) outside L γ η δ base roots boundary‖ ≤
      (1 + 9 * (7 ^ d * cellFourierFactor d) ^ 4 * C0 + 3 ^ (16 * d) * (7 ^ d * cellFourierFactor d) ^ 2) *
        ((1 + 9 * (7 ^ d * cellFourierFactor d) ^ 4 * C0 + 3 ^ (16 * d) * (7 ^ d * cellFourierFactor d) ^ 2) *
          δ) ^ (n + 1) *
        L ^ (-x * (sourceLadderIncoherency G D.layer u v : ℝ) + 20 * (d : ℝ)) := by
  classical
  set C := gardenCtx hlad with hC
  have hL0 : 0 < L := by linarith
  by_cases hne : Nonempty ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary)
  swap
  · have hz : ∀ z : ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary), False :=
      fun z => hne ⟨z⟩
    rw [kernel_eq, tsum_eq_sum (s := (∅ : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary)))
      (fun z hz' => (hz z).elim)]
    simp only [Finset.sum_empty, mul_zero, norm_zero]
    positivity
  obtain ⟨z⟩ := hne
  have hn : Mole.RootPairCompatible G (rootVec L base roots) :=
    Mole.rootPairCompatible_of_labels G _ (fun a => base + latticePoint L (z.1.1 a))
      (fun i => by rw [z.1.2.2.1 i]; rfl) (isDecoration_coset L base z.1.2.1).2
  have hρ : 0 ≤ L ^ (-γ + η) := (Real.rpow_pos_of_pos hL0 _).le
  have hR : L * L ^ (-γ + η) ≤ L ^ (1 - γ + η) := by
    have := Real.rpow_add hL0 1 (-γ + η)
    rw [Real.rpow_one] at this
    have e : (1 : ℝ) + (-γ + η) = 1 - γ + η := by ring
    rw [e] at this
    exact le_of_eq this.symm
  set NC : ℕ := ⌈((2 * L + 1) ^ d) ^ 16⌉₊ with hNCdef
  have hNC : ∀ T : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary),
      (∀ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 ≠ 0) →
        (T.image (fun z => LadderDarts.Ctx.clsOf (u := u) (v := v) z.1)).card ≤ NC := by
    intro T hT
    have h1 := C.class_count hP hL0 base D hD γ η roots boundary T hT
    have h2 : (((T.image (fun z => LadderDarts.Ctx.clsOf (u := u) (v := v) z.1)).card : ℕ) : ℝ) ≤ (NC : ℝ) :=
      h1.trans (Nat.le_ceil _)
    exact_mod_cast h2
  have kc := C.kernel_core hP hL0 base roots hn D hD (by omega) γ η δ x τ C0 hδ hC0 hρ hR hRung hlay
    outside boundary NC hNC
  have hcs : (Molecule.ladderAtoms u v).card - 1 = 2 * n + 3 := by
    rw [C.card_ladderAtoms]; omega
  have hcJ : Fintype.card ((Fin 3 × Fin 2) × (Fin 3 × Fin 2)) = 36 := by simp
  have hcoup : ‖(coupling d L γ δ : ℂ)‖ = δ / (2 * L ^ ((d : ℝ) - γ)) := by
    unfold coupling
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hdiff : ∀ a b : ℕ, (((a : ℝ) + 1 ≤ b ∨ (b : ℝ) + 1 ≤ a)) ↔ a ≠ b := by
    intro a b
    constructor
    · rintro (h | h) hab <;> subst hab <;> linarith
    · intro hab
      rcases lt_or_gt_of_ne hab with h | h
      · left; exact_mod_cast Nat.succ_le_of_lt h
      · right; exact_mod_cast Nat.succ_le_of_lt h
  rw [hcs, hcJ, card_code, hcoup] at kc
  have hprod := prod_rungBudget (n := n)
    (fun k => ((D.layer (u (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (v (LadderDarts.ir k)) ∨
      (D.layer (v (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (u (LadderDarts.ir k)))) d γ x δ L C0
  rw [hprod] at kc
  have hfilt : (Finset.univ.filter (fun k : Fin n =>
        ((D.layer (u (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (v (LadderDarts.ir k)) ∨
          (D.layer (v (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (u (LadderDarts.ir k))))) =
      Finset.univ.filter (fun k : Fin n => D.layer (u (LadderDarts.ir k)) ≠ D.layer (v (LadderDarts.ir k))) :=
    Finset.filter_congr (fun k _ => hdiff _ _)
  rw [hfilt] at kc
  have hinc := LadderDarts.Ctx.incoh_le (u := u) (v := v) D.layer
  have hNCle : (NC : ℝ) ≤ 2 * (3 * L) ^ (16 * d) := by
    have h1 : ((2 * L + 1) ^ d) ^ 16 ≤ (3 * L) ^ (16 * d) := by
      rw [← pow_mul, mul_comm d 16]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have h2 : (1 : ℝ) ≤ ((2 * L + 1) ^ d) ^ 16 := one_le_pow₀ (one_le_pow₀ (by linarith))
    have h3 := Nat.ceil_lt_add_one (a := ((2 * L + 1) ^ d) ^ 16) (by positivity)
    linarith
  exact final_bound hd3 hγ0 hγ1 hL1 hδ hδ1 hx0 hx1 hC0
    (by have := cellFourierFactor_nonneg d; positivity) hinc (Nat.cast_nonneg _) hNCle kc

/-- TARGET (redladder2), verbatim copy of the pinned `LadderDecayAt` (SourceLadderDecayInput.lean,
sha256 14bbd832...; the exact-type check against the pinned file is deferred to the port because
the scratch environments of the pinned input and of the Sumint scratch clash). -/
abbrev LadderDecayAtCopy (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ D : SplicedKernelData G P.d, SplicedAmplitudeBounds G D → (∀ v, D.layer v ≤ p) →
  ∀ (m : ℕ) (u v : Fin (m + 1) → GBranch G.tree), 1 ≤ m → G.molecule.IsLadder u v →
    Disjoint (Molecule.ladderAtoms u v) D.hinges →
  ∀ (outside : GBranch G.tree → ℝ), (∀ a, a ∉ Molecule.ladderAtoms u v → outside a ∈ Set.Icc (D.layer a : ℝ) (D.layer a + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (boundary : GardenDart G → (Fin P.d → ℤ)),
    ‖sourceLocalLadderKernel G D (Molecule.ladderAtoms u v) outside P.L P.γ P.η P.δ base roots boundary‖ ≤
      P.C₁ * (P.C₁ * P.δ) ^ m *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * sourceLadderIncoherency G D.layer u v + 20 * P.d)

open Set in
/-- **The ladder decay gate** (TARGET redladder2). -/
theorem ladderDecayGate : WTPrefix LadderDecayAtCopy := by
  intro d hd γ hγ
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1
  have hg1pos : 0 < g1 := by
    simp only [hg1]
    refine lt_min (by linarith) (lt_min one_pos ?_)
    nlinarith
  set η₀ : ℝ := min (min γ (1 - γ) / (10 * d)) ((g1 / 2) ^ 2) with hη₀
  have hη₀pos : 0 < η₀ := by
    refine lt_min ?_ (by positivity)
    apply div_pos (lt_min hγ0 (by linarith)) (by positivity)
  refine ⟨η₀, hη₀pos, ?_⟩
  intro η hη φin hφin τ hτ φ hφ
  obtain ⟨hη0, hηle⟩ := hη
  have hη1 : 10 * (d : ℝ) * η ≤ γ := by
    have h1 : η ≤ min γ (1 - γ) / (10 * d) := hηle.trans (min_le_left _ _)
    have h2 : 10 * (d : ℝ) * η ≤ min γ (1 - γ) := by
      rw [le_div_iff₀ (by positivity)] at h1; linarith
    exact h2.trans (min_le_left _ _)
  have hη2 : 10 * (d : ℝ) * η ≤ 1 - γ := by
    have h1 : η ≤ min γ (1 - γ) / (10 * d) := hηle.trans (min_le_left _ _)
    have h2 : 10 * (d : ℝ) * η ≤ min γ (1 - γ) := by
      rw [le_div_iff₀ (by positivity)] at h1; linarith
    exact h2.trans (min_le_right _ _)
  have hη1' : η ≤ 1 := by nlinarith
  have hsq : Real.sqrt η ≤ g1 / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    exact hηle.trans (min_le_right _ _)
  have hsqpos : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη0
  have hηsq : η ≤ Real.sqrt η := by
    have := Real.sqrt_le_sqrt hη1'
    nlinarith [Real.sq_sqrt hη0.le, Real.sqrt_nonneg η]
  set x : ℝ := g1 - Real.sqrt η with hx
  have hx0 : 0 ≤ x := by linarith
  have hx1 : x < 2 * γ := by
    have : g1 ≤ 2 * γ := min_le_left _ _
    linarith
  have hx2 : x ≤ 1 := by
    have : g1 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hx3 : -2 * ((d : ℝ) - 1) * (1 - γ) + η ≤ -x := by
    have : g1 ≤ 2 * ((d : ℝ) - 1) * (1 - γ) := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  obtain ⟨C0, hC0, hrt⟩ := rung_total hd ⟨hγ0, hγ1⟩ hη0 hη1 hη2 hτ hx1 hx2 hx3
  set M : ℝ := 7 ^ d * cellFourierFactor d with hM
  set C1 : ℝ := 1 + 9 * M ^ 4 * C0 + 3 ^ (16 * d) * M ^ 2 with hC1
  have hMn : 0 ≤ M := by have := cellFourierFactor_nonneg d; positivity
  have hC1ge : 1 ≤ C1 := by
    have : 0 ≤ 9 * M ^ 4 * C0 := by positivity
    have : 0 ≤ 3 ^ (16 * d) * M ^ 2 := by positivity
    linarith
  refine ⟨C1, hC1ge, 1, one_pos, ?_⟩
  intro ν hν
  refine ⟨1, one_pos, ?_⟩
  intro δ hδ D hD hτD
  obtain ⟨L1, hL1, hL1'⟩ := hrt δ hδ.1 hδ.2
  refine ⟨1, le_rfl, max 2 L1, le_max_left _ _, ?_⟩
  intro L hL
  have hLL1 : L1 ≤ L := (le_max_right _ _).trans hL
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  intro p hpD R hR1 hR2 G hplain hirr hbal hord1 hord2 Dd hDd hlayers m u v hm hlad hdisj outside houtside
    base roots boundary
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hlay : ∀ a, δ * ((Dd.layer a : ℝ) + 1) ≤ τ := by
    intro a
    have hpD' : p < D := hpD
    have h1 : Dd.layer a + 1 ≤ D := by have := hlayers a; omega
    have h2 : ((Dd.layer a : ℝ) + 1) ≤ (D : ℝ) := by exact_mod_cast h1
    rw [hτD]; nlinarith [hδ.1]
  have := ladder_fixed (G := G) hd (γ := γ) (η := η) (δ := δ) (τ := τ) (x := x) (C0 := C0) (L := L)
    hγ0 hγ1 hx0 hx2 hC0 hδ.1 hδ.2 (by linarith) (hL1' L hLL1) hlad hplain Dd hDd hlay outside base roots boundary
  exact this

end WaveTurbulence.LadderDecay
