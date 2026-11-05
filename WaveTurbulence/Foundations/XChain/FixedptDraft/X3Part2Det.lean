/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3KerMeas
public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3TimeSup

/-!
# X3 Part2Det: the event of Part 2 and the deterministic kernel bound

Fix a kind, `ζ`, and parameters `π` (`P2Par`): `q > 1`, the total threshold `B ≥ 0`, an exponent `A`, the time-sup
parameters `(J_A, h_A)` and `(J_B(j₂), h_B(j₂))`, and weights `v(j₂) ≥ 0` with `∑ v ≤ 1`. Write `M₁ = 2^{j₁} L`,
`M₂ = 2^{j₂} L`, and `w(k, k') = ⟨k/L − ζ k'/L⟩^{−A}`. Write `Φ[K, K']` for the time-sup functional of
`X3-TimeSup` on `(p, p+1)`, applied to the masked kernels `Kpl`, `Kdr` of `X3-KerMeas`.

The test sets:
* regime A (`|k| ≤ M₁^{10}`): `testA j₁ = ballZ L (M₁^{10})`;
* regime B (`|k| ≥ M₁^{10}`): the `†` box `dagBox L (ℓ_max M₁)` (labels with `|w_m/L| ≤ ℓ_max M₁`), and
  `testB j₁ j₂ = {M₁^{10} ≤ |k| ≤ R} ∪ Rep`. Here `Rep` is the `finitelem` set of `{|k| ≥ max(M₁^{10}, R)}` at
  radius `M_rep = M₂ + 4B₀² + 2B₀`, with `R`, `B₀` as in `Kpl_shift`.

The event `part2Event` is the set of data `b` such that:
* for all `j₁`, `k ∈ testA j₁` and `k'`: `Φ[𝒦^{j₁}_b(·,·,k,k')] ≤ B 2^{−(j₁+1)} w(k,k')`;
* for all `j₁, j₂`, `x ∈ dagBox`, `k ∈ testB j₁ j₂` and `k'`:
  `Φ[𝒦^{j₁ j₂ †x}_b(·,·,k,k')] ≤ B 2^{−(j₁+1)} v(j₂) / |dagBox| · w(k,k')`.

**Statement.**
1. (`measurableSet_part2Event`) The event is measurable.
2. (`mul_phase_mem_part2Event`) The event is stable under cubic phases.
3. (`lintegral_Kpl_le`) For summable `b` in the event, `t ∈ [p, p+1]` and all `k, k'`:
   `∫_p^t ‖𝒦^{plain}_b(t, s, k, k')‖ ds ≤ B w(k, k')`.

**Proof of 3.**
- Split `𝒦 = ∑_{j₁} 𝒦^{j₁}` (the `M₁` dyadics).
- If `|k| ≤ M₁^{10}`, apply `timeSup_le`.
- Otherwise:
  - split `𝒦^{j₁} = ∑_{j₂} 𝒦^{j₁ j₂}` (the `M₂` dyadics);
  - expand `𝒦^{j₁ j₂} = ∑_x e^{iθ_x s} 𝒦^{j₁ j₂ †x}` (the `†` expansion), where only `x ∈ dagBox` contribute;
  - move `k` to its representative `k_* ∈ testB j₁ j₂` (`Kpl_shift`). This keeps `k − ζk'`.
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI FTree
open scoped ENNReal

variable {d : ℕ}

/-! ## Weights, functional, test sets -/

/-- `w(k, k') = ⟨k/L − ζ k'/L⟩^{−A}`. -/
noncomputable def wtm (L : ℝ) (ζ : ℤˣ) (A : ℝ) (k k' : Fin d → ℤ) : ℝ :=
  jbr (latticePoint L k - (ζ : ℤ) • latticePoint L k') ^ (-A)

theorem wtm_nonneg (L : ℝ) (ζ : ℤˣ) (A : ℝ) (k k' : Fin d → ℤ) : 0 ≤ wtm L ζ A k k' :=
  Real.rpow_nonneg (Real.sqrt_nonneg _) _

/-- `w` depends on `k − ζk'` only. -/
theorem wtm_shift (L : ℝ) (ζ : ℤˣ) (A : ℝ) (k k₀ k' : Fin d → ℤ) :
    wtm L ζ A k₀ (k' - (ζ : ℤ) • (k - k₀)) = wtm L ζ A k k' := by
  unfold wtm
  congr 2
  rw [latticePoint_sub, latticePoint_zsmul, latticePoint_sub]
  rcases Int.units_eq_one_or ζ with h | h <;>
    simp only [h, Units.val_one, Units.val_neg, one_smul, neg_smul, smul_sub, smul_neg, neg_neg] <;> abel

/-- The time-sup functional on `(p, p+1)`. -/
noncomputable def PhiT (p : ℕ) (q h : ℝ) (J : ℕ) (K K' : ℝ → ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ s in Ioo (p : ℝ) (p + 1), timeSupIntegrand p h q J K K' s

theorem measurable_PhiT {α : Type*} [MeasurableSpace α] (p : ℕ) (q h : ℝ) (J : ℕ)
    {K K' : α → ℝ → ℝ → ℂ} (hKm : Measurable fun z : α × ℝ × ℝ => K z.1 z.2.1 z.2.2)
    (hK'm : Measurable fun z : α × ℝ × ℝ => K' z.1 z.2.1 z.2.2) :
    Measurable fun a => PhiT p q h J (K a) (K' a) := by
  have hB := measurable_timeSupB (a := (p : ℝ)) (q := q) hK'm
  have hKj := fun j : Fin J => measurable_timeSupK (a := (p : ℝ)) hKm j
  have hT : Measurable fun z : α × ℝ => timeSupIntegrand p h q J (K z.1) (K' z.1) z.2 := by
    unfold timeSupIntegrand
    exact (Finset.measurable_sum _ fun j _ => hKj j).add (measurable_const.mul (hB.pow_const _))
  exact hT.lintegral_prod_right'

/-- The regime-A test set `ballZ L (M₁^{10})`. -/
noncomputable def testA (L : ℝ) (j : ℕ) : Finset (Fin d → ℤ) := ballZ L ((2 ^ j * L) ^ 10)

/-- The `†` box: labels `x = (i, w)` with `|w_m/L| ≤ R` for `m ≠ i`. -/
noncomputable def dagBox (L R : ℝ) : Finset (DagIdx d) :=
  Finset.univ.sigma fun i =>
    (Fintype.piFinset fun m : Fin 3 => if m = i then ({0} : Finset (Fin d → ℤ)) else ballZ L R).subtype
      (fun w => w i = 0)

theorem dagBox_spec {L R : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (x : DagIdx d) :
    x ∈ dagBox L R ∨ ∃ m, m ≠ x.1 ∧ R < ‖latticePoint L (x.2.1 m)‖ := by
  by_cases h : ∃ m, m ≠ x.1 ∧ R < ‖latticePoint L (x.2.1 m)‖
  · exact Or.inr h
  left
  push Not at h
  obtain ⟨i, w, hw⟩ := x
  simp only [dagBox, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_subtype,
    Fintype.mem_piFinset]
  intro m
  by_cases hm : m = i
  · subst hm
    simp [hw]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm), mem_ballZ hL hR]
    exact h m hm

/-- The `finitelem` representatives (`∅` in the degenerate case). -/
noncomputable def repSet (L M : ℝ) (S : Set (Fin d → ℤ)) : Finset (Fin d → ℤ) :=
  if h : 1 ≤ L ∧ 0 ≤ M then Classical.choose (finitelem h.1 h.2 S) else ∅

theorem repSet_spec {L M : ℝ} (hL : 1 ≤ L) (hM : 0 ≤ M) (S : Set (Fin d → ℤ)) :
    (↑(repSet L M S) : Set (Fin d → ℤ)) ⊆ S ∧
      (repSet L M S).card ≤ (d + 1) * ((2 * ⌊L * M⌋₊ + 1) ^ d * (2 * ⌊L ^ 2 * M⌋₊ + 1)) ^ d ∧
      ∀ k ∈ S, ∃ k' ∈ repSet L M S, ∀ z : Fin d → ℤ, ‖latticePoint L z‖ ≤ M →
        (|ipL L k z| ≤ M ↔ |ipL L k' z| ≤ M) ∧ (|ipL L k z| ≤ M → ipL L k z = ipL L k' z) := by
  have h : 1 ≤ L ∧ 0 ≤ M := ⟨hL, hM⟩
  unfold repSet
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact Classical.choose_spec (finitelem h.1 h.2 S)

section Test

variable (L γ δ : ℝ) (p Ntr : ℕ) (kind : FlowerKind) (ζ : ℤˣ)

/-- The radius of the representatives, `M_rep = M₂ + 4B₀² + 2B₀`. -/
noncomputable def Mrep (j₁ j₂ : ℕ) : ℝ := 2 ^ j₂ * L + 4 * kerB0K L Ntr kind j₁ ^ 2 + 2 * kerB0K L Ntr kind j₁

/-- The set represented in regime B. -/
def repDom (j₁ j₂ : ℕ) : Set (Fin d → ℤ) :=
  {k | (2 ^ j₁ * L) ^ 10 ≤ ‖latticePoint L k‖ ∧ kerRK L Ntr kind j₁ j₂ ≤ ‖latticePoint L k‖}

/-- The regime-B test set `{M₁^{10} ≤ |k| ≤ R} ∪ Rep`. -/
noncomputable def testB (j₁ j₂ : ℕ) : Finset (Fin d → ℤ) :=
  ((ballZ L (kerRK L Ntr kind j₁ j₂)).filter fun k => (2 ^ j₁ * L) ^ 10 ≤ ‖latticePoint L k‖) ∪
    repSet L (Mrep L Ntr kind j₁ j₂) (repDom L Ntr kind j₁ j₂)

theorem kerB0K_nonneg (hL : 0 < L) (j₁ : ℕ) : 0 ≤ kerB0K L Ntr kind j₁ := by
  unfold kerB0K; positivity

theorem kerRK_nonneg (hL : 0 < L) (j₁ j₂ : ℕ) : 0 ≤ kerRK L Ntr kind j₁ j₂ := by
  unfold kerRK
  have := kerB0K_nonneg L Ntr kind hL j₁
  positivity

theorem Mrep_nonneg (hL : 0 < L) (j₁ j₂ : ℕ) : 0 ≤ Mrep L Ntr kind j₁ j₂ := by
  unfold Mrep
  have := kerB0K_nonneg L Ntr kind hL j₁
  positivity

/-- **Every regime-B mode has a test representative** with the same kernels, up to `k' ↦ k' − ζ(k − k_*)`. -/
theorem testB_spec (hL : 1 ≤ L) (j₁ j₂ : ℕ) {k : Fin d → ℤ} (hk : (2 ^ j₁ * L) ^ 10 ≤ ‖latticePoint L k‖) :
    ∃ k₀ ∈ testB L Ntr kind j₁ j₂, (2 ^ j₁ * L) ^ 10 ≤ ‖latticePoint L k₀‖ ∧
      ∀ (c : Fin 3 → Mom d) (b : (Fin d → ℤ) → ℂ) (t s : ℝ) (k' : Fin d → ℤ),
        Kpl L γ δ p Ntr kind (some c) (some j₁) (some j₂) ζ k k' b t s =
          Kpl L γ δ p Ntr kind (some c) (some j₁) (some j₂) ζ k₀ (k' - (ζ : ℤ) • (k - k₀)) b t s := by
  have hL0 : 0 < L := by linarith
  have hR0 := kerRK_nonneg L Ntr kind hL0 j₁ j₂
  have hB0 := kerB0K_nonneg L Ntr kind hL0 j₁
  have hM2 : (0 : ℝ) ≤ 2 ^ j₂ * L := by positivity
  by_cases hR : ‖latticePoint L k‖ ≤ kerRK L Ntr kind j₁ j₂
  · refine ⟨k, Finset.mem_union_left _ (Finset.mem_filter.2 ⟨(mem_ballZ hL0 hR0).2 hR, hk⟩), hk,
      fun c b t s k' => ?_⟩
    simp
  · push Not at hR
    obtain ⟨hsub, -, hrep⟩ := repSet_spec hL (Mrep_nonneg L Ntr kind hL0 j₁ j₂) (repDom L Ntr kind j₁ j₂)
    obtain ⟨k₀, hk₀, hrk⟩ := hrep k ⟨hk, hR.le⟩
    have hk₀S : k₀ ∈ repDom L Ntr kind j₁ j₂ := hsub hk₀
    refine ⟨k₀, Finset.mem_union_right _ hk₀, hk₀S.1, fun c b t s k' => ?_⟩
    have e : k₀ + (k - k₀) = k := by abel
    have e' : k' - (ζ : ℤ) • (k - k₀) + (ζ : ℤ) • (k - k₀) = k' := by abel
    have hrep' : ∀ z : Fin d → ℤ, ‖latticePoint L z‖ ≤ Mrep L Ntr kind j₁ j₂ →
        (|ipL L k₀ z| ≤ Mrep L Ntr kind j₁ j₂ ↔ |ipL L (k₀ + (k - k₀)) z| ≤ Mrep L Ntr kind j₁ j₂) ∧
        (|ipL L k₀ z| ≤ Mrep L Ntr kind j₁ j₂ → ipL L k₀ z = ipL L (k₀ + (k - k₀)) z) := by
      intro z hz
      rw [e]
      obtain ⟨h1, h2⟩ := hrk z hz
      exact ⟨h1.symm, fun h => (h2 (h1.2 h)).symm⟩
    have hsh := Kpl_shift L γ δ p Ntr kind ζ k₀ (k' - (ζ : ℤ) • (k - k₀)) hL0 c j₁ j₂ b t s
      (D := k - k₀) (M := Mrep L Ntr kind j₁ j₂) hk₀S.2 (by rw [e]; exact hR.le)
      (by unfold Mrep; nlinarith) (by unfold Mrep; nlinarith) hrep'
    rw [e, e'] at hsh
    exact hsh

end Test

/-! ## The event -/

/-- The parameters of the Part 2 event. -/
structure P2Par where
  /-- the moment exponent `q = 2P` -/
  q : ℝ
  /-- the kernel decay exponent -/
  A : ℝ
  /-- the total threshold -/
  B : ℝ
  /-- regime A: grid size -/
  JA : ℕ
  /-- regime A: window -/
  hA : ℝ
  /-- regime B: grid size -/
  JB : ℕ → ℕ
  /-- regime B: window -/
  hB : ℕ → ℝ
  /-- regime B: the weights of the `M₂` dyadics -/
  v : ℕ → ℝ

/-- The conditions on the parameters. -/
structure P2Par.Valid (π : P2Par) : Prop where
  hq : 1 < π.q
  hB : 0 ≤ π.B
  hJA : 1 ≤ π.JA
  hJhA : 1 ≤ ((π.JA : ℝ) + 1) * π.hA
  hJB : ∀ j, 1 ≤ π.JB j
  hJhB : ∀ j, 1 ≤ ((π.JB j : ℝ) + 1) * π.hB j
  hv0 : ∀ j, 0 ≤ π.v j
  hv : Summable π.v
  hv1 : ∑' j, π.v j ≤ 1

section Event

variable (L γ δ : ℝ) (p Ntr : ℕ) (kind : FlowerKind) (ζ : ℤˣ) (π : P2Par)

/-- The functional of regime A. -/
noncomputable def PhiA (j : ℕ) (k k' : Fin d → ℤ) (b : (Fin d → ℤ) → ℂ) : ℝ≥0∞ :=
  PhiT p π.q π.hA π.JA (Kpl L γ δ p Ntr kind none (some j) none ζ k k' b)
    (Kdr L γ δ p Ntr kind none (some j) none ζ k k' b)

/-- The functional of regime B. -/
noncomputable def PhiB (j₁ j₂ : ℕ) (x : DagIdx d) (k k' : Fin d → ℤ) (b : (Fin d → ℤ) → ℂ) : ℝ≥0∞ :=
  PhiT p π.q (π.hB j₂) (π.JB j₂) (Kpl L γ δ p Ntr kind (some (dagLabel L x)) (some j₁) (some j₂) ζ k k' b)
    (Kdr L γ δ p Ntr kind (some (dagLabel L x)) (some j₁) (some j₂) ζ k k' b)

/-- The `†` box of the kind at `M₁ = 2^{j₁} L`. -/
noncomputable def dagBoxK (j₁ : ℕ) : Finset (DagIdx d) := dagBox L ((leafMax Ntr kind : ℝ) * (2 ^ j₁ * L))

/-- The threshold of regime A. -/
noncomputable def lamA (j : ℕ) (k k' : Fin d → ℤ) : ℝ := π.B * (2 ^ (j + 1))⁻¹ * wtm L ζ π.A k k'

/-- The threshold of regime B. -/
noncomputable def lamB (j₁ j₂ : ℕ) (k k' : Fin d → ℤ) : ℝ :=
  π.B * (2 ^ (j₁ + 1))⁻¹ * (π.v j₂ / ((dagBoxK (d := d) L Ntr kind j₁).card : ℝ)) * wtm L ζ π.A k k'

/-- **The event of Part 2** for one kind and one `ζ`. -/
def part2Event : Set ((Fin d → ℤ) → ℂ) :=
  {b | (∀ j, ∀ k ∈ testA L j, ∀ k', PhiA L γ δ p Ntr kind ζ π j k k' b ≤ ENNReal.ofReal (lamA L ζ π j k k')) ∧
    ∀ j₁ j₂, ∀ x ∈ dagBoxK L Ntr kind j₁, ∀ k ∈ testB L Ntr kind j₁ j₂, ∀ k',
      PhiB L γ δ p Ntr kind ζ π j₁ j₂ x k k' b ≤ ENNReal.ofReal (lamB L Ntr kind ζ π j₁ j₂ k k')}

theorem measurable_Kpl_fst (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (k k' : Fin d → ℤ) :
    Measurable fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ => Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k' z.1 z.2.1 z.2.2 :=
  (stronglyMeasurable_Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k').measurable

theorem measurable_Kdr_fst (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (k k' : Fin d → ℤ) :
    Measurable fun z : ((Fin d → ℤ) → ℂ) × ℝ × ℝ => Kdr L γ δ p Ntr kind dagger cut1 cut2 ζ k k' z.1 z.2.1 z.2.2 :=
  (stronglyMeasurable_Kdr L γ δ p Ntr kind dagger cut1 cut2 ζ k k').measurable

theorem measurable_PhiA (j : ℕ) (k k' : Fin d → ℤ) : Measurable (PhiA L γ δ p Ntr kind ζ π j k k') :=
  measurable_PhiT p π.q π.hA π.JA (measurable_Kpl_fst L γ δ p Ntr kind ζ _ _ _ k k')
    (measurable_Kdr_fst L γ δ p Ntr kind ζ _ _ _ k k')

theorem measurable_PhiB (j₁ j₂ : ℕ) (x : DagIdx d) (k k' : Fin d → ℤ) :
    Measurable (PhiB L γ δ p Ntr kind ζ π j₁ j₂ x k k') :=
  measurable_PhiT p π.q (π.hB j₂) (π.JB j₂) (measurable_Kpl_fst L γ δ p Ntr kind ζ _ _ _ k k')
    (measurable_Kdr_fst L γ δ p Ntr kind ζ _ _ _ k k')

/-- **1. The event is measurable.** -/
theorem measurableSet_part2Event : MeasurableSet (part2Event (d := d) L γ δ p Ntr kind ζ π) := by
  simp only [part2Event, ofPred_and, ofPred_forall]
  refine (MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun k' => measurableSet_le (measurable_PhiA L γ δ p Ntr kind ζ π j k k')
      measurable_const).inter
    (MeasurableSet.iInter fun j₁ => MeasurableSet.iInter fun j₂ => MeasurableSet.iInter fun x =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
        MeasurableSet.iInter fun k' => measurableSet_le (measurable_PhiB L γ δ p Ntr kind ζ π j₁ j₂ x k k')
          measurable_const)

theorem PhiT_mul_phase {φ : (Fin d → ℤ) → ℂ} (hφ : IsCubicPhase φ) (dagger : Option (Fin 3 → Mom d))
    (cut1 cut2 : Option ℕ) (q h : ℝ) (J : ℕ) (k k' : Fin d → ℤ) (b : (Fin d → ℤ) → ℂ) :
    PhiT p q h J (Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k' fun m => φ m * b m)
        (Kdr L γ δ p Ntr kind dagger cut1 cut2 ζ k k' fun m => φ m * b m) =
      PhiT p q h J (Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b)
        (Kdr L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b) := by
  simp only [PhiT, timeSupIntegrand, enorm_Kpl_mul_phase L γ δ p Ntr kind dagger cut1 cut2 ζ k k' hφ,
    enorm_Kdr_mul_phase L γ δ p Ntr kind dagger cut1 cut2 ζ k k' hφ]

/-- **2. The event is stable under cubic phases.** -/
theorem mul_phase_mem_part2Event {φ : (Fin d → ℤ) → ℂ} (hφ : IsCubicPhase φ) {b : (Fin d → ℤ) → ℂ}
    (hb : b ∈ part2Event L γ δ p Ntr kind ζ π) :
    (fun m => φ m * b m) ∈ part2Event L γ δ p Ntr kind ζ π := by
  refine ⟨fun j k hk k' => ?_, fun j₁ j₂ x hx k hk k' => ?_⟩
  · unfold PhiA
    rw [PhiT_mul_phase L γ δ p Ntr kind ζ hφ]
    exact hb.1 j k hk k'
  · unfold PhiB
    rw [PhiT_mul_phase L γ δ p Ntr kind ζ hφ]
    exact hb.2 j₁ j₂ x hx k hk k'

end Event

/-! ## The deterministic kernel bound -/

section Det

variable (L γ δ : ℝ) (p Ntr : ℕ) (kind : FlowerKind) (ζ : ℤˣ) (π : P2Par)

theorem measurable_Kpl_slice (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (k k' : Fin d → ℤ)
    (b : (Fin d → ℤ) → ℂ) (t : ℝ) :
    Measurable fun s => Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b t s :=
  (measurable_Kpl_fst L γ δ p Ntr kind ζ dagger cut1 cut2 k k').comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

theorem measurable_Kdr_slice (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (k k' : Fin d → ℤ)
    (b : (Fin d → ℤ) → ℂ) (s : ℝ) :
    Measurable fun u => Kdr L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b u s :=
  (measurable_Kdr_fst L γ δ p Ntr kind ζ dagger cut1 cut2 k k').comp
    (measurable_const.prodMk (measurable_id.prodMk measurable_const))

/-- One piece: `∫_p^t ‖K(t, s)‖ ≤ Φ[K, K']`, by `timeSup_le` and the masked FTC. -/
theorem lintegral_piece_le (hπ : π.Valid) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖)
    (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (h : ℝ) (J : ℕ) (hJ : 1 ≤ J)
    (hJh : 1 ≤ ((J : ℝ) + 1) * h) (k k' : Fin d → ℤ) {t : ℝ} (ht : t ∈ Icc (p : ℝ) (p + 1)) :
    ∫⁻ s in Ioo (p : ℝ) t, ‖Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b t s‖ₑ ≤
      PhiT p π.q h J (Kpl L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b)
        (Kdr L γ δ p Ntr kind dagger cut1 cut2 ζ k k' b) :=
  timeSup_le hJ hJh hπ.hq (fun _s hs _t₀ ht₀ _t ht => Kpl_FTC L γ δ p Ntr kind dagger cut1 cut2 ζ k k' hb hs ht₀ ht)
    (fun s => measurable_Kdr_slice L γ δ p Ntr kind ζ dagger cut1 cut2 k k' b s) ht

theorem tsum_half_pow (c : ℝ) : ∑' j : ℕ, c * (2 ^ (j + 1) : ℝ)⁻¹ = c :=
  calc ∑' j : ℕ, c * (2 ^ (j + 1) : ℝ)⁻¹ = ∑' n : ℕ, c / 2 / 2 ^ n :=
        tsum_congr fun j => by rw [pow_succ]; ring
    _ = c := tsum_geometric_two' c

theorem summable_half_pow (c : ℝ) : Summable fun j : ℕ => c * (2 ^ (j + 1) : ℝ)⁻¹ := by
  have h : Summable fun j : ℕ => c / 2 * ((1 : ℝ) / 2) ^ j :=
    (summable_geometric_two).mul_left (c / 2)
  refine h.congr fun j => ?_
  rw [pow_succ, one_div, inv_pow]
  ring

/-- **Regime B, one `j₁`**: `∫_p^t ‖𝒦^{j₁}(t,s,k,k')‖ ≤ B 2^{−(j₁+1)} w(k,k')` when `|k| ≥ M₁^{10}`. -/
theorem lintegral_regimeB_le (hπ : π.Valid) (hL : 1 ≤ L) (hd : 0 < d) {b : (Fin d → ℤ) → ℂ}
    (hb : Summable fun m => ‖b m‖) (hev : b ∈ part2Event L γ δ p Ntr kind ζ π) (j₁ : ℕ)
    {k : Fin d → ℤ} (hk : (2 ^ j₁ * L) ^ 10 ≤ ‖latticePoint L k‖) (k' : Fin d → ℤ) {t : ℝ}
    (ht : t ∈ Icc (p : ℝ) (p + 1)) :
    ∫⁻ s in Ioo (p : ℝ) t, ‖Kpl L γ δ p Ntr kind none (some j₁) none ζ k k' b t s‖ₑ ≤
      ENNReal.ofReal (π.B * (2 ^ (j₁ + 1))⁻¹ * wtm L ζ π.A k k') := by
  have hL0 : 0 < L := by linarith
  set W := wtm L ζ π.A k k'
  set c : ℝ := π.B * (2 ^ (j₁ + 1))⁻¹ * W with hc
  have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg hπ.hB (by positivity)) (wtm_nonneg _ _ _ _ _)
  set box := dagBoxK (d := d) L Ntr kind j₁
  have hR : (0 : ℝ) ≤ (leafMax Ntr kind : ℝ) * (2 ^ j₁ * L) := by positivity
  -- the representatives
  have hrep := fun j₂ => testB_spec L γ δ p Ntr kind ζ hL j₁ j₂ hk
  choose k₀ hk₀ hk₀M hk₀K using hrep
  -- pointwise
  have hpt : ∀ s, ‖Kpl L γ δ p Ntr kind none (some j₁) none ζ k k' b t s‖ₑ ≤
      ∑' j₂, ∑ x ∈ box, ‖Kpl L γ δ p Ntr kind (some (dagLabel L x)) (some j₁) (some j₂) ζ (k₀ j₂)
        (k' - (ζ : ℤ) • (k - k₀ j₂)) b t s‖ₑ := by
    intro s
    rw [← (hasSum_Kpl_cut2 L γ δ p Ntr kind ζ k k' hL0 none (some j₁) b t s).tsum_eq]
    refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun j₂ => ?_)
    rw [← (hasSum_Kpl_dagger L γ δ p Ntr kind ζ k k' hd hL0.ne' (some j₁) (some j₂) b t s).tsum_eq]
    refine enorm_tsum_le_tsum_enorm.trans (le_of_eq ?_)
    rw [tsum_eq_sum (s := box)]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [enorm_mul, ← ofReal_norm (dagPhase L γ δ ζ x k' s), norm_dagPhase, ENNReal.ofReal_one, one_mul,
        hk₀K j₂ (dagLabel L x) b t s k']
    · intro x hx
      rcases dagBox_spec hL0 hR x with h | ⟨m, hm, hlt⟩
      · exact absurd h hx
      · rw [Kpl_dagger_eq_zero L γ δ p Ntr kind ζ k k' hd hL0 (some j₂) j₁ b t s x ⟨m, hm, hlt.le⟩, mul_zero,
          enorm_zero]
  -- each term
  have hterm : ∀ j₂, ∀ x ∈ box, ∫⁻ s in Ioo (p : ℝ) t, ‖Kpl L γ δ p Ntr kind (some (dagLabel L x)) (some j₁)
      (some j₂) ζ (k₀ j₂) (k' - (ζ : ℤ) • (k - k₀ j₂)) b t s‖ₑ ≤
        ENNReal.ofReal (π.B * (2 ^ (j₁ + 1))⁻¹ * (π.v j₂ / (box.card : ℝ)) * W) := by
    intro j₂ x hx
    refine (lintegral_piece_le L γ δ p Ntr kind ζ π hπ hb _ _ _ (π.hB j₂) (π.JB j₂) (hπ.hJB j₂) (hπ.hJhB j₂)
      _ _ ht).trans ?_
    have := hev.2 j₁ j₂ x hx (k₀ j₂) (hk₀ j₂) (k' - (ζ : ℤ) • (k - k₀ j₂))
    unfold PhiB lamB at this
    rw [wtm_shift] at this
    exact this
  have hmeas : ∀ j₂ (x : DagIdx d), Measurable fun s => ‖Kpl L γ δ p Ntr kind (some (dagLabel L x)) (some j₁)
      (some j₂) ζ (k₀ j₂) (k' - (ζ : ℤ) • (k - k₀ j₂)) b t s‖ₑ := fun j₂ x =>
    (measurable_Kpl_slice L γ δ p Ntr kind ζ _ _ _ _ _ b t).enorm
  calc ∫⁻ s in Ioo (p : ℝ) t, ‖Kpl L γ δ p Ntr kind none (some j₁) none ζ k k' b t s‖ₑ
      ≤ ∫⁻ s in Ioo (p : ℝ) t, ∑' j₂, ∑ x ∈ box, ‖Kpl L γ δ p Ntr kind (some (dagLabel L x)) (some j₁)
          (some j₂) ζ (k₀ j₂) (k' - (ζ : ℤ) • (k - k₀ j₂)) b t s‖ₑ := lintegral_mono hpt
    _ = ∑' j₂, ∑ x ∈ box, ∫⁻ s in Ioo (p : ℝ) t, ‖Kpl L γ δ p Ntr kind (some (dagLabel L x)) (some j₁)
          (some j₂) ζ (k₀ j₂) (k' - (ζ : ℤ) • (k - k₀ j₂)) b t s‖ₑ := by
        rw [lintegral_tsum fun j₂ => (Finset.measurable_sum _ fun x _ => hmeas j₂ x).aemeasurable]
        exact tsum_congr fun j₂ => lintegral_finsetSum _ fun x _ => hmeas j₂ x
    _ ≤ ∑' j₂, ∑ _x ∈ box, ENNReal.ofReal (π.B * (2 ^ (j₁ + 1))⁻¹ * (π.v j₂ / (box.card : ℝ)) * W) :=
        ENNReal.tsum_le_tsum fun j₂ => Finset.sum_le_sum fun x hx => hterm j₂ x hx
    _ ≤ ∑' j₂, ENNReal.ofReal (c * π.v j₂) := by
        refine ENNReal.tsum_le_tsum fun j₂ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rcases Nat.eq_zero_or_pos box.card with h0 | hpos
        · rw [h0]; simp only [Nat.cast_zero, zero_mul]
          exact mul_nonneg hc0 (hπ.hv0 j₂)
        · have hcard : (0 : ℝ) < box.card := by exact_mod_cast hpos
          rw [hc]
          field_simp
          exact le_rfl
    _ = ENNReal.ofReal (∑' j₂, c * π.v j₂) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j₂ => mul_nonneg hc0 (hπ.hv0 j₂)) (hπ.hv.mul_left c)).symm
    _ ≤ ENNReal.ofReal c := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_left]
        calc c * ∑' j₂, π.v j₂ ≤ c * 1 := mul_le_mul_of_nonneg_left hπ.hv1 hc0
          _ = c := mul_one c

/-- **3. The deterministic kernel bound**: `∫_p^t ‖𝒦_b(t, s, k, k')‖ ≤ B w(k, k')` on the event. -/
theorem lintegral_Kpl_le (hπ : π.Valid) (hL : 1 ≤ L) (hd : 0 < d) {b : (Fin d → ℤ) → ℂ}
    (hb : Summable fun m => ‖b m‖) (hev : b ∈ part2Event L γ δ p Ntr kind ζ π) {t : ℝ}
    (ht : t ∈ Icc (p : ℝ) (p + 1)) (k k' : Fin d → ℤ) :
    ∫⁻ s in Ioo (p : ℝ) t, ‖Kpl L γ δ p Ntr kind none none none ζ k k' b t s‖ₑ ≤
      ENNReal.ofReal (π.B * wtm L ζ π.A k k') := by
  have hL0 : 0 < L := by linarith
  set W := wtm L ζ π.A k k'
  have hW := wtm_nonneg L ζ π.A k k'
  have hpiece : ∀ j₁, ∫⁻ s in Ioo (p : ℝ) t, ‖Kpl L γ δ p Ntr kind none (some j₁) none ζ k k' b t s‖ₑ ≤
      ENNReal.ofReal (π.B * W * (2 ^ (j₁ + 1))⁻¹) := by
    intro j₁
    rw [show π.B * W * (2 ^ (j₁ + 1))⁻¹ = π.B * (2 ^ (j₁ + 1))⁻¹ * W by ring]
    by_cases hk : ‖latticePoint L k‖ ≤ (2 ^ j₁ * L) ^ 10
    · refine (lintegral_piece_le L γ δ p Ntr kind ζ π hπ hb _ _ _ π.hA π.JA hπ.hJA hπ.hJhA k k' ht).trans ?_
      have hkA : k ∈ testA L j₁ := (mem_ballZ hL0 (by positivity)).2 hk
      exact hev.1 j₁ k hkA k'
    · push Not at hk
      exact lintegral_regimeB_le L γ δ p Ntr kind ζ π hπ hL hd hb hev j₁ hk.le k' ht
  calc ∫⁻ s in Ioo (p : ℝ) t, ‖Kpl L γ δ p Ntr kind none none none ζ k k' b t s‖ₑ
      ≤ ∫⁻ s in Ioo (p : ℝ) t, ∑' j₁, ‖Kpl L γ δ p Ntr kind none (some j₁) none ζ k k' b t s‖ₑ := by
        refine lintegral_mono fun s => ?_
        rw [← (hasSum_Kpl_cut1 L γ δ p Ntr kind ζ k k' hL0 none none b t s).tsum_eq]
        exact enorm_tsum_le_tsum_enorm
    _ = ∑' j₁, ∫⁻ s in Ioo (p : ℝ) t, ‖Kpl L γ δ p Ntr kind none (some j₁) none ζ k k' b t s‖ₑ :=
        lintegral_tsum fun j₁ => (measurable_Kpl_slice L γ δ p Ntr kind ζ _ _ _ k k' b t).enorm.aemeasurable
    _ ≤ ∑' j₁, ENNReal.ofReal (π.B * W * (2 ^ (j₁ + 1))⁻¹) := ENNReal.tsum_le_tsum hpiece
    _ = ENNReal.ofReal (π.B * W) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (mul_nonneg hπ.hB hW) (by positivity))
          (summable_half_pow _), tsum_half_pow]

end Det

end WaveTurbulence.Fixedpt
