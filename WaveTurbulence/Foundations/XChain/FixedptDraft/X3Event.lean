/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Part1
public import WaveTurbulence.Foundations.XChain.FixedptDraft.ICanonicalCoefficient
public import WaveTurbulence.Foundations.XChain.FixedptDraft.ISolutionPhase
public import WaveTurbulence.Foundations.XChain.FixedptDraft.IBaseEvent

/-!
# X3: the excluded event (T L2333: "a subset `𝔊 ⊂ 𝔉_p` which has gauge and space translation symmetry")

`exists_symmetric_subevent`: let `Fev` be a symmetric event on which `a(ω)` is a classed solution with data
`initialCoeff ω`, and let `C` be a measurable set of data at time `T` that is stable under cubic phases. Then
there is a measurable symmetric `F' ⊆ Fev` such that:
- `a(ω, T) ∈ C` on `F'`;
- `Fev \ F' ⊆ {non-rapid data} ∪ {ω ∈ Fev | a(ω, T) ∉ C}`.

`F'` is the preimage under `initialCoeff` of `A₀ ∩ SolData ∩ canonA⁻¹(C)`:
- `A₀` is the data set of `Fev`;
- `SolData` is the data with a classed solution on `[0, T]`. It is measurable by the continuation criterion
  of NLS.Measurability, and phase-stable by INDUCT `isASolution_mul_phase`;
- `canonA` is INDUCT's `canonicalCoeff` at time `T`, covariant on `SolData`.

`Good1Q`: the clauses (1)–(2) at rational times. On summable data it is measurable and phase-stable, and it is
equivalent to `Good1` by continuity in `t`.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.Fixedpt

open MeasureTheory Set NLS SysAPI

variable {d : ℕ}

/-! ## Data with a classed solution -/

/-- The data with a classed solution on `[0, T]`. -/
def SolData (L γ δ T : ℝ) : Set ((Fin d → ℤ) → ℂ) :=
  {c | IsRapidDecay c ∧ ∃ a, IsASolution L γ δ T c a}

theorem solData_eq {L γ δ T : ℝ} (hL : 0 < L) :
    SolData (d := d) L γ δ T =
      ⋃ R : ℕ, {c | IsRapidDecay c ∧ L1.ofFun (weightUp c) ∈ truncBallSet L γ δ R T} := by
  ext c
  simp only [SolData, mem_ofPred_eq, mem_iUnion, truncBallSet, mem_iInter]
  constructor
  · rintro ⟨hc, a, ha⟩
    obtain ⟨R, hR⟩ := (exists_isAkSolution_iff (γ := γ) (δ := δ) (𝔇 := T) hL hc).1
      ⟨a, SysAPI.IsASolution.toNLS ha⟩
    exact ⟨R, hc, hR⟩
  · rintro ⟨R, hc, hR⟩
    obtain ⟨a, ha⟩ := (exists_isAkSolution_iff (γ := γ) (δ := δ) (𝔇 := T) hL hc).2 ⟨R, hR⟩
    exact ⟨hc, a, SysAPI.IsASolution.ofNLS ha⟩

theorem measurableSet_solData {L γ δ T : ℝ} (hL : 0 < L) : MeasurableSet (SolData (d := d) L γ δ T) := by
  rw [solData_eq hL]
  exact MeasurableSet.iUnion fun R =>
    measurableSet_isRapidDecay_inter (isClosed_truncBallSet (Nat.cast_nonneg R))

theorem solData_mul_phase {L γ δ T : ℝ} {φ : (Fin d → ℤ) → ℂ} (hφ : IsCubicPhase φ) {c : (Fin d → ℤ) → ℂ}
    (hc : c ∈ SolData L γ δ T) : (fun k => φ k * c k) ∈ SolData L γ δ T := by
  obtain ⟨hr, a, ha⟩ := hc
  exact ⟨rapidDecay_mul_phase hr hφ.norm_eq, _, isASolution_mul_phase ha φ hφ.norm_eq hφ.rel⟩

/-- The canonical value at time `T` of the solution with data `c`. -/
noncomputable def canonA (L γ δ T : ℝ) (c : (Fin d → ℤ) → ℂ) : (Fin d → ℤ) → ℂ :=
  fun n => canonicalCoeff L γ δ T T n c

theorem measurable_canonA {L γ δ T : ℝ} (hT : 0 ≤ T) : Measurable (canonA (d := d) L γ δ T) :=
  measurable_pi_iff.mpr fun n => measurable_canonicalCoeff L γ δ T ⟨hT, le_rfl⟩ n

theorem canonA_eq {L γ δ T : ℝ} (hL : 0 < L) (hT : 0 ≤ T) {c : (Fin d → ℤ) → ℂ} (hc : IsRapidDecay c)
    {a : ℝ → (Fin d → ℤ) → ℂ} (ha : IsASolution L γ δ T c a) : canonA L γ δ T c = a T :=
  funext fun n => canonicalCoeff_eq hL hc ha ⟨hT, le_rfl⟩ n

theorem canonA_mul_phase {L γ δ T : ℝ} (hL : 0 < L) (hT : 0 ≤ T) {φ : (Fin d → ℤ) → ℂ} (hφ : IsCubicPhase φ)
    {c : (Fin d → ℤ) → ℂ} (hc : c ∈ SolData L γ δ T) :
    canonA L γ δ T (fun k => φ k * c k) = fun k => φ k * canonA L γ δ T c k := by
  obtain ⟨hr, a, ha⟩ := hc
  rw [canonA_eq hL hT hr ha, canonA_eq hL hT (rapidDecay_mul_phase hr hφ.norm_eq)
    (isASolution_mul_phase ha φ hφ.norm_eq hφ.rel)]

/-! ## The symmetric sub-event -/

/-- **The symmetric sub-event** cut out by a phase-stable measurable condition on `a(T)`. -/
theorem exists_symmetric_subevent {Ω : Type*} [MeasurableSpace Ω] {L γ δ : ℝ} (hL : 0 < L) (φin : Mom d → ℝ)
    {g : (Fin d → ℤ) → Ω → ℂ} (hg : ∀ n, Measurable (g n)) {T : ℝ} (hT : 0 ≤ T)
    {Fev : Set Ω} (hsym : IsSymmetricEvent L φin g Fev) {a : Ω → ℝ → (Fin d → ℤ) → ℂ}
    (hsol : ∀ ω ∈ Fev, IsASolution L γ δ T (initialCoeff L φin g ω) (a ω))
    {C : Set ((Fin d → ℤ) → ℂ)} (hC : MeasurableSet C)
    (hCinv : ∀ φ, IsCubicPhase φ → ∀ b ∈ C, (fun k => φ k * b k) ∈ C) :
    ∃ F' ⊆ Fev, MeasurableSet F' ∧ IsSymmetricEvent L φin g F' ∧
      (∀ ω ∈ F', a ω T ∈ C) ∧
      Fev \ F' ⊆ (initialRapidEvent L φin g)ᶜ ∪ (Fev ∩ {ω | a ω T ∉ C}) := by
  obtain ⟨A₀, hA₀, hFev, hgauge, htrans⟩ := hsym
  set A₁ := SolData L γ δ T ∩ canonA L γ δ T ⁻¹' C
  have hA₁ : MeasurableSet A₁ := (measurableSet_solData hL).inter (measurable_canonA hT hC)
  have hinv : ∀ φ, IsCubicPhase φ → ∀ c ∈ A₁, (fun k => φ k * c k) ∈ A₁ := by
    rintro φ hφ c ⟨hcS, hcC⟩
    refine ⟨solData_mul_phase hφ hcS, ?_⟩
    show canonA L γ δ T (fun k => φ k * c k) ∈ C
    rw [canonA_mul_phase hL hT hφ hcS]
    exact hCinv φ hφ _ hcC
  have hFev' : ∀ ω, ω ∈ Fev ↔ initialCoeff L φin g ω ∈ A₀ := fun ω => by rw [hFev]; rfl
  refine ⟨initialCoeff L φin g ⁻¹' (A₀ ∩ A₁), fun ω hω => (hFev' ω).2 hω.1, ?_, ?_, ?_, ?_⟩
  · exact (measurable_initialCoeff L φin hg) (hA₀.inter hA₁)
  · refine ⟨A₀ ∩ A₁, hA₀.inter hA₁, rfl, ?_, ?_⟩
    · rintro θ c ⟨h0, h1⟩
      exact ⟨hgauge θ c h0, hinv _ (isCubicPhase_gauge θ) c h1⟩
    · rintro x c ⟨h0, h1⟩
      exact ⟨htrans x c h0, hinv _ (isCubicPhase_translation L x) c h1⟩
  · rintro ω ⟨h0, hS, hC'⟩
    have hω : ω ∈ Fev := (hFev' ω).2 h0
    rw [← canonA_eq hL hT hS.1 (hsol ω hω)]
    exact hC'
  · rintro ω ⟨hω, hnot⟩
    by_cases hr : ω ∈ initialRapidEvent L φin g
    · right
      refine ⟨hω, fun haC => hnot ⟨(hFev' ω).1 hω, ⟨hr, _, hsol ω hω⟩, ?_⟩⟩
      show canonA L γ δ T (initialCoeff L φin g ω) ∈ C
      rw [canonA_eq hL hT hr (hsol ω hω)]
      exact haC
    · exact Or.inl hr

/-! ## Clauses (1)–(2) at rational times -/

section Good1Q

/-- A closed condition holding at rational times holds on the whole interval. -/
theorem le_of_rat_le {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) {B : ℝ}
    (h : ∀ q : ℚ, (q : ℝ) ∈ Icc a b → f q ≤ B) : ∀ t ∈ Icc a b, f t ≤ B := by
  have hS : IsClosed (Icc a b ∩ f ⁻¹' Iic B) := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hsub : Ioo a b ∩ range ((↑) : ℚ → ℝ) ⊆ Icc a b ∩ f ⁻¹' Iic B := by
    rintro x ⟨hx, q, rfl⟩
    exact ⟨Ioo_subset_Icc_self hx, h q (Ioo_subset_Icc_self hx)⟩
  have hcl : Ioo a b ⊆ closure (Ioo a b ∩ range ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
  have h2 : closure (Ioo a b) ⊆ Icc a b ∩ f ⁻¹' Iic B :=
    closure_minimal (hcl.trans (closure_minimal hsub hS)) hS
  intro t ht
  rw [← closure_Ioo hab.ne] at ht
  exact (h2 ht).2

theorem measurableSet_imp (P' : Prop) {X : Type*} [MeasurableSpace X] {S : Set X} (hS : MeasurableSet S) :
    MeasurableSet {b | P' → b ∈ S} := by
  have : {b | P' → b ∈ S} = S ∪ {_b | ¬P'} := by
    ext b
    by_cases h : P' <;> simp [h]
  rw [this]
  exact hS.union (MeasurableSet.const _)

variable (P : WTParams) (p : ℕ)

/-- **Clauses (1)–(2) at rational times**, for `sumMod b`. -/
def Good1Q : Set ((Fin P.d → ℤ) → ℂ) :=
  {b | ∀ q : ℚ, (q : ℝ) ∈ Icc (p : ℝ) (p + 1) → ∀ n,
    ‖aTr P.L P.γ P.δ p (P.N (p + 1)) (sumMod b) q n‖ ≤
        jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) * Real.exp (3 * (P.N (p + 1) : ℝ)) ∧
      ‖Lop P.L P.γ P.δ p (P.N (p + 1)) (sumMod b) 0 (fun _ _ => 0) q n‖ ≤
        jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) * Real.exp (-(20 * P.N (p + 1) : ℝ))}

theorem stronglyMeasurable_aTr_data (q : ℝ) (n : Fin P.d → ℤ) :
    StronglyMeasurable fun b : (Fin P.d → ℤ) → ℂ => aTr P.L P.γ P.δ p (P.N (p + 1)) (sumMod b) q n :=
  stronglyMeasurable_aTr' P.L P.γ P.δ (B := fun b => sumMod b) (T := fun _ => q)
    (stronglyMeasurable_sumMod fun k => (measurable_pi_apply k).stronglyMeasurable) (fun b => summable_sumMod b)
    measurable_const p _ n

theorem stronglyMeasurable_L0_data (hL : 0 < P.L) (q : ℝ) (n : Fin P.d → ℤ) :
    StronglyMeasurable fun b : (Fin P.d → ℤ) → ℂ =>
      Lop P.L P.γ P.δ p (P.N (p + 1)) (sumMod b) 0 (fun _ _ => 0) q n := by
  have heq : (fun b : (Fin P.d → ℤ) → ℂ => Lop P.L P.γ P.δ p (P.N (p + 1)) (sumMod b) 0 (fun _ _ => 0) q n) =
      fun b => ∫ s in (p : ℝ)..q, L0Dt P.L P.γ P.δ p (P.N (p + 1)) (sumMod b) s n :=
    funext fun b => L0_eq P.L P.γ P.δ hL p _ (summable_sumMod b) _ q n
  rw [heq]
  exact stronglyMeasurable_intervalIntegral_param
    (F := fun z : ((Fin P.d → ℤ) → ℂ) × ℝ => L0Dt P.L P.γ P.δ p (P.N (p + 1)) (sumMod z.1) z.2 n)
    (stronglyMeasurable_L0Dt' P.L P.γ P.δ (B := fun z : ((Fin P.d → ℤ) → ℂ) × ℝ => sumMod z.1)
      (stronglyMeasurable_sumMod fun k => ((measurable_pi_apply k).comp measurable_fst).stronglyMeasurable)
      (fun z => summable_sumMod _) measurable_snd p _ n) measurable_const _

theorem measurableSet_good1Q (hL : 0 < P.L) : MeasurableSet (Good1Q P p) := by
  have : Good1Q P p = ⋂ q : ℚ, ⋂ n : Fin P.d → ℤ, {b | (q : ℝ) ∈ Icc (p : ℝ) (p + 1) → b ∈
      {b | ‖aTr P.L P.γ P.δ p (P.N (p + 1)) (sumMod b) q n‖ ≤
        jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) * Real.exp (3 * (P.N (p + 1) : ℝ))} ∩
      {b | ‖Lop P.L P.γ P.δ p (P.N (p + 1)) (sumMod b) 0 (fun _ _ => 0) q n‖ ≤
        jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) * Real.exp (-(20 * P.N (p + 1) : ℝ))}} := by
    ext b
    simp only [Good1Q, mem_ofPred_eq, mem_iInter, mem_inter_iff]
    constructor
    · intro h q n hq
      exact h q hq n
    · intro h q hq n
      exact h q n hq
  rw [this]
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun n => measurableSet_imp _ ?_
  exact (measurableSet_le (stronglyMeasurable_aTr_data P p q n).measurable.norm measurable_const).inter
    (measurableSet_le (stronglyMeasurable_L0_data P p hL q n).measurable.norm measurable_const)

theorem good1Q_mul_phase (hL : 0 < P.L) {φ : (Fin P.d → ℤ) → ℂ} (hφ : IsCubicPhase φ) {b : (Fin P.d → ℤ) → ℂ}
    (hb : Summable fun m => ‖b m‖) (h : b ∈ Good1Q P p) : (fun k => φ k * b k) ∈ Good1Q P p := by
  intro q hq n
  have hb' : Summable fun m => ‖φ m * b m‖ := (summable_mul_phase hφ).2 hb
  obtain ⟨h1, h2⟩ := h q hq n
  rw [sumMod_of_summable hb] at h1 h2
  rw [sumMod_of_summable hb', aTr_mul_phase P.L P.γ P.δ hφ p hb,
    Lop0_mul_phase P.L P.γ P.δ hφ p hb hL _ (fun _ _ => 0) (fun _ _ => 0), norm_mul, norm_mul, hφ.norm_eq,
    one_mul, one_mul]
  exact ⟨h1, h2⟩

theorem good1_of_good1Q (hL : 0 < P.L) {b : (Fin P.d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖)
    (h : b ∈ Good1Q P p) : b ∈ Good1 P p := by
  have hp : (p : ℝ) < p + 1 := by linarith
  refine ⟨fun t ht n => ?_, fun t ht n => ?_⟩
  · refine le_of_rat_le hp (f := fun t => ‖aTr P.L P.γ P.δ p (P.N (p + 1)) b t n‖)
      (continuousOn_aTr P.L P.γ P.δ p _ (p + 1) hb n).norm (fun q hq => ?_) t ht
    have := (h q hq n).1
    rwa [sumMod_of_summable hb] at this
  · have hc : Continuous fun t => Lop P.L P.γ P.δ p (P.N (p + 1)) b 0 (fun _ _ => 0) t n := by
      simp_rw [L0_eq P.L P.γ P.δ hL p _ hb]
      exact intervalIntegral.continuous_primitive
        (fun a c => intervalIntegrable_L0Dt P.L P.γ P.δ p _ hb a c n) _
    refine le_of_rat_le hp (f := fun t => ‖Lop P.L P.γ P.δ p (P.N (p + 1)) b 0 (fun _ _ => 0) t n‖)
      hc.norm.continuousOn (fun q hq => ?_) t ht
    have := (h q hq n).2
    rwa [sumMod_of_summable hb] at this

theorem good1Q_of_good1 {b : (Fin P.d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖) (h : b ∈ Good1 P p) :
    b ∈ Good1Q P p := fun q hq n => by
  rw [sumMod_of_summable hb]
  exact ⟨h.1 q hq n, h.2 q hq n⟩

end Good1Q

end WaveTurbulence.Fixedpt
