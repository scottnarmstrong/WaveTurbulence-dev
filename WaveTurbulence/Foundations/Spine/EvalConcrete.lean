/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.EvalSem
public import WaveTurbulence.Foundations.Spine.TypeSlopes
public import WaveTurbulence.Foundations.RegularAsymptotics.KernelContinuity
public import WaveTurbulence.Foundations.Spine.LeafwiseKernelSpatial
public import WaveTurbulence.Foundations.RegularAsymptotics.CosetSummability
/-! AMEND6' (design P*): the concrete evaluation system `V g = k |-> sum_{LG in A} K_LG[typeProfiles g](k)`:
qualitative admissibility `AdmI` (`Inv` with the bounds forgotten), its closure under one operation, the
smoothness of `V`, and the exact slope identities (D), (M) for `V` as function identities. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset CentralDiff NormBridgeScratch
open scoped ENNReal

/-- The evaluation of the pair-type profile `g` on the garden set `A`. -/
noncomputable def evalV (P : WTParams) {w : ℕ} (A : Finset (LayeredGarden w)) (tt : Fin w → ℝ)
    (nroot : Fin w → (Fin P.d → ℤ)) (g : TProf P.d w) : Mom P.d → ℂ :=
  fun k => ∑ LG ∈ A, kernelLeaves P.L P.γ P.δ LG (typeProfiles LG g) (fun b => tt b.1.1) 0 k nroot 0

/-- Qualitative admissibility before the operations `os`: `Inv` at levels `(1, d+1)` for some bounds. -/
def AdmI (P : WTParams) {w : ℕ} (p : ℕ) (os : List (TOp P.d w)) (g : TProf P.d w) : Prop :=
  ∃ u c : ℝ, 0 ≤ u ∧ 0 ≤ c ∧ Inv p 1 (P.d + 1) os u c g

theorem AdmI.step (P : WTParams) (hd : 1 ≤ P.d) {w p : ℕ} {O : TOp P.d w} {rest : List (TOp P.d w)}
    {g : TProf P.d w} (μ : ℝ) (h : AdmI P p (O :: rest) g) :
    AdmI P p rest (TProf.perturb g (O.apply g) μ) := by
  obtain ⟨u, c, hu, hc, hI⟩ := h
  have hd1 : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  have hdc : dcnt rest ≤ dcnt (O :: rest) := by cases O <;> simp [dcnt_der, dcnt_form]
  have h2 : (1 : ℝ) ≤ 2 * P.d := by linarith
  refine ⟨_, _, ?_, ?_, Inv.step hd (x := |μ|) (κ := (2 * (P.d : ℝ)) ^ (1 + dcnt (O :: rest)))
    hu hc (abs_nonneg μ) μ le_rfl ?_ ?_ hI⟩
  · positivity
  · positivity
  · rw [mul_pow]
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  · rw [← mul_pow]
    exact pow_le_pow_right₀ h2 (by omega)

variable {P : WTParams} {w : ℕ} {A : Finset (LayeredGarden w)} {p : ℕ}

/-- Input data of a leaf from the pair-type invariant. -/
theorem leaf_inv {os : List (TOp P.d w)} {u c : ℝ} {g : TProf P.d w} (hI : Inv p 1 (P.d + 1) os u c g)
    {LG : LayeredGarden w} (hlay : ∀ a, LG.layer a ≤ p) (l : GLeaf LG.garden.tree) :
    ContDiff ℝ (1 + dcnt os : ℕ) (typeProfiles LG g l.1) ∧
    SNormR (1 + dcnt os) (P.d + 1 + fcnt (l.1.1) (LG.garden.pair l).1.1 os) (typeProfiles LG g l.1) ≤
      ENNReal.ofReal u ∧ SNormR 1 (P.d + 1) (typeProfiles LG g l.1) ≤ ENNReal.ofReal c := by
  rw [typeProfiles_leaf]
  exact hI _ (hlay _) _ _


/-- Standing hypotheses of an evaluation system. `σ j0` is the (common) sign of the root `j0`. -/
structure EvalCtx (P : WTParams) {w : ℕ} (A : Finset (LayeredGarden w)) (p M : ℕ) (σ : Fin w → ℝ) : Prop where
  hd : 1 ≤ P.d
  hL : 1 ≤ P.L
  hM1 : 1 ≤ M
  plain : ∀ LG ∈ A, LG.garden.IsPlain
  lay : ∀ LG ∈ A, ∀ a, LG.layer a ≤ p
  card : ∀ LG ∈ A, (inputLeaves LG.garden).card ≤ 2 * M
  sig : ∀ LG ∈ A, ∀ j0, (((nodeSign LG.garden.sig (GNode.root LG.garden.tree j0).1 : ℤˣ) : ℤ) : ℝ) = σ j0

variable {M : ℕ} {σ : Fin w → ℝ}

theorem evalV_contDiff (hc : EvalCtx P A p M σ) (tt : Fin w → ℝ) (nroot : Fin w → (Fin P.d → ℤ))
    {os : List (TOp P.d w)} {g : TProf P.d w} (h : AdmI P p os g) :
    ContDiff ℝ (dcnt os : ℕ) (evalV P A tt nroot g) := by
  obtain ⟨u, c, hu, hc0, hI⟩ := h
  unfold evalV
  refine ContDiff.sum fun LG hLG => ?_
  refine contDiff_kernelLeaves_spatial (A := dcnt os) (B := P.d + 1) hc.hd hc.hL P.γ P.δ LG (typeProfiles LG g)
    (fun _ => ⟨u, hu⟩) ?_ ?_ le_rfl _ _ _ _ (card_lone_le_one_of_plain _ (hc.plain LG hLG))
  · intro l _
    exact Complex.ofRealCLM.contDiff.comp
      ((leaf_inv hI (hc.lay LG hLG) l).1.of_le (by exact_mod_cast Nat.le_add_left _ _))
  · intro l _
    obtain ⟨h1, h2, _⟩ := leaf_inv hI (hc.lay LG hLG) l
    exact SNormR_mono_bound (Nat.le_add_left _ _) (Nat.le_add_right _ _) _ h1 u hu h2


theorem evalV_D (hc : EvalCtx P A p M σ) (tt : Fin w → ℝ) (nroot : Fin w → (Fin P.d → ℤ))
    {i : Fin P.d} {rest : List (TOp P.d w)} {g : TProf P.d w} (h : AdmI P p (TOp.der i :: rest) g)
    (lam : ℝ) (hlam : lam ≠ 0) :
    (fun x => ∑ m ∈ range (2 * M + 1), ((cw M m / lam : ℝ) : ℂ) *
      evalV P A tt nroot (TProf.perturb g (TProf.der i g) (lam * ((m : ℝ) - M))) x) =
      partialMom i (evalV P A tt nroot g) := by
  obtain ⟨u, c, hu, hc0, hI⟩ := h
  have hK : ∀ LG ∈ A, ContDiff ℝ (1 : ℕ) (fun x => kernelLeaves P.L P.γ P.δ LG (typeProfiles LG g)
      (fun b => tt b.1.1) 0 x nroot 0) := by
    intro LG hLG
    refine contDiff_kernelLeaves_spatial (A := 1) (B := P.d + 1) hc.hd hc.hL P.γ P.δ LG (typeProfiles LG g)
      (fun _ => ⟨c, hc0⟩) ?_ ?_ le_rfl _ _ _ _ (card_lone_le_one_of_plain _ (hc.plain LG hLG))
    · intro l _
      exact Complex.ofRealCLM.contDiff.comp
        ((leaf_inv hI (hc.lay LG hLG) l).1.of_le (by rw [dcnt_der]; exact_mod_cast (by omega)))
    · intro l _
      exact (leaf_inv hI (hc.lay LG hLG) l).2.2
  have hd1 : (1 : ℕ) = [i].length := rfl
  have hsum : partialMom i (evalV P A tt nroot g) =
      fun x => ∑ LG ∈ A, partialMom i (fun y => kernelLeaves P.L P.γ P.δ LG (typeProfiles LG g)
        (fun b => tt b.1.1) 0 y nroot 0) x := by
    have := wordD_finset_sum A [i] (fun LG y => kernelLeaves P.L P.γ P.δ LG (typeProfiles LG g)
        (fun b => tt b.1.1) 0 y nroot 0) (fun LG hLG => by simpa using hK LG hLG)
    exact this
  rw [hsum]
  funext x
  have hper : ∀ LG ∈ A, partialMom i (fun y => kernelLeaves P.L P.γ P.δ LG (typeProfiles LG g)
        (fun b => tt b.1.1) 0 y nroot 0) x =
      ∑ m ∈ range (2 * M + 1), ((cw M m / lam : ℝ) : ℂ) *
        kernelLeaves P.L P.γ P.δ LG (typeProfiles LG (TProf.perturb g (TProf.der i g) (lam * ((m : ℝ) - M))))
          (fun b => tt b.1.1) 0 x nroot 0 := by
    intro LG hLG
    have hbb : ∀ l ∈ inputLeaves LG.garden, SNormR 1 (P.d + 1) (typeProfiles LG g l.1) ≤
        ENNReal.ofReal ((⟨c, hc0⟩ : NNReal) : ℝ) := fun l _ => (leaf_inv hI (hc.lay LG hLG) l).2.2
    refine partialMom_kernel_typeProfiles (B := P.d + 1) hc.hd hc.hL le_rfl P.γ P.δ LG g i
      (fun _ => ⟨c, hc0⟩) ?_ hbb (fun b => tt b.1.1) 0 nroot 0 (card_lone_le_one_of_plain _ (hc.plain LG hLG))
      ?_ ?_ M hc.hM1 (hc.card LG hLG) lam hlam x
    · intro l _
      exact (leaf_inv hI (hc.lay LG hLG) l).1.of_le (by rw [dcnt_der]; exact_mod_cast (by omega))
    · intro k l hl
      exact summable_abs_coset_of_SNormR hc.hL le_rfl hc0 _ (hbb l hl) k
    · intro k l hl
      rw [typeProfiles_der]
      have hcd : ContDiff ℝ ((0 : ℕ) + 1 : ℕ) (typeProfiles LG g l.1) :=
        (leaf_inv hI (hc.lay LG hLG) l).1.of_le (by rw [dcnt_der]; exact_mod_cast (by omega))
      have hb0 := SNormR_realPartialMom_bound (A := 0) (B := P.d + 1) hc.hd i _ hcd c hc0
        (by simpa using hbb l hl)
      exact summable_abs_coset_of_SNormR hc.hL le_rfl (by positivity) _ hb0 k
  rw [Finset.sum_congr rfl hper, Finset.sum_comm]
  unfold evalV
  simp_rw [Finset.mul_sum]


/-- The root linear form `x |-> sigma_{j0} (x + r_{j0})_i` as a complex-valued function of the base momentum. -/
noncomputable def rootForm (P : WTParams) {w : ℕ} (σ : Fin w → ℝ) (nroot : Fin w → (Fin P.d → ℤ))
    (j0 : Fin w) (i : Fin P.d) : Mom P.d → ℂ :=
  fun x => ((σ j0 * (x + latticePoint P.L (nroot j0)) i : ℝ) : ℂ)

theorem evalV_M (hc : EvalCtx P A p M σ) (tt : Fin w → ℝ) (nroot : Fin w → (Fin P.d → ℤ))
    {j0 : Fin w} {i : Fin P.d} {rest : List (TOp P.d w)} {g : TProf P.d w}
    (h : AdmI P p (TOp.form j0 i :: rest) g) (lam : ℝ) (hlam : lam ≠ 0) :
    (fun x => ∑ m ∈ range (2 * M + 1), ((cw M m / lam : ℝ) : ℂ) *
      evalV P A tt nroot (TProf.perturb g (TProf.form j0 i g) (lam * ((m : ℝ) - M))) x) =
      rootForm P σ nroot j0 i * evalV P A tt nroot g := by
  obtain ⟨u, c, hu, hc0, hI⟩ := h
  funext x
  have hper : ∀ LG ∈ A, ((σ j0 * (x + latticePoint P.L (nroot j0)) i : ℝ) : ℂ) *
        kernelLeaves P.L P.γ P.δ LG (typeProfiles LG g) (fun b => tt b.1.1) 0 x nroot 0 =
      ∑ m ∈ range (2 * M + 1), ((cw M m / lam : ℝ) : ℂ) *
        kernelLeaves P.L P.γ P.δ LG (typeProfiles LG (TProf.perturb g (TProf.form j0 i g) (lam * ((m : ℝ) - M))))
          (fun b => tt b.1.1) 0 x nroot 0 := by
    intro LG hLG
    have hbb : ∀ l ∈ inputLeaves LG.garden, SNormR 1 (P.d + 1) (typeProfiles LG g l.1) ≤
        ENNReal.ofReal c := fun l _ => (leaf_inv hI (hc.lay LG hLG) l).2.2
    have := rootcoord_mul_kernel_typeProfiles P.L P.γ P.δ LG (hc.plain LG hLG)
      (card_lone_le_one_of_plain _ (hc.plain LG hLG)) g j0 i (fun b => tt b.1.1) 0 x nroot 0
      (fun l hl => summable_abs_coset_of_SNormR hc.hL le_rfl hc0 _ (hbb l hl) x)
      ?_ M hc.hM1 (hc.card LG hLG) lam hlam
    · rw [hc.sig LG hLG j0] at this
      exact_mod_cast this
    · intro l hl
      simp_rw [typeProfiles_form]
      by_cases hz : ((if l.1.1 = j0 then (1 : ℝ) else 0) - (if (LG.garden.pair l).1.1 = j0 then (1 : ℝ) else 0)) = 0
      · simp only [hz, zero_mul, abs_zero]
        exact summable_zero
      · obtain ⟨h1, h2, _⟩ := leaf_inv hI (hc.lay LG hLG) l
        have hf : fcnt l.1.1 (LG.garden.pair l).1.1 (TOp.form j0 i :: rest) =
            fcnt l.1.1 (LG.garden.pair l).1.1 rest + 1 := by
          rw [fcnt_form]
          have : TOp.coef (d := P.d) l.1.1 (LG.garden.pair l).1.1 (.form j0 i) ≠ 0 := hz
          rw [if_neg this]
        rw [hf] at h2
        have h0 : ContDiff ℝ ((0 : ℕ) : ℕ) (typeProfiles LG g l.1) := h1.of_le (by exact_mod_cast Nat.zero_le _)
        have h3 : SNormR 0 (P.d + 1 + 1) (typeProfiles LG g l.1) ≤ ENNReal.ofReal u :=
          SNormR_mono_bound (Nat.zero_le _) (by omega) _ h1 u hu h2
        have hcf : |(if l.1.1 = j0 then (1 : ℝ) else 0) - (if (LG.garden.pair l).1.1 = j0 then (1 : ℝ) else 0)| ≤ 1 :=
          abs_coef_le (d := P.d) l.1.1 (LG.garden.pair l).1.1 j0 i
        have h4 := SNormR_coord_mul_le (A := 0) (B := P.d + 1) hc.hd i _ hcf _ h0 u hu h3
        exact summable_abs_coset_of_SNormR hc.hL le_rfl (by positivity) _ h4 x
  have hrw : rootForm P σ nroot j0 i x * evalV P A tt nroot g x = ∑ LG ∈ A,
      ((σ j0 * (x + latticePoint P.L (nroot j0)) i : ℝ) : ℂ) *
        kernelLeaves P.L P.γ P.δ LG (typeProfiles LG g) (fun b => tt b.1.1) 0 x nroot 0 := by
    unfold rootForm evalV
    rw [Finset.mul_sum]
  show _ = rootForm P σ nroot j0 i x * evalV P A tt nroot g x
  rw [hrw, Finset.sum_congr rfl hper, Finset.sum_comm]
  unfold evalV
  simp_rw [Finset.mul_sum]


/-- The semantics of the recursion on `evalV`: derivatives (reversed) then root forms. -/
theorem evalV_ders_forms (hc : EvalCtx P A p M σ) (tt : Fin w → ℝ) (nroot : Fin w → (Fin P.d → ℤ))
    (lam : ℝ) (hlam : lam ≠ 0) (ders : List (Fin P.d)) (fs : List (Fin w × Fin P.d)) (h : TProf P.d w)
    (hh : AdmI P p (ders.map TOp.der ++ fs.map fun f => TOp.form f.1 f.2) h) :
    evalOps (evalV P A tt nroot) M lam (ders.map TOp.der ++ fs.map fun f => TOp.form f.1 f.2) h =
      (fs.map fun f => rootForm P σ nroot f.1 f.2).prod * wordD ders.reverse (evalV P A tt nroot h) :=
  evalOps_ders_forms (evalV P A tt nroot) M lam (rootForm P σ nroot) (AdmI P p)
    (fun O rest g μ hg => AdmI.step P hc.hd μ hg)
    (fun os g hg => evalV_contDiff hc tt nroot hg)
    (fun i rest g hg => evalV_D hc tt nroot hg lam hlam)
    (fun j0 i rest g hg => evalV_M hc tt nroot hg lam hlam) ders fs h hh

end WaveTurbulence.LGSpine
