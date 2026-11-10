/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# X3: the complete model of `Z` (copied from INDUCT)

`Z = Z^Λ([p, p+1])` is modelled by the Banach space `(ℤ^d →ᵇ C([p,p+1], ℂ))` with weights `⟨n⟩^Λ`, which gives the
contraction principle `exists_Z_fixedPoint`. All of this is **copied verbatim** from wt-cumul's INDUCT scratch,
with only the namespace changed (`WaveTurbulence.Fixedpt`), so the copies cannot clash:
- `ZBanach.lean` (sha256 `debb7b1f236c58b4e6af56f12857ff0c4c7fc21e303605beb0d3c5fbab056911`), whole file;
- `ZFixedPoint.lean` (sha256 `34301f902ff00f84330578d0ac445f6efef9b2e8215c41cce692652b2afbe261`), whole file;
- `ZOperations.lean` (sha256 `ef067723b4f83ee39e4932207bf106dde38fe36f6978b5d713a9a7af2c4eb03d`): `ZNorm_le_of_decay`, `ZNorm_add_le`, `ZNorm_mono`,
  `zSpace_mono`, `zSpace_add`.
On landing, keep one copy.
-/

@[expose] public section
namespace WaveTurbulence.Fixedpt
open Set
open scoped ENNReal NNReal BoundedContinuousFunction

abbrev ZTime (p : ℕ) := Icc (p : ℝ) (p + 1)
abbrev ZModel (d p : ℕ) := (Fin d → ℤ) →ᵇ C(ZTime p, ℂ)

noncomputable def zWeight {d : ℕ} (L Λ : ℝ) (n : Fin d → ℤ) : ℝ :=
  jbr (latticePoint L n) ^ Λ

theorem zWeight_pos {d : ℕ} (L Λ : ℝ) (n : Fin d → ℤ) : 0 < zWeight L Λ n :=
  Real.rpow_pos_of_pos (Real.sqrt_pos.mpr (by positivity)) _

noncomputable def zDecode {d p : ℕ} (L Λ : ℝ) (g : ZModel d p) :
    ZTime p → (Fin d → ℤ) → ℂ := fun t n => g n t / (zWeight L Λ n : ℂ)

theorem weighted_zDecode_norm {d p : ℕ} (L Λ : ℝ) (g : ZModel d p)
    (t : ZTime p) (n : Fin d → ℤ) :
    zWeight L Λ n * ‖zDecode L Λ g t n‖ = ‖g n t‖ := by
  rw [zDecode, norm_div, Complex.norm_real, Real.norm_of_nonneg (zWeight_pos L Λ n).le]
  exact mul_div_cancel₀ _ (zWeight_pos L Λ n).ne'

theorem ZNorm_zDecode {d p : ℕ} (L Λ : ℝ) (g : ZModel d p) :
    ZNorm L Λ (zDecode L Λ g) = ‖g‖ₑ := by
  unfold ZNorm
  simp_rw [show ∀ t n, jbr (latticePoint L n) ^ Λ * ‖zDecode L Λ g t n‖ = ‖g n t‖ from
    weighted_zDecode_norm L Λ g, ofReal_norm]
  rw [iSup_comm]
  simp only [← ContinuousMap.enorm_eq_iSup_enorm, ← BoundedContinuousFunction.enorm_eq_iSup_enorm]

theorem zDecode_mem_ZSpace {d p : ℕ} (L Λ : ℝ) (g : ZModel d p) :
    zDecode L Λ g ∈ ZSpace L Λ p := by
  refine ⟨fun n => (g n).continuous.div_const _, ?_⟩
  rw [ZNorm_zDecode]
  exact enorm_lt_top

theorem zSpace_weighted_bound {d p : ℕ} {L Λ : ℝ} {b : ZTime p → (Fin d → ℤ) → ℂ}
    (hb : b ∈ ZSpace L Λ p) (t : ZTime p) (n : Fin d → ℤ) :
    zWeight L Λ n * ‖b t n‖ ≤ (ZNorm L Λ b).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal hb.2.ne).mp
  exact le_iSup_of_le t (le_iSup (fun n => ENNReal.ofReal (zWeight L Λ n * ‖b t n‖)) n)

noncomputable def zEncode {d p : ℕ} (L Λ : ℝ) (b : ZTime p → (Fin d → ℤ) → ℂ)
    (hb : b ∈ ZSpace L Λ p) : ZModel d p := by
  have hc : ∀ n, Continuous (fun t => b t n) := hb.1
  let f : (Fin d → ℤ) → C(ZTime p, ℂ) :=
    fun n => ⟨fun t => (zWeight L Λ n : ℂ) * b t n, continuous_const.mul (hc n)⟩
  refine BoundedContinuousFunction.ofNormedAddCommGroupDiscrete f (ZNorm L Λ b).toReal ?_
  intro n
  apply (ContinuousMap.norm_le (f n) ENNReal.toReal_nonneg).mpr
  intro t
  change ‖(zWeight L Λ n : ℂ) * b t n‖ ≤ (ZNorm L Λ b).toReal
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (zWeight_pos L Λ n).le]
  exact zSpace_weighted_bound hb t n

theorem zDecode_zEncode {d p : ℕ} (L Λ : ℝ) (b : ZTime p → (Fin d → ℤ) → ℂ)
    (hb : b ∈ ZSpace L Λ p) : zDecode L Λ (zEncode L Λ b hb) = b := by
  funext t n
  change (zWeight L Λ n : ℂ) * b t n / (zWeight L Λ n : ℂ) = b t n
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (zWeight_pos L Λ n).ne')

theorem enorm_zEncode {d p : ℕ} (L Λ : ℝ) (b : ZTime p → (Fin d → ℤ) → ℂ)
    (hb : b ∈ ZSpace L Λ p) : ‖zEncode L Λ b hb‖ₑ = ZNorm L Λ b := by
  rw [← ZNorm_zDecode L Λ (zEncode L Λ b hb), zDecode_zEncode]

theorem zDecode_sub {d p : ℕ} (L Λ : ℝ) (g h : ZModel d p) :
    zDecode L Λ (g - h) = zDecode L Λ g - zDecode L Λ h := by
  funext t n
  exact sub_div _ _ _

theorem ZNorm_zDecode_sub {d p : ℕ} (L Λ : ℝ) (g h : ZModel d p) :
    ZNorm L Λ (zDecode L Λ g - zDecode L Λ h) = ‖g - h‖ₑ := by
  rw [← zDecode_sub, ZNorm_zDecode]

theorem exists_Z_fixedPoint {d p : ℕ} (L Λ r : ℝ) (hr : 0 ≤ r)
    (R : (ZTime p → (Fin d → ℤ) → ℂ) → (ZTime p → (Fin d → ℤ) → ℂ) → Prop)
    (hmaps : ∀ b ∈ ZSpace L Λ p, ZNorm L Λ b ≤ ENNReal.ofReal r →
      ∃ c ∈ ZSpace L Λ p, R b c ∧ ZNorm L Λ c ≤ ENNReal.ofReal r)
    (hlip : ∀ b ∈ ZSpace L Λ p, ∀ b' ∈ ZSpace L Λ p,
      ∀ c ∈ ZSpace L Λ p, ∀ c' ∈ ZSpace L Λ p,
      ZNorm L Λ b ≤ ENNReal.ofReal r → ZNorm L Λ b' ≤ ENNReal.ofReal r →
      R b c → R b' c' →
      ZNorm L Λ (c - c') ≤ ENNReal.ofReal (1 / 2) * ZNorm L Λ (b - b')) :
    ∃ b ∈ ZSpace L Λ p, ZNorm L Λ b ≤ ENNReal.ofReal r ∧ R b b := by
  classical
  have hdist (g h : ZModel d p) : dist g h = ‖g - h‖ := dist_eq_norm g h
  let S := Metric.closedBall (0 : ZModel d p) r
  have hS : IsClosed S := Metric.isClosed_closedBall
  let : CompleteSpace S := hS.completeSpace_coe
  let : Nonempty S := ⟨⟨0, by simpa only [S, Metric.mem_closedBall, dist_self] using hr⟩⟩
  have hball (x : S) : ZNorm L Λ (zDecode L Λ x.1) ≤ ENNReal.ofReal r := by
    rw [ZNorm_zDecode, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [S, Metric.mem_closedBall, BoundedContinuousFunction.norm_def] using x.2)
  have hex (x : S) := hmaps (zDecode L Λ x.1) (zDecode_mem_ZSpace L Λ x.1) (hball x)
  choose c hcZ hcR hcB using hex
  let Φ : S → S := fun x => ⟨zEncode L Λ (c x) (hcZ x), by
    change dist (zEncode L Λ (c x) (hcZ x)) 0 ≤ r
    rw [← BoundedContinuousFunction.norm_def]
    apply (ENNReal.ofReal_le_ofReal_iff hr).mp
    rw [ofReal_norm, enorm_zEncode]
    exact hcB x⟩
  have hcontract : ContractingWith (1 / 2 : ℝ≥0) Φ := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    have h := hlip _ (zDecode_mem_ZSpace L Λ x.1) _ (zDecode_mem_ZSpace L Λ y.1)
      _ (hcZ x) _ (hcZ y) (hball x) (hball y) (hcR x) (hcR y)
    have he : ZNorm L Λ (c x - c y) =
        ‖zEncode L Λ (c x) (hcZ x) - zEncode L Λ (c y) (hcZ y)‖ₑ := by
      rw [← ZNorm_zDecode_sub, zDecode_zEncode, zDecode_zEncode]
    rw [he, ZNorm_zDecode_sub] at h
    change dist (zEncode L Λ (c x) (hcZ x)) (zEncode L Λ (c y) (hcZ y)) ≤
      (1 / 2 : ℝ) * dist x.1 y.1
    rw [hdist, hdist]
    have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) * ‖x.1 - y.1‖ :=
      mul_nonneg (by norm_num) (norm_nonneg (x.1 - y.1))
    exact (ENNReal.ofReal_le_ofReal_iff h0).mp (by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      convert h using 1
      · exact ofReal_norm (zEncode L Λ (c x) (hcZ x) - zEncode L Λ (c y) (hcZ y))
      · exact congrArg (ENNReal.ofReal (1 / 2 : ℝ) * ·) (ofReal_norm (x.1 - y.1)))
  let x : S := ContractingWith.fixedPoint Φ hcontract
  have hx : Φ x = x := ContractingWith.fixedPoint_isFixedPt hcontract
  have hcx : c x = zDecode L Λ x.1 := by
    calc
      _ = zDecode L Λ (Φ x).1 := (zDecode_zEncode L Λ (c x) (hcZ x)).symm
      _ = _ := congrArg (fun y : S => zDecode L Λ y.1) hx
  refine ⟨zDecode L Λ x.1, zDecode_mem_ZSpace L Λ x.1, hball x, ?_⟩
  simpa only [hcx] using hcR x

theorem ZNorm_le_of_decay {d p : ℕ} (L Λ C : ℝ)
    {f : ZTime p → (Fin d → ℤ) → ℂ}
    (hf : ∀ t n, ‖f t n‖ ≤ jbr (latticePoint L n) ^ (-Λ) * C) :
    ZNorm L Λ f ≤ ENNReal.ofReal C := by
  apply iSup_le fun t => iSup_le fun n => ?_
  apply ENNReal.ofReal_le_ofReal
  have hw := zWeight_pos L Λ n
  calc
    _ ≤ zWeight L Λ n * (jbr (latticePoint L n) ^ (-Λ) * C) :=
      mul_le_mul_of_nonneg_left (hf t n) hw.le
    _ = C := by
      have hj : 0 < jbr (latticePoint L n) := Real.sqrt_pos.mpr (by positivity)
      rw [Real.rpow_neg hj.le]
      exact mul_inv_cancel_left₀ hw.ne' _

theorem ZNorm_add_le {d p : ℕ} (L Λ : ℝ)
    (f g : ZTime p → (Fin d → ℤ) → ℂ) :
    ZNorm L Λ (f + g) ≤ ZNorm L Λ f + ZNorm L Λ g := by
  apply iSup_le fun t => iSup_le fun n => ?_
  have hw := (zWeight_pos L Λ n).le
  calc
    _ ≤ ENNReal.ofReal (zWeight L Λ n * ‖f t n‖ + zWeight L Λ n * ‖g t n‖) :=
      ENNReal.ofReal_le_ofReal (by simpa only [Pi.add_apply, mul_add, zWeight] using
        (mul_le_mul_of_nonneg_left (norm_add_le (f t n) (g t n)) hw))
    _ = ENNReal.ofReal (zWeight L Λ n * ‖f t n‖) +
        ENNReal.ofReal (zWeight L Λ n * ‖g t n‖) :=
      ENNReal.ofReal_add (mul_nonneg hw (norm_nonneg _)) (mul_nonneg hw (norm_nonneg _))
    _ ≤ _ := add_le_add
      (le_iSup_of_le t (le_iSup (fun n => ENNReal.ofReal (zWeight L Λ n * ‖f t n‖)) n))
      (le_iSup_of_le t (le_iSup (fun n => ENNReal.ofReal (zWeight L Λ n * ‖g t n‖)) n))

theorem zSpace_add {d p : ℕ} {L Λ : ℝ} {f g : ZTime p → (Fin d → ℤ) → ℂ}
    (hf : f ∈ ZSpace L Λ p) (hg : g ∈ ZSpace L Λ p) : f + g ∈ ZSpace L Λ p :=
  ⟨fun n => (hf.1 n).add (hg.1 n),
    (ZNorm_add_le L Λ f g).trans_lt (ENNReal.add_lt_top.mpr ⟨hf.2, hg.2⟩)⟩

end WaveTurbulence.Fixedpt
