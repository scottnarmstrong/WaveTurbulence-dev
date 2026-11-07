/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVN12
public import WaveTurbulence.Foundations.Stage1.Represents.RepNode2
public import WaveTurbulence.Foundations.Stage1.Represents.RepH5
import Mathlib.Tactic

/-!
# S2 REPRESENTS, F-LEAFCLK: hinge data with the clock of a leaf lower child decoupled

The clock of a leaf lower child of a unit is the root time of its tree, which lies above the hinge clock and so outside
`outBox`.  The unit kernel does not depend on it (`hind`, from `unitKernelM_clocks` / `clRecenteredLocalKernelModC_congr`).
`HingeFam.leafWrap` zeroes the frequency of the leaf coordinates and absorbs `e^{πi m·t_d}` (a dummy time `td`) into the
amplitude; `exists_hinge_data_units_leaf` is `exists_hinge_data_units` with G1 asked only at the clock tuple whose leaf
coordinates are replaced by `td`, and the superposition identity delivered at the actual clocks.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C VineParamContract
open scoped ENNReal

theorem fsPhase_leaf_split {r : ℕ} (leaf : Fin r → Prop) [DecidablePred leaf] (m : Fin r → ℤ) (t td : Fin r → ℝ) :
    fsPhase m (fun i => if leaf i then td i else t i) =
      fsPhase (fun i => if leaf i then 0 else m i) t * fsPhase (fun i => if leaf i then m i else 0) td := by
  rw [fsPhase_eq_prod, fsPhase_eq_prod, fsPhase_eq_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : leaf i <;> simp [h]

/-- Zero the frequencies of the leaf coordinates; absorb their phase at the dummy time `td` into the amplitude. -/
noncomputable def HingeFam.leafWrap {J : Type} {d : ℕ} (H : HingeFam J d) (leaf : J → Fin 3 → Prop)
    [∀ j i, Decidable (leaf j i)] (td : J → Fin 3 → ℝ) : HingeFam J d where
  Λ := H.Λ
  cnt := H.cnt
  w := H.w
  m j c l := fun i => if leaf j i then 0 else H.m j c l i
  a j c l E := H.a j c l E * fsPhase (fun i => if leaf j i then H.m j c l i else 0) (td j)
  w_nn := H.w_nn
  w_sum := H.w_sum
  a_one j c l E := by
    rw [norm_mul, fsPhase_norm, mul_one]
    exact H.a_one j c l E

theorem HingeFam.leafWrap_hasSum {J : Type} {d : ℕ} (H : HingeFam J d) (leaf : J → Fin 3 → Prop)
    [∀ j i, Decidable (leaf j i)] (td : J → Fin 3 → ℝ) (j : J) (c : Fin 4 → Fin d → ℤ) (E : Fin 4 → Mom d)
    (t : Fin 3 → ℝ) {F : ℂ}
    (h : HasSum (fun l => (H.w j c l : ℂ) * H.a j c l E *
      fsPhase (H.m j c l) (fun i => if leaf j i then td j i else t i)) F) :
    HasSum (fun l => ((H.leafWrap leaf td).w j c l : ℂ) * (H.leafWrap leaf td).a j c l E *
      fsPhase ((H.leafWrap leaf td).m j c l) t) F := by
  have e : (fun l : H.Λ j c => ((H.leafWrap leaf td).w j c l : ℂ) * (H.leafWrap leaf td).a j c l E *
      fsPhase ((H.leafWrap leaf td).m j c l) t) =
      fun l : H.Λ j c => (H.w j c l : ℂ) * H.a j c l E *
        fsPhase (H.m j c l) (fun i => if leaf j i then td j i else t i) := by
    funext l
    show (H.w j c l : ℂ) * (H.a j c l E * fsPhase (fun i => if leaf j i then H.m j c l i else 0) (td j)) *
        fsPhase (fun i => if leaf j i then 0 else H.m j c l i) t = _
    rw [fsPhase_leaf_split (leaf j) (H.m j c l) t (td j)]
    ring
  show HasSum (fun l : H.Λ j c => ((H.leafWrap leaf td).w j c l : ℂ) * (H.leafWrap leaf td).a j c l E *
      fsPhase ((H.leafWrap leaf td).m j c l) t) F
  rw [e]
  exact h

/-- `exists_hinge_data_mod` with an arbitrary clock tuple `ck` in place of `clockOf ∘ hclk`. -/
theorem exists_hinge_data_mod_ck {θ : ℝ} (hθ : 0 ≤ θ) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {w : ℕ} (S : Garden w) (J : Type) [Fintype J] (Dj : J → (Fin 4 → Fin d → ℤ) → SumintDatum d)
      (Kj : J → (Fin 4 → Fin d → ℤ) → Set (Fin 4 → Mom d)) (σ : J → ℤˣ)
      (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) (M0 : J → ℝ) (c : ℝ), (∀ j, 0 ≤ M0 j) →
      (∀ j c' lam, ∀ E ∈ Kj j c', ContinuousOn (fun t => HkM j lam t (sumintBoundary (σ j) E)) (cubeSet (Dj j c').qOut)) →
      (∀ j c' (lam : ℤ), XNorm00Restr θ (outBox (Dj j c')) (Kj j c')
        (fun t E => HkM j lam t (sumintBoundary (σ j) E)) ≤
        ENNReal.ofReal ((1 + |(lam : ℝ)|) ^ c * M0 j)) →
      ∀ (L : ℝ) (base : Mom d) (tt : Fin w → ℝ) (roots : Fin w → Fin d → ℤ)
        (selSk : GenDecoration S d roots 0 → Prop) (layer : GBranch S.tree → ℕ)
        (hmom : J → Fin 4 → GNode S.tree) (ck : J → (GBranch S.tree → ℝ) → Fin 3 → ℝ),
      (∀ κ : GenDecoration S d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain S layer tt, ∀ j c',
        (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c' i)‖ ≤ 1) →
          ck j τ ∈ outBox (Dj j c')) →
      (∀ κ : GenDecoration S d roots 0, selSk κ → ∀ j c',
        (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c' i)‖ ≤ 1) →
          sumintBoundary (σ j) (fun i => base + latticePoint L (κ.1 (hmom j i))) ∈ Kj j c') →
      ∀ lam : J → ℤ, ∃ (H : HingeFam J d) (Mh : J → ℝ), (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
        (∀ κ : GenDecoration S d roots 0, selSk κ → ∀ τ ∈ splicedTimeDomain S layer tt, ∀ j c',
          (∀ i, ‖(base + latticePoint L (κ.1 (hmom j i))) - latPt d (c' i)‖ ≤ 1) →
          HasSum (fun l => (H.w j c' l : ℂ) * H.a j c' l (fun i => base + latticePoint L (κ.1 (hmom j i))) *
            fsPhase (H.m j c' l) (ck j τ))
            (HkM j (lam j) (ck j τ) (fun i => base + latticePoint L (κ.1 (hmom j i))))) ∧
        ∏ j, Mh j = C ^ Fintype.card J * (∏ j, M0 j) * ∏ j, (1 + |((lam j : ℤ) : ℝ)|) ^ c := by
  obtain ⟨C, hC, hex⟩ := exists_hingeFam hθ d
  refine ⟨C, hC, fun {w} S J _ Dj Kj σ HkM M0 c hM0 hcont hbd L base tt roots selSk layer hmom ck G1 G2 lam => ?_⟩
  obtain ⟨H, hH1, hH2⟩ := hex J Dj Kj σ (fun j => HkM j (lam j))
    (fun j => (1 + |((lam j : ℤ) : ℝ)|) ^ c * M0 j)
    (fun j => mul_nonneg (by positivity) (hM0 j)) (fun j c' E hE => hcont j c' (lam j) E hE)
    (fun j c' => hbd j c' (lam j))
  refine ⟨H, fun j => C * ((1 + |((lam j : ℤ) : ℝ)|) ^ c * M0 j), fun j c' => hH1 j c', fun κ hκ τ hτ j c' hball =>
    hH2 j c' _ (G1 κ hκ τ hτ j c' hball) _ (G2 κ hκ j c' hball), ?_⟩
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  ring

end WaveTurbulence.Represents
