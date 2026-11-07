/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.Analysis
public import WaveTurbulence.Foundations.VineEst.VineEstS3.RestrScalar

/-! # P4-W1: separated expansions with an identity set, and their window certificates (generic)

`ObjExp d f`: a separated expansion `f(t,s,k) = ∑ᵢ c Jᵢ(t,s) Mᵢ(k)` valid on an identity set `V ⊆ ℝ²` (at least one term).
`ObjExp.term`: the term `i`, equal to the separated term `sepTerm c Jᵢ Mᵢ` on `V`, and to the fallback `f` (term `0`) resp. `0`
off `V`, so that `f = ∑ᵢ termᵢ` holds at EVERY point (`ObjExp.sum_term`).  The family `P4.SepFam` asks the expansion identity at all
points of its `PtOK`; with the fallback, `PtOK := True` works, and the pieces of the bundle only read the terms at points of `V`
(`term_of_mem`), where they are separated terms.

`ObjExp.ofPad`: from an expansion with `m₀ ≥ 0` terms, padded by zero terms to `max m₀ 1`.
`ObjCert`: an `ObjExp` together with `P2.SepT` certificates of every term on two window boxes `Blo`, `Bhi` with common constants
`CJ`, `CM` (the data the `P2.piece_*` bounds consume).  `sepTPad`: the certificate of a padded term.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W13
open WaveTurbulence WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS3.FS MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- A separated expansion of `f` valid on the identity set `V`. -/
structure ObjExp (d : ℕ) (f : ℝ → ℝ → Mom d → ℂ) where
  m : ℕ
  hm : 1 ≤ m
  c : ℝ
  J : Fin m → (Fin 2 → ℝ) → ℂ
  M : Fin m → Mom d → ℝ
  V : Set (Fin 2 → ℝ)
  hV : ∀ t s : ℝ, ![t, s] ∈ V → ∀ k, f t s k = ∑ i, sepTerm c (J i) (M i) t s k

namespace ObjExp
variable {f : ℝ → ℝ → Mom d → ℂ} (E : ObjExp d f)

open Classical in
/-- The term `i`: the separated term on `V`, the fallback (`f` for `i = 0`, `0` otherwise) off `V`. -/
noncomputable def term (i : Fin E.m) (t s : ℝ) (k : Mom d) : ℂ :=
  if ![t, s] ∈ E.V then sepTerm E.c (E.J i) (E.M i) t s k else if i.val = 0 then f t s k else 0

theorem term_of_mem {t s : ℝ} (h : ![t, s] ∈ E.V) (i : Fin E.m) (k : Mom d) :
    E.term i t s k = sepTerm E.c (E.J i) (E.M i) t s k := by
  classical
  unfold term
  rw [if_pos h]

/-- **The expansion holds at every point.** -/
theorem sum_term (t s : ℝ) (k : Mom d) : f t s k = ∑ i, E.term i t s k := by
  classical
  by_cases h : ![t, s] ∈ E.V
  · rw [E.hV t s h k]
    exact Finset.sum_congr rfl fun i _ => (E.term_of_mem h i k).symm
  · have e : ∀ i, E.term i t s k = if i = ⟨0, E.hm⟩ then f t s k else 0 := fun i => by
      unfold term
      rw [if_neg h]
      by_cases hi : i.val = 0
      · rw [if_pos hi, if_pos (Fin.ext hi)]
      · rw [if_neg hi, if_neg (fun he => hi (by rw [he]))]
    simp_rw [e]
    rw [Finset.sum_ite_eq' Finset.univ (⟨0, E.hm⟩ : Fin E.m), if_pos (Finset.mem_univ _)]

end ObjExp

section Pad
variable {m₀ : ℕ}

/-- The time factor of a padded term. -/
noncomputable def padJ (J₀ : Fin m₀ → (Fin 2 → ℝ) → ℂ) (i : Fin (max m₀ 1)) : (Fin 2 → ℝ) → ℂ :=
  if h : i.val < m₀ then J₀ ⟨i.val, h⟩ else fun _ => 0

/-- The momentum factor of a padded term. -/
noncomputable def padM (M₀ : Fin m₀ → Mom d → ℝ) (i : Fin (max m₀ 1)) : Mom d → ℝ :=
  if h : i.val < m₀ then M₀ ⟨i.val, h⟩ else fun _ => 0

theorem sum_pad (c : ℝ) (J₀ : Fin m₀ → (Fin 2 → ℝ) → ℂ) (M₀ : Fin m₀ → Mom d → ℝ) (t s : ℝ) (k : Mom d) :
    ∑ i : Fin (max m₀ 1), sepTerm c (padJ J₀ i) (padM M₀ i) t s k = ∑ i : Fin m₀, sepTerm c (J₀ i) (M₀ i) t s k := by
  classical
  set g : ℕ → ℂ := fun n => if h : n < m₀ then sepTerm c (J₀ ⟨n, h⟩) (M₀ ⟨n, h⟩) t s k else 0 with hg
  have e1 : ∀ i : Fin (max m₀ 1), sepTerm c (padJ J₀ i) (padM M₀ i) t s k = g i.val := fun i => by
    unfold padJ padM
    by_cases h : i.val < m₀
    · simp only [hg, dif_pos h]
    · simp only [hg, dif_neg h, sepTerm]; simp
  have e2 : ∀ i : Fin m₀, sepTerm c (J₀ i) (M₀ i) t s k = g i.val := fun i => by simp only [hg, dif_pos i.2]
  simp_rw [e1, e2]
  rw [Fin.sum_univ_eq_sum_range g, Fin.sum_univ_eq_sum_range g]
  refine (Finset.sum_subset (Finset.range_subset_range.2 (le_max_left m₀ 1)) fun n _ hn => ?_).symm
  have : ¬ n < m₀ := fun h => hn (Finset.mem_range.2 h)
  simp only [hg, dif_neg this]

/-- **The padded expansion.** -/
noncomputable def ObjExp.ofPad {f : ℝ → ℝ → Mom d → ℂ} (c : ℝ) (J₀ : Fin m₀ → (Fin 2 → ℝ) → ℂ) (M₀ : Fin m₀ → Mom d → ℝ)
    (V : Set (Fin 2 → ℝ)) (hV : ∀ t s : ℝ, ![t, s] ∈ V → ∀ k, f t s k = ∑ i, sepTerm c (J₀ i) (M₀ i) t s k) : ObjExp d f where
  m := max m₀ 1
  hm := le_max_right _ _
  c := c
  J := padJ J₀
  M := padM M₀
  V := V
  hV t s h k := by rw [sum_pad]; exact hV t s h k

/-- The expansion with no identity set (one fallback term). -/
noncomputable def ObjExp.triv (f : ℝ → ℝ → Mom d → ℂ) : ObjExp d f where
  m := 1
  hm := le_rfl
  c := 0
  J := fun _ _ => 0
  M := fun _ _ => 0
  V := ∅
  hV _ _ h := absurd h (Set.notMem_empty _)

end Pad

/-- **A certified separated expansion**: an `ObjExp` with `P2.SepT` certificates of every term on the two window boxes. -/
structure ObjCert (P : WTParams) (Wm : ℕ) (f : ℝ → ℝ → Mom P.d → ℂ) (Blo Bhi : Set (Fin 2 → ℝ)) (qlo qhi : Fin 2 → ℝ)
    extends ObjExp P.d f where
  CJ : ℝ
  CM : ℝ
  lo : Fin m → SepT P Wm Blo qlo CJ CM
  hi : Fin m → SepT P Wm Bhi qhi CJ CM
  lo_c : ∀ i, (lo i).c = c
  lo_J : ∀ i, (lo i).J = J i
  lo_M : ∀ i, (lo i).M = M i
  hi_c : ∀ i, (hi i).c = c
  hi_J : ∀ i, (hi i).J = J i
  hi_M : ∀ i, (hi i).M = M i

section SepTPad
variable {P : WTParams} {Wm : ℕ} {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} {CJ CM : ℝ}

theorem SNormR_zero_fn (Λ₁ Λ₂ : ℕ) : SNormR Λ₁ Λ₂ (fun _ : Mom P.d => (0 : ℝ)) = 0 := by
  unfold SNormR
  simpa using SNorm_zero' (d := P.d) Λ₁ Λ₂

/-- The `SepT` certificate of a padded term. -/
noncomputable def sepTPad {m₀ : ℕ} (hc : B ⊆ cell q) (hi : B ⊆ closure (interior B)) (hCJ : 0 < CJ) (hCM : 0 ≤ CM) (c : ℝ)
    (J₀ : Fin m₀ → (Fin 2 → ℝ) → ℂ) (M₀ : Fin m₀ → Mom P.d → ℝ)
    (hJ : ∀ i, XNorm00Restr (V := Unit) (1 - P.η) B Set.univ (fun ts _ => J₀ i ts) < ENNReal.ofReal CJ)
    (hM : ∀ i, SNormR (30 * P.d) Wm (M₀ i) ≤ ENNReal.ofReal CM) (i : Fin (max m₀ 1)) : SepT P Wm B q CJ CM where
  c := c
  J := padJ J₀ i
  M := padM M₀ i
  hcell := hc
  hint := hi
  hCJ := hCJ.le
  hCM := hCM
  hJ := by
    unfold padJ
    by_cases h : i.val < m₀
    · rw [dif_pos h]; exact hJ _
    · rw [dif_neg h]
      rw [VineEstS3.Eng.XNorm00Restr_zero]
      exact ENNReal.ofReal_pos.2 hCJ
  hM := by
    unfold padM
    by_cases h : i.val < m₀
    · rw [dif_pos h]; exact hM _
    · rw [dif_neg h, SNormR_zero_fn]; exact zero_le

end SepTPad

end WaveTurbulence.VineEstS5C.P4.W13
