/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.ZpSurjStmt
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.BundleAbs
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.BundleAlg
public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4KConj

/-! # The bundle of a level in the pairing form (V5 Step 4d part C, WP-B step 3)

Given `hZ : ZpSurj`, the index type is the set of states of `Zp(A)`: `bsB` (all II-b states), `bsA` (the II-b states with
carrier-side roots `<= L4`, which stand for the twin pairs `{G, τ G}`, and the II-a states with a root `> L4`, which are
unpaired).  Carrier-side approximants `Qf`, `Tf` (ANY functions of the index; `srcQ`, `srcT` are the `SourceApp` instances) and remainders `remQ`, `remT`
(exact kernel minus approximant) are functions of the index only.  `bundle_eq_repl`: the exact bundle `psiSB` is
`frame * νA * (replSum (approximants) + remainder rows)`; no approximant-conjugation theorem is used: the barred approximants
are the conjugate-swaps (`cswap`, `cconj`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.ConjCoh TTree
  WaveTurbulence.VineEstS4c

theorem units_ne_one_iff (ν : ℤˣ) : ν ≠ 1 ↔ ν = -1 := by
  rcases Int.units_eq_one_or ν with rfl | rfl <;> decide

section
variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} {d : ℕ} [Fintype ι] [DecidableEq ι]

/-- The source approximant (at the parameters `zpQQ`) of the carrier-side couple of the index `b`. -/
noncomputable def srcQ (κ : KPar d) (b : ST w ι pstar J) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => LGSpine.SourceApp.couple κ.δ κ.F (zpObjC b.1 pstar) (zpCodeC b.1 pstar) (zpQQ b.1 pstar).1
    (zpQQ b.1 pstar).2 t s k

/-- The source approximant (at the parameters `zpBranchQ`) of the carrier-side tree of the index `b`. -/
noncomputable def srcT (κ : KPar d) (b : ST w ι pstar J) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => LGSpine.SourceApp.tree κ.δ κ.F (zpObjT b.1 pstar) (zpCodeT b.1 pstar) (zpBranchQ b.1 pstar).1
    (zpBranchQ b.1 pstar).2 t s k

/-- The remainder of the carrier-side couple: exact kernel minus approximant. -/
noncomputable def remQ (κ : KPar d) (Qf : ST w ι pstar J → ℝ → ℝ → Mom d → ℂ) (b : ST w ι pstar J) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => KQstar κ.L κ.γ κ.δ κ.F (zpObjC b.1 pstar) t s k - Qf b t s k

/-- The remainder of the carrier-side tree. -/
noncomputable def remT (κ : KPar d) (Tf : ST w ι pstar J → ℝ → ℝ → Mom d → ℂ) (b : ST w ι pstar J) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => KTstar κ.L κ.γ κ.δ κ.F (zpObjT b.1 pstar) t s k - Tf b t s k


variable (κ : KPar d) (Qf Tf : ST w ι pstar J → ℝ → ℝ → Mom d → ℂ)

theorem zpObjC_of_neg {G : FamilyReconstruction w ι} {i : ι} (h : nuOf G i = -1) : zpObjC G i = (sigStar G i).2.1 := by
  classical
  simp [zpObjC, h]

theorem zpObjT_of_neg {G : FamilyReconstruction w ι} {i : ι} (h : nuOf G i = -1) :
    zpObjT G i = conjLayered (sigStar G i).2.2 (Equiv.refl (Fin 1)) := by
  classical
  simp [zpObjT, h]

theorem zpObjC_of_pos {G : FamilyReconstruction w ι} {i : ι} (h : nuOf G i = 1) :
    zpObjC G i = conjLayered (sigStar G i).2.1 (Equiv.swap (0 : Fin 2) 1) := by
  classical
  have : ¬ nuOf G i = -1 := by rw [h]; decide
  simp [zpObjC, this]

theorem zpObjT_of_pos {G : FamilyReconstruction w ι} {i : ι} (h : nuOf G i = 1) : zpObjT G i = (sigStar G i).2.2 := by
  classical
  have : ¬ nuOf G i = -1 := by rw [h]; decide
  simp [zpObjT, this]

/-- Exact rows of a II-b index: `K*_Q = Q + R_Q`. -/
theorem rowQ_B (b : ST w ι pstar J) (hb : nuOf b.1 pstar ≠ 1) (t s : ℝ) (k : Mom d) :
    rowQ κ b.1 pstar t s k = Qf b t s k + remQ κ Qf b t s k := by
  have h := (units_ne_one_iff _).mp hb
  unfold remQ rowQ
  rw [zpObjC_of_neg h]; ring

/-- Exact tree row of a II-b index: `K*_{T̄} = T̄ + conj R_T`. -/
theorem rowT_B (b : ST w ι pstar J) (hb : nuOf b.1 pstar ≠ 1) (t s : ℝ) (k : Mom d) :
    rowT κ b.1 pstar t s k = cconj (Tf) b t s k + (starRingEnd ℂ) (remT κ Tf b t s k) := by
  have h := (units_ne_one_iff _).mp hb
  have hc := PL234.KTstar_conj κ.L κ.γ κ.δ κ.F (conjLayered_isConjugateBy (sigStar b.1 pstar).2.2 (Equiv.refl (Fin 1))) t s k
  unfold remT rowT cconj
  rw [zpObjT_of_neg h, hc, map_sub]
  simp


variable (τ : ST w ι pstar J → ST w ι pstar J)

open Classical in
/-- The II-a state standing for the index `b`: `b` itself if it is a II-a state (unpaired), its twin `τ b` otherwise. -/
noncomputable def bsigma (b : ST w ι pstar J) : ST w ι pstar J := if nuOf b.1 pstar = 1 then b else τ b

variable (p kind J)

open Classical in
/-- The index set of the II-b terms: all II-b states of `Zp(A)`. -/
noncomputable def bsB (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) : Finset (ST w ι pstar J) :=
  (zpFinset p kind pstar J A sp0 hA).filter fun G => nuOf G.1 pstar ≠ 1

open Classical in
/-- The index set of the II-a terms: twin pairs (indexed by the II-b member) and the unpaired II-a states (a root `> L4`). -/
noncomputable def bsA (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) : Finset (ST w ι pstar J) :=
  (zpFinset p kind pstar J A sp0 hA).filter fun G =>
    (nuOf G.1 pstar ≠ 1 ∧ ZpRootsLE A G.1 pstar) ∨ (nuOf G.1 pstar = 1 ∧ ¬ ZpRootsLE A G.1 pstar)

variable {p kind J}

/-- Exact couple row of the II-a state standing for an index of `bsA`: `K*_{Q̄} = Q̄ + conj R_Q`. -/
theorem rowQ_A {b : ST w ι pstar J} (hb : (nuOf b.1 pstar = 1) ∨
      (nuOf b.1 pstar ≠ 1 ∧ IsConjugateCouple (sigStar b.1 pstar).2.1 (sigStar (τ b).1 pstar).2.1))
    (t s : ℝ) (k : Mom d) :
    rowQ κ (bsigma τ b).1 pstar t s k = cswap (Qf) b t s k + (starRingEnd ℂ) (remQ κ Qf b s t k) := by
  classical
  unfold cswap remQ rowQ bsigma
  rcases hb with h | ⟨h, hc⟩
  · rw [if_pos h, zpObjC_of_pos h]
    have := PL234.KQstar_conj κ.L κ.γ κ.δ κ.F (conjLayered_isConjugateBy (sigStar b.1 pstar).2.1 (Equiv.swap (0 : Fin 2) 1)) s t k
    rw [map_sub, ← sub_eq_zero]
    rw [this]; simp
  · have h' := (units_ne_one_iff _).mp h
    rw [if_neg h, zpObjC_of_neg h', PL234.KQstar_conj κ.L κ.γ κ.δ κ.F hc t s k]
    simp

/-- Exact tree row of the II-a state standing for an index of `bsA`: `K*_T = T + R_T`. -/
theorem rowT_A {b : ST w ι pstar J} (hb : (nuOf b.1 pstar = 1) ∨
      (nuOf b.1 pstar ≠ 1 ∧ IsConjugateTree (sigStar b.1 pstar).2.2 (sigStar (τ b).1 pstar).2.2))
    (t s : ℝ) (k : Mom d) :
    rowT κ (bsigma τ b).1 pstar t s k = Tf b t s k + remT κ Tf b t s k := by
  classical
  unfold remT rowT bsigma
  rcases hb with h | ⟨h, hc⟩
  · rw [if_pos h, zpObjT_of_pos h]; ring
  · have h' := (units_ne_one_iff _).mp h
    rw [if_neg h, zpObjT_of_neg h', PL234.KTstar_conj κ.L κ.γ κ.δ κ.F hc t s k,
      PL234.KTstar_conj κ.L κ.γ κ.δ κ.F (conjLayered_isConjugateBy (sigStar b.1 pstar).2.2 (Equiv.refl (Fin 1))) t s k]
    ring


section Reindex
variable (p kind J)

open Classical in
theorem sum_bsA_reindex (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hbij : Set.BijOn τ (zpSet p kind pstar J A sp0 hA (-1)) (zpSet p kind pstar J A sp0 hA 1))
    (F : ST w ι pstar J → ℂ) :
    ∑ b ∈ bsA p kind J A sp0 hA, F (bsigma τ b) =
      ∑ G ∈ (zpFinset p kind pstar J A sp0 hA).filter (fun G => nuOf G.1 pstar = 1), F G := by
  refine Finset.sum_nbij (bsigma τ) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro b hb
    simp only [bsA, Finset.mem_filter] at hb
    simp only [Finset.mem_filter]
    unfold bsigma
    rcases hb with ⟨hz, ⟨hn, hr⟩ | ⟨hn, hr⟩⟩
    · have hbm : b ∈ zpSet p kind pstar J A sp0 hA (-1) := ⟨hz, (units_ne_one_iff _).mp hn, hr⟩
      rw [if_neg hn]
      have := hbij.mapsTo hbm
      exact ⟨this.1, this.2.1⟩
    · rw [if_pos hn]; exact ⟨hz, hn⟩
  · intro b1 hb1 b2 hb2 he
    simp only [Finset.mem_coe, bsA, Finset.mem_filter] at hb1 hb2
    unfold bsigma at he
    by_cases h1 : nuOf b1.1 pstar = 1 <;> by_cases h2 : nuOf b2.1 pstar = 1
    · rw [if_pos h1, if_pos h2] at he; exact he
    · rw [if_pos h1, if_neg h2] at he
      have hb2m : b2 ∈ zpSet p kind pstar J A sp0 hA (-1) := by
        rcases hb2 with ⟨hz, ⟨hn, hr⟩ | ⟨hn, _⟩⟩
        · exact ⟨hz, (units_ne_one_iff _).mp hn, hr⟩
        · exact absurd hn h2
      have hm := (hbij.mapsTo hb2m)
      rw [← he] at hm
      rcases hb1 with ⟨_, ⟨hn, _⟩ | ⟨_, hr⟩⟩
      · exact absurd h1 hn
      · exact absurd hm.2.2 hr
    · rw [if_neg h1, if_pos h2] at he
      have hb1m : b1 ∈ zpSet p kind pstar J A sp0 hA (-1) := by
        rcases hb1 with ⟨hz, ⟨hn, hr⟩ | ⟨hn, _⟩⟩
        · exact ⟨hz, (units_ne_one_iff _).mp hn, hr⟩
        · exact absurd hn h1
      have hm := (hbij.mapsTo hb1m)
      rw [he] at hm
      rcases hb2 with ⟨_, ⟨hn, _⟩ | ⟨_, hr⟩⟩
      · exact absurd h2 hn
      · exact absurd hm.2.2 hr
    · rw [if_neg h1, if_neg h2] at he
      have hm : ∀ b : ST w ι pstar J, b ∈ bsA p kind J A sp0 hA → ¬ nuOf b.1 pstar = 1 →
          b ∈ zpSet p kind pstar J A sp0 hA (-1) := by
        intro b hb hn
        simp only [bsA, Finset.mem_filter] at hb
        rcases hb with ⟨hz, ⟨hn', hr⟩ | ⟨hn', _⟩⟩
        · exact ⟨hz, (units_ne_one_iff _).mp hn', hr⟩
        · exact absurd hn' hn
      exact hbij.injOn (hm b1 (by simp only [bsA, Finset.mem_filter]; exact hb1) h1)
        (hm b2 (by simp only [bsA, Finset.mem_filter]; exact hb2) h2) he
  · intro G hG
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hG
    by_cases hr : ZpRootsLE A G.1 pstar
    · have hGm : G ∈ zpSet p kind pstar J A sp0 hA 1 := ⟨hG.1, hG.2, hr⟩
      obtain ⟨b, hb, hbG⟩ := hbij.surjOn hGm
      refine ⟨b, ?_, ?_⟩
      · simp only [Finset.mem_coe, bsA, Finset.mem_filter]
        exact ⟨hb.1, Or.inl ⟨by rw [hb.2.1]; decide, hb.2.2⟩⟩
      · unfold bsigma
        have : ¬ nuOf b.1 pstar = 1 := by rw [hb.2.1]; decide
        rw [if_neg this]; exact hbG
    · refine ⟨G, ?_, ?_⟩
      · simp only [Finset.mem_coe, bsA, Finset.mem_filter]
        exact ⟨hG.1, Or.inr ⟨hG.2, hr⟩⟩
      · unfold bsigma; rw [if_pos hG.2]


open Classical in
/-- **The exact bundle in the pairing form** (TARGET (replaceterm1) with the remainder rows):
`psiSB = frame * νA * (replSum approximants + ∑ remA - ∑ remB)`. -/
theorem bundle_eq_repl (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hbij : Set.BijOn τ (zpSet p kind pstar J A sp0 hA (-1)) (zpSet p kind pstar J A sp0 hA 1))
    (hrel : ∀ G ∈ zpSet p kind pstar J A sp0 hA (-1),
      IsConjugateCouple (sigStar G.1 pstar).2.1 (sigStar (τ G).1 pstar).2.1 ∧
      IsConjugateTree (sigStar G.1 pstar).2.2 (sigStar (τ G).1 pstar).2.2)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (u : GBranch A.skeleton.tree → ℝ) :
    psiSB (p := p) (kind := kind) κ A sp0 hA x u = bundleFrame κ A sp0 x u * (((nuOf A pstar : ℤˣ) : ℂ) *
      (replSum (bsA p kind J A sp0 hA) (bsB p kind J A sp0 hA) (Qf) (cswap (Qf)) (Tf) (cconj (Tf))
          (bundleVars κ A sp0 x u).1 (bundleVars κ A sp0 x u).2.1 (bundleVars κ A sp0 x u).2.2.1
          (bundleVars κ A sp0 x u).2.2.2.1 (bundleVars κ A sp0 x u).2.2.2.2 +
        (∑ b ∈ bsA p kind J A sp0 hA, remA (Qf) (Tf) (remQ κ Qf) (remT κ Tf) b
            (bundleVars κ A sp0 x u).1 (bundleVars κ A sp0 x u).2.1 (bundleVars κ A sp0 x u).2.2.1
            (bundleVars κ A sp0 x u).2.2.2.1 (bundleVars κ A sp0 x u).2.2.2.2 -
          ∑ b ∈ bsB p kind J A sp0 hA, remB (Qf) (Tf) (remQ κ Qf) (remT κ Tf) b
            (bundleVars κ A sp0 x u).1 (bundleVars κ A sp0 x u).2.1 (bundleVars κ A sp0 x u).2.2.1
            (bundleVars κ A sp0 x u).2.2.2.1 (bundleVars κ A sp0 x u).2.2.2.2))) := by
  rw [psiSB_eq_dict]
  congr 2
  rw [← sum_bsA_reindex p kind J τ A sp0 hA hbij, ← exact_eq_repl_add_rem]
  congr 1
  · refine Finset.sum_congr rfl fun b hb => ?_
    have hb' := Finset.mem_filter.mp hb
    have hr1 : (nuOf b.1 pstar = 1) ∨ (nuOf b.1 pstar ≠ 1 ∧
        IsConjugateCouple (sigStar b.1 pstar).2.1 (sigStar (τ b).1 pstar).2.1) := by
      rcases hb'.2 with ⟨hn, hr⟩ | ⟨hn, _⟩
      · exact Or.inr ⟨hn, (hrel b ⟨hb'.1, (units_ne_one_iff _).mp hn, hr⟩).1⟩
      · exact Or.inl hn
    have hr2 : (nuOf b.1 pstar = 1) ∨ (nuOf b.1 pstar ≠ 1 ∧
        IsConjugateTree (sigStar b.1 pstar).2.2 (sigStar (τ b).1 pstar).2.2) := by
      rcases hb'.2 with ⟨hn, hr⟩ | ⟨hn, _⟩
      · exact Or.inr ⟨hn, (hrel b ⟨hb'.1, (units_ne_one_iff _).mp hn, hr⟩).2⟩
      · exact Or.inl hn
    have e1 : rowQ κ (bsigma τ b).1 pstar =
        fun t s k => cswap (Qf) b t s k + (starRingEnd ℂ) (remQ κ Qf b s t k) :=
      funext fun t => funext fun s => funext fun k => rowQ_A κ Qf τ hr1 t s k
    have e2 : rowT κ (bsigma τ b).1 pstar = fun t s k => Tf b t s k + remT κ Tf b t s k :=
      funext fun t => funext fun s => funext fun k => rowT_A κ Tf τ hr2 t s k
    rw [e1, e2]
  · refine Finset.sum_congr rfl fun b hb => ?_
    have hb' : b ∈ bsB p kind J A sp0 hA := hb
    have hn : nuOf b.1 pstar ≠ 1 := (Finset.mem_filter.mp hb').2
    have e1 : rowQ κ b.1 pstar = fun t s k => Qf b t s k + remQ κ Qf b t s k :=
      funext fun t => funext fun s => funext fun k => rowQ_B κ Qf b hn t s k
    have e2 : rowT κ b.1 pstar = fun t s k => cconj (Tf) b t s k + (starRingEnd ℂ) (remT κ Tf b t s k) :=
      funext fun t => funext fun s => funext fun k => rowT_B κ Tf b hn t s k
    rw [e1, e2]

end Reindex
end
end WaveTurbulence.VineEstS5C
