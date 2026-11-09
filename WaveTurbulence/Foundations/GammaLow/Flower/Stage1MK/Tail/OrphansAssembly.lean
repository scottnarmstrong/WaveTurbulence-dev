/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L8-I-ORPHANS port of main `WaveTurbulence.Foundations.Stage1.ClassCount.Assembly.classCount_of_legsMk` and
-- `…Stage1.Represents.RepCountA.pieceCount_of_repMk` (sha256 in Tail/Orphans-COPIED-SHA256SUMS), over 𝒱_γ.
module
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Tail.OrphansSkeleton
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Tail.OrphansLayering
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P16
public import WaveTurbulence.Foundations.GammaLow.Fama.Gate
public import WaveTurbulence.Foundations.Stage1.ClassCount.Assembly
import Mathlib.Tactic
/-! # Item I orphans: the marked class count from its legs, and the piece count, over `𝒱_γ`

* `classCount_of_legsMkLow` is main's `classCount_of_legsMk` (B2b): the decode-size leg (main's, family-free), Leg 1
  `SkeletonLegMkLow` and Leg 2 `LayeringLegMkLow` give L8's `ClassCountStmtMkLow (fun _ _ _ => True)` (P16) for the
  family `𝒱_γF`. Verbatim up to `rbarOfMk → rbarOfMkG γF`, `stage1PieceOf → Fama.stage1PieceOf γF`,
  `Stage1.CLVine → Fama.CLVineG γF`.
* `pieceCount_of_repMkLow` is main's `pieceCount_of_repMk` (B1b-2) with L8's `MarkAdmLow`/`HasPieceDataMkLow`/
  `ClassCountStmtMkLow` and L5a's `Fama.Stage1DataG` (main `Stage1Data`, pubmap); verbatim.
The section family is `γF` (CONVENTIONS; L8's `ClassCountStmtMkLow` fixes it outside `∀ P`). -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.GammaLow.Flower
open Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg.Skeleton
open WaveTurbulence.GammaLow.Famc.ClassCount (rbarOfMkG)

variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineIsoInvariant]

/-- **Assembly at a marking over `𝒱_γ`** (main `classCount_of_legsMk`): the three legs give the marked class count
with the trivial admissibility. -/
theorem classCount_of_legsMkLow (h0 : WaveTurbulence.ClassCount.DecodeSizeLeg) (h1 : SkeletonLegMkLow)
    (h2 : LayeringLegMkLow (γF := γF)) : ClassCountStmtMkLow (γF := γF) fun _ _ _ => True := by
  classical
  obtain ⟨C₁, hC₁, hsk⟩ := h1
  obtain ⟨C₃, K, hC₃, hlay⟩ := h2
  have h12 : 12 ^ 18 ≤ 2 ^ 65 := by norm_num
  have hC₀a : C₁ + 65 ≤ C₁ * 12 ^ 18 * C₃ := by
    have : C₁ * 12 ^ 18 ≤ C₁ * 12 ^ 18 * C₃ := Nat.le_mul_of_pos_right _ hC₃
    have h3 : 65 + C₁ ≤ C₁ * 12 ^ 18 := by nlinarith
    omega
  have hC₀b : C₁ + C₃ ≤ C₁ * 12 ^ 18 * C₃ := by nlinarith
  refine ⟨C₁ * 12 ^ 18 * C₃, K + 1, by nlinarith, ?_⟩
  intro P hK' p hp R hR N hN g r A hA
  have hK : K ^ (P.D + 1) ≤ P.C₂ :=
    le_trans (by exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ K) _) hK'
  have hC2one : (1 : ℝ) ≤ P.C₂ :=
    le_trans (by exact_mod_cast Nat.one_le_pow _ _ (Nat.succ_pos K)) hK'
  have hC2 : (0 : ℝ) ≤ P.C₂ ^ (g + r) := pow_nonneg (by linarith) _
  set C₀ : ℕ := C₁ * 12 ^ 18 * C₃ with hC₀
  have hex : ∀ LG : A, ∃ t : (Σ S : Garden (2 * R), ReconstructionData S),
      ∃ (hS : t.1.IsPlain) (hd : t.2.Decodes hS LG.1.garden) (σ : Prescription t.1)
        (Mk : Set (Fama.CLVineG γF t.1)), rbarOfMkG γF t.1 σ Mk = r ∧
          (Fama.stage1PieceOf γF P.d hS LG.1 hd σ Mk).gbar = g := by
    intro LG
    obtain ⟨-, S, D, hS, hd, σ, Mk, -, hg, hr⟩ := hA LG.1 LG.2
    exact ⟨⟨S, D⟩, hS, hd, σ, Mk, hr, hg⟩
  choose pick hpick using hex
  have hord : ∀ LG : A, (pick LG).1.order ≤ N ∧ (pick LG).2.size ≤ N := by
    intro LG
    obtain ⟨hS, hd, -⟩ := hpick LG
    have := h0 (pick LG).1 (pick LG).2 hS LG.1.garden hd
    have hN' : LG.1.garden.order = N := (hA LG.1 LG.2).1.2.1
    omega
  set T : Finset (Σ S : Garden (2 * R), ReconstructionData S) := A.attach.image pick with hT
  -- fibers over layered gardens
  have hfib : ∀ t ∈ T, ((A.attach.filter (fun LG => pick LG = t)).card : ℝ) ≤
      (C₃ : ℝ) ^ N * (((C₃ * r).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r) := by
    intro t ht
    obtain ⟨LG0, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hS0, -, -⟩ := hpick LG0
    have hcard : (A.attach.filter (fun LG => pick LG = pick LG0)).card =
        ((A.attach.filter (fun LG => pick LG = pick LG0)).map
          ⟨Subtype.val, Subtype.val_injective⟩).card := by rw [Finset.card_map]
    rw [hcard]
    refine hlay P hK p hp R hR N hN g r (pick LG0).1 (pick LG0).2 _ hS0 (hord LG0).1 ?_
    intro LG' hLG'
    obtain ⟨LG, hLG, rfl⟩ := Finset.mem_map.mp hLG'
    have hLGeq : pick LG = pick LG0 := (Finset.mem_filter.mp hLG).2
    have h := hpick LG
    rw [hLGeq] at h
    exact ⟨(hA LG.1 LG.2).1, h⟩
  -- the skeleton count
  have hskel : ∀ S ∈ T.image Sigma.fst, S.IsPlain ∧ S.order ≤ N ∧
      ∃ (σ : Prescription S) (Mk : Set (Fama.CLVineG γF S)), rbarOfMkG γF S σ Mk = r := by
    intro S hSm
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hSm
    obtain ⟨LG, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hS, hd, σ, Mk, hr, -⟩ := hpick LG
    exact ⟨hS, (hord LG).1, σ, Mk, hr⟩
  have hTS := hsk γF (Fact.out) R N r hR hN (T.image Sigma.fst) hskel
  have hdat : ∀ S ∈ T.image Sigma.fst, (T.filter (fun t => t.1 = S)).card ≤ (12 ^ 18) ^ (N + R) := by
    intro S hSm
    obtain ⟨hSp, hSo, -⟩ := hskel S hSm
    refine WaveTurbulence.ClassCount.card_sigma_fiber_le S hSp (N + R) (by omega) (by omega) (by omega) _ ?_
    intro t ht
    obtain ⟨ht1, ht2⟩ := Finset.mem_filter.mp ht
    obtain ⟨LG, -, rfl⟩ := Finset.mem_image.mp ht1
    exact ⟨ht2, by have := (hord LG).2; omega⟩
  have hTcard : (T.card : ℝ) ≤ ((C₁ : ℝ) ^ N * (((C₁ * r).factorial : ℕ) : ℝ) * (((C₁ * R).factorial : ℕ) : ℝ)) *
      (((12 : ℝ) ^ 18) ^ (N + R)) := by
    have h1 : T.card = ∑ S ∈ T.image Sigma.fst, (T.filter (fun t => t.1 = S)).card :=
      Finset.card_eq_sum_card_image _ _
    have h2 : T.card ≤ (T.image Sigma.fst).card * (12 ^ 18) ^ (N + R) := by
      rw [h1]
      calc ∑ S ∈ T.image Sigma.fst, (T.filter (fun t => t.1 = S)).card
          ≤ ∑ S ∈ T.image Sigma.fst, (12 ^ 18) ^ (N + R) := Finset.sum_le_sum hdat
        _ = _ := by simp
    have h3 : (T.card : ℝ) ≤ ((T.image Sigma.fst).card : ℝ) * (((12 : ℝ) ^ 18) ^ (N + R)) := by
      exact_mod_cast h2
    refine h3.trans ?_
    exact mul_le_mul_of_nonneg_right hTS (by positivity)
  -- total
  have hA1 : A.card = ∑ t ∈ T, (A.attach.filter (fun LG => pick LG = t)).card := by
    rw [← Finset.card_attach (s := A)]
    exact Finset.card_eq_sum_card_image _ _
  have hAcard : (A.card : ℝ) ≤ (T.card : ℝ) * ((C₃ : ℝ) ^ N * (((C₃ * r).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r)) := by
    rw [hA1]; push_cast
    calc ∑ t ∈ T, ((A.attach.filter (fun LG => pick LG = t)).card : ℝ)
        ≤ ∑ t ∈ T, ((C₃ : ℝ) ^ N * (((C₃ * r).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r)) := Finset.sum_le_sum hfib
      _ = _ := by simp
  -- arithmetic
  have hfact1 : ((C₁ * r).factorial : ℝ) * ((C₃ * r).factorial : ℝ) ≤ ((C₀ * r).factorial : ℝ) := by
    have h := Nat.factorial_mul_factorial_dvd_factorial_add (C₁ * r) (C₃ * r)
    have h' : (C₁ * r).factorial * (C₃ * r).factorial ≤ (C₀ * r).factorial := by
      refine (Nat.le_of_dvd (Nat.factorial_pos _) h).trans (Nat.factorial_le ?_)
      rw [← add_mul]; exact Nat.mul_le_mul_right _ hC₀b
    exact_mod_cast h'
  have hfact2 : ((C₁ * R).factorial : ℝ) * ((12 : ℝ) ^ 18) ^ R ≤ ((C₀ * R).factorial : ℝ) := by
    have h := WaveTurbulence.ClassCount.fact_mul_pow_le C₁ R 65 (by omega) hR
    have h' : (C₁ * R).factorial * (12 ^ 18) ^ R ≤ (C₀ * R).factorial := by
      refine le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h12 R)) ?_
      exact h.trans (Nat.factorial_le (Nat.mul_le_mul_right _ hC₀a))
    exact_mod_cast h'
  have hC0N : (C₀ : ℝ) ^ N = (C₁ : ℝ) ^ N * ((12 : ℝ) ^ 18) ^ N * (C₃ : ℝ) ^ N := by
    rw [hC₀]; push_cast; rw [mul_pow, mul_pow]; norm_num
  calc (A.card : ℝ) ≤ (T.card : ℝ) * ((C₃ : ℝ) ^ N * (((C₃ * r).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r)) := hAcard
    _ ≤ ((C₁ : ℝ) ^ N * (((C₁ * r).factorial : ℕ) : ℝ) * (((C₁ * R).factorial : ℕ) : ℝ)) *
          (((12 : ℝ) ^ 18) ^ (N + R)) * ((C₃ : ℝ) ^ N * (((C₃ * r).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r)) :=
        mul_le_mul_of_nonneg_right hTcard (by positivity)
    _ = ((C₁ : ℝ) ^ N * ((12 : ℝ) ^ 18) ^ N * (C₃ : ℝ) ^ N) *
          (((C₁ * r).factorial : ℝ) * ((C₃ * r).factorial : ℝ)) *
          (((C₁ * R).factorial : ℝ) * ((12 : ℝ) ^ 18) ^ R) * P.C₂ ^ (g + r) := by
        rw [pow_add]; ring
    _ ≤ (C₀ : ℝ) ^ N * ((C₀ * r).factorial : ℝ) * ((C₀ * R).factorial : ℝ) * P.C₂ ^ (g + r) := by
        rw [hC0N]
        gcongr

open Classical in
/-- B1b-2: `pieceCount_of_rep` for Stage 1′ pieces at admissible marked sets (`ClassCountStmtMkLow Adm`), over
`𝒱_γ` (main `pieceCount_of_repMk`). -/
theorem pieceCount_of_repMkLow (Adm : MarkAdmLow (γF := γF)) (hcc : ClassCountStmtMkLow (γF := γF) Adm) :
    ∃ C₀ K : ℕ, 2 ≤ C₀ ∧ ∀ (P : WTParams), K ^ (P.D + 1) ≤ P.C₂ → ∀ p, p < P.D → ∀ R, 1 ≤ R → ∀ N, 1 ≤ N →
      ∀ (S : Fama.Stage1DataG P R) (rep : S.Pc → LayeredGarden (2 * R)) (M : ℕ),
        (∀ π, Stage1Mk.Stage1CarriesW P p N (rep π) ∧
          HasPieceDataMkLow (γF := γF) Adm P.d (rep π) (S.piece π).gbar (S.piece π).rbar) →
        (∀ LG, ((@univ S.Pc S.fin).filter fun π => rep π = LG).card ≤ M) →
        ∀ g r : ℕ,
          ((((@univ S.Pc S.fin).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r).card : ℕ) : ℝ) ≤
            (M : ℝ) * ((C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) *
              P.C₂ ^ (g + r)) := by
  obtain ⟨C₀, K, hC₀, hmain⟩ := hcc
  refine ⟨C₀, K, hC₀, ?_⟩
  intro P hK p hp R hR N hN S rep M hrep hfib g r
  letI := S.fin
  set PS := (univ : Finset S.Pc).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r with hPS
  set A := PS.image rep with hA
  have hAc : (A.card : ℝ) ≤ (C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) *
      P.C₂ ^ (g + r) := by
    refine hmain P hK p hp R hR N hN g r A fun LG hLG => ?_
    obtain ⟨π, hπ, hLGe⟩ := Finset.mem_image.1 hLG
    have hgr := (Finset.mem_filter.1 hπ).2
    obtain ⟨h1, h2⟩ := hrep π
    rw [← hLGe]
    refine ⟨h1, ?_⟩
    rw [← hgr.1, ← hgr.2]
    exact h2
  have hcard : PS.card ≤ M * A.card := by
    have := Finset.card_le_mul_card_image PS M fun LG _ => by
      refine le_trans (Finset.card_le_card ?_) (hfib LG)
      intro π hπ
      simp only [Finset.mem_filter] at hπ ⊢
      exact ⟨Finset.mem_univ _, hπ.2⟩
    simpa [hA, mul_comm] using this
  have hcardR : (PS.card : ℝ) ≤ (M : ℝ) * (A.card : ℝ) := by exact_mod_cast hcard
  exact hcardR.trans (mul_le_mul_of_nonneg_left hAc (Nat.cast_nonneg _))

end WaveTurbulence.GammaLow.Flower
