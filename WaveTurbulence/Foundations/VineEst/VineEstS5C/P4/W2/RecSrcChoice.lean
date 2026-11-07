/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz5

/-! # P4-W2 (session 19, step 2): the remainder constants `CRq`, `CRt` of the certified source

`crqChoice`, `crtChoice`: `2 ·` the gate bound at the members of the bundle (`b ∈ bsA ∪ bsB`), `1` elsewhere, for the constant profile `fun _ => B₀`, `0 < B₀`.
They are positive and strictly above the gate bounds (`hgq`, `hgt` of `srcOf`), and have the shape needed by `sz_idx`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.LGSpine TTree WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  Set WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]

open Classical in
/-- The couple remainder constant: twice the gate bound on the bundle, `1` elsewhere. -/
noncomputable def crqChoice (P : WTParams) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (B0 : ℝ) (b : ST w ι pstar J) : ℝ :=
  if b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA then
    2 * (P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) *
      layerCost (fun _ => B0) (zpObjC b.1 pstar))
  else 1

open Classical in
/-- The tree remainder constant. -/
noncomputable def crtChoice (P : WTParams) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (B0 : ℝ) (b : ST w ι pstar J) : ℝ :=
  if b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA then
    2 * (P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) *
      layerCost (fun _ => B0) (zpObjT b.1 pstar))
  else 1

section
variable {P : WTParams} (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton) {B0 : ℝ}

theorem gate_pos_C (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 0 < P.L) (hB0 : 0 < B0) (b : ST w ι pstar J) :
    0 < P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) *
      layerCost (fun _ => B0) (zpObjC b.1 pstar) := by
  rw [layerCost_const]
  have : 0 < P.C₁ := by linarith
  positivity

theorem gate_pos_T (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 0 < P.L) (hB0 : 0 < B0) (b : ST w ι pstar J) :
    0 < P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) *
      layerCost (fun _ => B0) (zpObjT b.1 pstar) := by
  rw [layerCost_const]
  have : 0 < P.C₁ := by linarith
  positivity

theorem crqChoice_pos (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 0 < P.L) (hB0 : 0 < B0) (b : ST w ι pstar J) :
    0 < crqChoice (p := p) (kind := kind) P A sp0 hA B0 b := by
  unfold crqChoice
  split_ifs
  · have := gate_pos_C (P := P) (B0 := B0) hC1 hδ hL hB0 b; linarith
  · exact one_pos

theorem crtChoice_pos (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 0 < P.L) (hB0 : 0 < B0) (b : ST w ι pstar J) :
    0 < crtChoice (p := p) (kind := kind) P A sp0 hA B0 b := by
  unfold crtChoice
  split_ifs
  · have := gate_pos_T (P := P) (B0 := B0) hC1 hδ hL hB0 b; linarith
  · exact one_pos

theorem crqChoice_gate (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 0 < P.L) (hB0 : 0 < B0) (b : ST w ι pstar J)
    (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) :
    P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ)) *
      layerCost (fun _ => B0) (zpObjC b.1 pstar) < crqChoice (p := p) (kind := kind) P A sp0 hA B0 b := by
  unfold crqChoice
  rw [if_pos hb, Nat.cast_one, mul_one]
  have := gate_pos_C (P := P) (B0 := B0) hC1 hδ hL hB0 b; linarith

theorem crtChoice_gate (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 0 < P.L) (hB0 : 0 < B0) (b : ST w ι pstar J)
    (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) :
    P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ)) *
      layerCost (fun _ => B0) (zpObjT b.1 pstar) < crtChoice (p := p) (kind := kind) P A sp0 hA B0 b := by
  unfold crtChoice
  rw [if_pos hb, Nat.cast_one, mul_one]
  have := gate_pos_T (P := P) (B0 := B0) hC1 hδ hL hB0 b; linarith

theorem crqChoice_eq (b : ST w ι pstar J) (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) :
    crqChoice (p := p) (kind := kind) P A sp0 hA B0 b = 2 * (P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) *
      layerCost (fun _ => B0) (zpObjC b.1 pstar)) := by
  unfold crqChoice; rw [if_pos hb]

theorem crtChoice_eq (b : ST w ι pstar J) (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) :
    crtChoice (p := p) (kind := kind) P A sp0 hA B0 b = 2 * (P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) *
      layerCost (fun _ => B0) (zpObjT b.1 pstar)) := by
  unfold crtChoice; rw [if_pos hb]

end

end WaveTurbulence.VineEstS5C.P4.W2
