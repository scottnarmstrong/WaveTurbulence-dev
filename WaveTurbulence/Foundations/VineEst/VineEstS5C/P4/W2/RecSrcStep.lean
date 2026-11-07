/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSrcChoice
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecCoh
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecKind
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.XSrcOfX

/-! # P4-W2 (session 19, step 2): the certified source of a step level with the chosen constants, and its `Src.sz` bound

`srcOfC`: `srcOf` with `CRq = crqChoice`, `CRt = crtChoice`.  `srcOfC_idx`: the four size products of a good member against `K Z N`.
`srcOfC_sz_le`: `Src.sz c' ≤ KZ · N · (Lw if recKind c' = 3)`.  `hg_of_op`: the incoherency indices of the operative row vanish.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.LGSpine TTree WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  Set WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng


variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]
variable {P : WTParams} {κ : KPar P.d} {B0 : ℝ}

variable (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
    (A.family.atoms pstar) (A.family.upper pstar))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))
  (R : RemEnv P κ) (E : GateEnv P κ p (fun _ => B0)) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)
  (hC1 : 1 ≤ P.C₁) (hB0 : 0 < B0)

include hcan hel htc hcc R E hN hC1 hB0 in
/-- **The certified source of a level with the chosen remainder constants.** -/
noncomputable def srcOfC : Src P (sepFamOf (κ := κ) A sp0 hA hcan hel htc hcc E hN).S (remQ κ (zpQfam κ A)) (remT κ (zpTfam κ A))
    (zpQ2 A pstar : ℝ) (zpQ4 A pstar : ℝ) (zpQh A pstar : ℝ) :=
  srcOf (κ := κ) A sp0 hA hcan hel htc hcc R (crqChoice (p := p) (kind := kind) P A sp0 hA B0) (crtChoice (p := p) (kind := kind) P A sp0 hA B0)
    (crqChoice_pos A sp0 hA hC1 R.hδ0 (by linarith [R.hL1]) hB0) (crtChoice_pos A sp0 hA hC1 R.hδ0 (by linarith [R.hL1]) hB0)
    (fun b hb => crqChoice_gate A sp0 hA hC1 R.hδ0 (by linarith [R.hL1]) hB0 b hb)
    (fun b hb => crtChoice_gate A sp0 hA hC1 R.hδ0 (by linarith [R.hL1]) hB0 b hb) E hN

include hcan hel htc hcc R E hN hC1 hB0 in
/-- **The cross fields of `srcOfC`.** -/
noncomputable def srcOfCX (hη0 : 0 < P.η) (hη4 : P.η < 1 / 4) (hgap : zpQ4 A pstar + 1 ≤ zpQh A pstar) :
    K2.XCross P (srcOfC (κ := κ) A sp0 hA hcan hel htc hcc R E hN hC1 hB0) :=
  srcOfX (κ := κ) A sp0 hA hcan hel htc hcc E hN R (crqChoice (p := p) (kind := kind) P A sp0 hA B0) (crtChoice (p := p) (kind := kind) P A sp0 hA B0)
    (crqChoice_pos A sp0 hA hC1 R.hδ0 (by linarith [R.hL1]) hB0) (crtChoice_pos A sp0 hA hC1 R.hδ0 (by linarith [R.hL1]) hB0)
    (fun b hb => crqChoice_gate A sp0 hA hC1 R.hδ0 (by linarith [R.hL1]) hB0 b hb)
    (fun b hb => crtChoice_gate A sp0 hA hC1 R.hδ0 (by linarith [R.hL1]) hB0 b hb) hη0 hη4 hgap

include hcan hel htc hcc R E hN hC1 hB0 in
open Classical in
/-- **The four size products of a good member of `srcOfC`** against `KZ · Nn` (`Nn` the common value of the native row-bound product). -/
theorem srcOfC_idx (hη0 : 0 < P.η) (hη : P.η ≤ 1) (hcb : 0 < rowCb P) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) (Nn : ℝ)
    (hNn : ∀ b : ST w ι pstar J, (b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) →
      rowCb P ^ 2 * P.C₁ ^ 4 * (2 * (P.C₁ ^ 2 * P.δ)) ^ zpN A pstar *
        (layerCost (fun _ => B0) (zpObjC b.1 pstar) * layerCost (fun _ => B0) (zpObjT b.1 pstar)) = Nn) :
    ∀ b, (srcOfC (κ := κ) A sp0 hA hcan hel htc hcc R E hN hC1 hB0).good b →
      (srcOfC (κ := κ) A sp0 hA hcan hel htc hcc R E hN hC1 hB0).szQ b * (srcOfC (κ := κ) A sp0 hA hcan hel htc hcc R E hN hC1 hB0).szT b ≤
          (4 * TR P.η ^ 2 * trC (6 * P.η ^ 6) ^ 2 / rowCb P ^ 2) * Nn ∧
        (srcOfC (κ := κ) A sp0 hA hcan hel htc hcc R E hN hC1 hB0).szQ b * (srcOfC (κ := κ) A sp0 hA hcan hel htc hcc R E hN hC1 hB0).CRt b ≤
          (4 * TR P.η ^ 2 * trC (6 * P.η ^ 6) ^ 2 / rowCb P ^ 2) * (P.L ^ (-(P.gamma1 - Real.sqrt P.η)) * Nn) ∧
        (srcOfC (κ := κ) A sp0 hA hcan hel htc hcc R E hN hC1 hB0).CRq b * (srcOfC (κ := κ) A sp0 hA hcan hel htc hcc R E hN hC1 hB0).szT b ≤
          (4 * TR P.η ^ 2 * trC (6 * P.η ^ 6) ^ 2 / rowCb P ^ 2) * (P.L ^ (-(P.gamma1 - Real.sqrt P.η)) * Nn) ∧
        (srcOfC (κ := κ) A sp0 hA hcan hel htc hcc R E hN hC1 hB0).CRq b * (srcOfC (κ := κ) A sp0 hA hcan hel htc hcc R E hN hC1 hB0).CRt b ≤
          (4 * TR P.η ^ 2 * trC (6 * P.η ^ 6) ^ 2 / rowCb P ^ 2) * (P.L ^ (-(P.gamma1 - Real.sqrt P.η)) * Nn) := by
  intro b hb
  have hb' : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA := hb
  have hL0 : 0 < P.L := by linarith [R.hL1]
  have hLw0 : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η)) := Real.rpow_nonneg hL0.le _
  have hLw1 : P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos R.hL1 (by linarith)
  have hcC : 0 ≤ layerCost (fun _ => B0) (zpObjC b.1 pstar) := by rw [layerCost_const]; exact pow_nonneg hB0.le _
  have hcT : 0 ≤ layerCost (fun _ => B0) (zpObjT b.1 pstar) := by rw [layerCost_const]; exact pow_nonneg hB0.le _
  have htrc : 1 ≤ trC (6 * P.η ^ 6) := one_le_trC (by positivity)
  have key := sz_idx (κ := κ) A sp0 hA hcan hel htc hcc E hN R.hδ0 hC1 hη hcb hb' (P.L ^ (-(P.gamma1 - Real.sqrt P.η))) (trC (6 * P.η ^ 6))
    ((srcOfC (κ := κ) A sp0 hA hcan hel htc hcc R E hN hC1 hB0).CRq b) ((srcOfC (κ := κ) A sp0 hA hcan hel htc hcc R E hN hC1 hB0).CRt b)
    htrc hLw0 hLw1 hcC hcT
    (by show trC (6 * P.η ^ 6) * crqChoice (p := p) (kind := kind) P A sp0 hA B0 b = _
        rw [crqChoice_eq A sp0 hA b hb'])
    (by show trC (6 * P.η ^ 6) * crtChoice (p := p) (kind := kind) P A sp0 hA B0 b = _
        rw [crtChoice_eq A sp0 hA b hb'])
  have hN' := hNn b hb'
  simp only at key
  rw [hN'] at key
  exact key

section SzKind
variable {β : Type*} [DecidableEq β] {S : SepTerms β P.d} {RQ RT : β → ℝ → ℝ → Mom P.d → ℂ} {q2 q4 qh : ℝ}

theorem recKind_inl_ne_three {bs₁ bs₂ rA rB : Finset β} (pc : PCh S bs₁ bs₂) :
    recKind (Sum.inl pc : Ch S bs₁ bs₂ rA rB) ≠ 3 := by
  rcases pc with _ | _ | _ | _ | _ | _ <;> simp [recKind, kindOf]

/-- **`Src.sz` of a summand against `K · N · Lw^{[kind 3]}`**, from the four size products of the good indices. -/
theorem sz_le_kind {bs₁ bs₂ rA rB : Finset β} (src : Src P S RQ RT q2 q4 qh) (K Lw N : ℝ)
    (hgood : ∀ b, (b ∈ bs₁ ∨ b ∈ bs₂ ∨ b ∈ rA ∨ b ∈ rB) → src.good b)
    (hidx : ∀ b, src.good b → src.szQ b * src.szT b ≤ K * N ∧ src.szQ b * src.CRt b ≤ K * (Lw * N) ∧
      src.CRq b * src.szT b ≤ K * (Lw * N) ∧ src.CRq b * src.CRt b ≤ K * (Lw * N))
    (c : Ch S bs₁ bs₂ rA rB) : src.sz c ≤ K * N * (if recKind c = 3 then Lw else 1) := by
  rcases c with pc | rc
  · rw [if_neg (recKind_inl_ne_three pc), mul_one]
    exact sz_inl_le src K Lw N hgood hidx pc
  · rw [if_pos (by simp [recKind])]
    have := sz_inr_le src K Lw N hgood hidx rc
    linarith

end SzKind

end WaveTurbulence.VineEstS5C.P4.W2
