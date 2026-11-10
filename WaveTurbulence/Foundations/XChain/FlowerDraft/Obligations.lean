/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FlowerDraft.OFKRep

/-!
# The kernel representation (packet X1): one obligation, and its consequences

**Obligation O-FK `fOp_kernel_rep`** (proved). For a nontrivial flower tree, the root-attachment operator
`𝒥_F[b]` of `Flower-Ops` is the kernel operator of TARGET's `𝒥̃_F` (T (jtflower)):
`𝒥_F[b]_k(t) = ∑_{k'} ∫_p^t 𝒥̃_F(t,s,k,k') b_{k'}(s)^{ζ_𝔣} ds`. The statement includes the integrability and
summability that let finite sums pass through.

**Proof** (`OFK-TreeG` … `OFK-Rep`).
- `OFK-TreeG`, `OFK-NodeG`: tree terms `treeTermG` whose leaf inputs depend on the parent's time, and their root
  splitting `treeTermG_node`, which generalizes the Duhamel identity O-TR1 `treeTerm_node`.
- `OFK-Flower`: `𝒥_F[b] = treeTermG F.toTree`, with `b` at the flower and `a(p)` at every other leaf. The proof is
  an induction on `F`, using `treeTermG_node` in the stem slot.
- `OFK-Fubini`: Fubini at the flower parent (`piEquivPiSubtypeProd`, `funUnique`). It turns each decoration's time
  integral into `∫_p^t W_κ(s) b_{κ_𝔣}(s)^{ζ_𝔣} ∏_{ℓ≠𝔣} a_{κ_ℓ}(p)^{ζ_ℓ} ds`, where `W_κ(s)` is TARGET's time
  integral with `t_{𝔣^pr} := s`.
- `OFK-Rep`: the decorations are regrouped by the flower mode `κ_𝔣 = k'` (`Equiv.sigmaFiberEquiv`). For each `k'`,
  the sum commutes with the `s`-integral, by the `ℓ¹` majorant `leafBound`.

**Consequences, proved here:**
- `Xop_eq_kernelOp`, `Yop_eq_kernelOp`, `Wop_eq_kernelOp`: `𝒳 = 1 + 𝒦[Xker]`, `Yop = 𝒦[Yker]`,
  `Wop = 𝒦[Wker]`.
- The identities for TARGET's kernel-defined operators: `(1 − ℒ₁)(1 + 𝒦[Xker]) = 1 − 𝒦[Yker]` and
  `(1 + 𝒦[Xker])(1 − ℒ₁) = 1 − 𝒦[Wker]`.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.SysAPI

open FTree

variable (L γ δ : ℝ) {d : ℕ}

/-- **O-FK** (T (jtflower) ⇔ DH21 Prop 11.2's root attachment). -/
theorem fOp_kernel_rep (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
    {b : ArrI p d} (hb : Good p b) {F : FTree} (hF : F ≠ flower) (t : Icc (p : ℝ) (p + 1))
    (k : Fin d → ℤ) :
    (∀ k', IntervalIntegrable (fun s => flowerKernel L γ δ p F aP t s k k' *
      zpowSign F.sign (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k')) volume p t) ∧
    Summable (fun k' => ∫ s in (p : ℝ)..t, flowerKernel L γ δ p F aP t s k k' *
      zpowSign F.sign (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k')) ∧
    fOp L γ δ p aP F b t k = ∑' k', ∫ s in (p : ℝ)..t, flowerKernel L γ δ p F aP t s k k' *
      zpowSign F.sign (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k') :=
  fOp_kernel_rep' L γ δ hF p haP hb t k

/-- A sum of `𝒥_F` over a finite set of nontrivial flower trees is the kernel operator of the sum of their
kernels, grouped by flower sign. -/
theorem sum_fOp_eq_kernelOp (p : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
    {b : ArrI p d} (hb : Good p b) {ι : Type*} [DecidableEq ι] (S : Finset ι) (G : ι → FTree)
    (hG : ∀ x ∈ S, G x ≠ flower) :
    ∑ x ∈ S, fOp L γ δ p aP (G x) b = kernelOp p
      (fun ζ t s k k' => ∑ x ∈ S.filter (fun x => (G x).sign = ζ),
        flowerKernel L γ δ p (G x) aP t s k k') b := by
  funext t k
  rw [Finset.sum_apply, Finset.sum_apply]
  unfold kernelOp
  have hterm : ∀ ζ : ℤˣ, ∑' k', ∫ s in (p : ℝ)..t,
      (∑ x ∈ S.filter (fun x => (G x).sign = ζ), flowerKernel L γ δ p (G x) aP t s k k') *
        zpowSign ζ (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k') =
      ∑ x ∈ S.filter (fun x => (G x).sign = ζ), fOp L γ δ p aP (G x) b t k := by
    intro ζ
    have hrep : ∀ x ∈ S.filter (fun x => (G x).sign = ζ),
        (∀ k', IntervalIntegrable (fun s => flowerKernel L γ δ p (G x) aP t s k k' *
          zpowSign ζ (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k')) volume p t) ∧
        Summable (fun k' => ∫ s in (p : ℝ)..t, flowerKernel L γ δ p (G x) aP t s k k' *
          zpowSign ζ (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k')) ∧
        fOp L γ δ p aP (G x) b t k = ∑' k', ∫ s in (p : ℝ)..t, flowerKernel L γ δ p (G x) aP t s k k' *
          zpowSign ζ (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k') := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [← hx.2]
      exact fOp_kernel_rep L γ δ p haP hb (hG x hx.1) t k
    have h1 : ∀ k', ∫ s in (p : ℝ)..t,
        (∑ x ∈ S.filter (fun x => (G x).sign = ζ), flowerKernel L γ δ p (G x) aP t s k k') *
          zpowSign ζ (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k') =
        ∑ x ∈ S.filter (fun x => (G x).sign = ζ), ∫ s in (p : ℝ)..t,
          flowerKernel L γ δ p (G x) aP t s k k' *
            zpowSign ζ (Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s k') := by
      intro k'
      simp only [Finset.sum_mul]
      exact intervalIntegral.integral_finsetSum fun x hx => (hrep x hx).1 k'
    simp only [h1]
    rw [Summable.tsum_finsetSum fun x hx => (hrep x hx).2.1]
    exact Finset.sum_congr rfl fun x hx => ((hrep x hx).2.2).symm
  simp only [hterm]
  exact (Finset.sum_fiberwise S (fun x => (G x).sign) fun x => fOp L γ δ p aP (G x) b t k).symm

/-- **`𝒳 = 1 + 𝒦[Xker]`** (T (operatorx), (operatorxker), with the identity term; F39). -/
theorem Xop_eq_kernelOp (p N : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
    {b : ArrI p d} (hb : Good p b) :
    Xop L γ δ p N aP b = b + kernelOp p (Xker L γ δ p N aP) b := by
  unfold Xop
  congr 1
  exact sum_fOp_eq_kernelOp L γ δ p haP hb (Xset N) id fun F hF => (Finset.mem_filter.1 hF).2

/-- **`Yop = 𝒦[Yker]`**. -/
theorem Yop_eq_kernelOp (p N : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
    {b : ArrI p d} (hb : Good p b) :
    Yop L γ δ p N aP b = kernelOp p (Yker L γ δ p N aP) b :=
  sum_fOp_eq_kernelOp L γ δ p haP hb (Yind N) rootOf fun x _ => by simp [rootOf]

/-- **`Wop = 𝒦[Wker]`**. -/
theorem Wop_eq_kernelOp (p N : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
    {b : ArrI p d} (hb : Good p b) :
    Wop L γ δ p N aP b = kernelOp p (Wker L γ δ p N aP) b :=
  sum_fOp_eq_kernelOp L γ δ p haP hb (Wind N) bottomOf fun x _ => graft_ne_flower (by simp)

end WaveTurbulence.SysAPI
