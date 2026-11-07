/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4GtD

/-!
# Prop 6.3 (iii): the paired sum is real

* `block_eq`: for fixed sizes, the code sum of label sums is `∑_{i + a₀ = a} ∑_{j + b₀ = b} A i j · R a₀ b₀`;
* **`reality_gt`** (`q' < q`) and, with `P4Equal.reality_same`, **`reality_all`** (`q' ≤ q`): for every real input
  family `F`, every `b`, and `ts ∈ timeBoxGt q q'`,
  `(∑ᶠ … CoherentPairCarrier p q q' n b …, SourceApp.couple · conj SourceApp.tree).im = 0`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset ComplexConjugate
open scoped Classical

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

section Gt

variable {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ) {p q q' : ℕ} (t s : ℝ) (k : Mom d) (b : Option ℕ)
  (hlt : q' < q)
include hlt

theorem block_eq (a c : ℕ) :
    ∑ Q ∈ Mexp.domCodes a, ∑ X ∈ Mexp.domTrees c, labSum δ F p q q' t s k b Q X =
      ∑ ia ∈ antidiagonal a, ∑ jb ∈ antidiagonal c,
        Aup δ F p q q' t k b ia.1 jb.1 * Rlow δ F q' s k ia.2 jb.2 := by
  unfold labSum
  rw [Finset.sum_congr rfl fun Q _ => Finset.sum_comm]
  rw [sum_couple_decomp hlt.le a]
  refine Finset.sum_congr rfl fun ia _ => ?_
  have hin : ∀ x ∈ UP q q' ia.1, ∀ B ∈ Mexp.domCodes ia.2,
      (∑ X ∈ Mexp.domTrees c, ∑ μ ∈ labsF q' X q,
        if BM b (κC p q (composeC q' x.1 x.2 B).1 (composeC q' x.1 x.2 B).2 + κT p q X μ) then
          appC δ F q q' t s k (composeC q' x.1 x.2 B).1 (composeC q' x.1 x.2 B).2 *
            star (appT δ F q q' t s k X μ) else 0) =
      ∑ jb ∈ antidiagonal c, ∑ y ∈ UP q q' jb.1, ∑ Z ∈ Mexp.domTrees jb.2,
        (if BM b (κU p q x + κU p q y) then upF δ F q q' t k x.1 x.2 * star (upF δ F q q' t k y.1 y.2) else 0) *
          (B.app δ q' (F q') (q' + 1) s k * star (Z.app δ q' (F q') 1 (q' + 1) s k)) := by
    intro x hx B hB
    have hxL := (mem_labsF x.1 q x.2).1 (Finset.mem_sigma.1 hx).2
    have hBw := (Mexp.mem_domCodes.1 hB).1
    rw [sum_tree_decomp hlt.le c]
    refine Finset.sum_congr rfl fun jb _ => Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun Z _ => ?_
    exact term_eq δ F t s k b hlt hxL ((mem_labsF y.1 q y.2).1 (Finset.mem_sigma.1 hy).2) hBw Z
  rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun B hB => hin x hx B hB]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun jb _ => ?_
  exact four_sum _ _ _ _ _ _

theorem labSum_nondom (Q : RegCpl) (X : RegChain) (h : Q.dominant = false ∨ X.dominant = false) :
    labSum δ F p q q' t s k b Q X = 0 := by
  unfold labSum
  refine Finset.sum_eq_zero fun ls hls => Finset.sum_eq_zero fun μ hμ => ?_
  split_ifs
  · rcases h with h | h
    · rw [appC_nondom δ F t s k hlt h hls, zero_mul]
    · rw [appT_nondom δ F t s k hlt h hμ, star_zero, mul_zero]
  · rfl

/-- **Prop 6.3 (iii), `q > q'`.** -/
theorem reality_gt (hqp : q ≤ p) (n : ℕ) (ts : Fin 2 → ℝ) (hts : ts ∈ timeBoxGt q q') :
    (∑ᶠ (Q : RegCpl) (X : RegChain) (LQ : LayeredGarden 2) (LX : LayeredGarden 1)
      (_ : CoherentPairCarrier p q q' n b Q X LQ LX),
      SourceApp.couple δ F LQ Q q q' (ts 0) (ts 1) k *
        star (SourceApp.tree δ F LX X q q' (ts 0) (ts 1) k)).im = 0 := by
  rw [finsum_congr fun Q => finsum_congr fun X => carrier_QX δ F (ts 0) (ts 1) k n b hlt hqp Q X]
  have hc := finsum_codes_eq n (labSum δ F p q q' (ts 0) (ts 1) k b)
    (fun Q X h => labSum_nondom δ F (ts 0) (ts 1) k b hlt Q X h)
  unfold codeTerm at hc
  rw [hc, Finset.sum_congr rfl fun ab _ => block_eq δ F (ts 0) (ts 1) k b hlt ab.1 ab.2, antidiag_rearrange,
    Complex.im_sum]
  refine Finset.sum_eq_zero fun MN _ => ?_
  have hR : (∑ cd ∈ antidiagonal MN.2, Rlow δ F q' (ts 1) k cd.1 cd.2).im = 0 :=
    Mexp.regcancel δ q' (F q') MN.2 hts.1.2.1 hts.1.2.2 k
  rw [Complex.mul_im, sum_Aup_real, hR, mul_zero, zero_mul, add_zero]

end Gt

/-- **Prop 6.3 (iii)**: the paired sum is real, for `q' ≤ q ≤ p` and every real input family. -/
theorem reality_all {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ) {p q q' : ℕ} (hqq : q' ≤ q) (hqp : q ≤ p) (n : ℕ)
    (b : Option ℕ) (ts : Fin 2 → ℝ) (hts : ts ∈ timeBoxGt q q') (k : Mom d) :
    (∑ᶠ (Q : RegCpl) (X : RegChain) (LQ : LayeredGarden 2) (LX : LayeredGarden 1)
      (_ : CoherentPairCarrier p q q' n b Q X LQ LX),
      SourceApp.couple δ F LQ Q q q' (ts 0) (ts 1) k *
        star (SourceApp.tree δ F LX X q q' (ts 0) (ts 1) k)).im = 0 := by
  rcases hqq.lt_or_eq with hlt | heq
  · exact reality_gt δ F k b hlt hqp n ts hts
  · subst heq
    exact reality_same δ F hqp n b ts hts k

end WaveTurbulence.PL234
