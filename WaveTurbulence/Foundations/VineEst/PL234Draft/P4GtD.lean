/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4GtC

/-!
# Prop 6.3, realness of the paired sum for `q > q'`

After the decompositions, a carrier term is `[BM b (κU x + κU y)] · Φ(x) conj Φ(y) · ψ(B) conj χ(Z)`.
Here `x`, `y` are upper labelled chains (of the couple and of the tree), `B` is the bottom couple and `Z` the bottom
chain. So

`∑ = ∑_{M + N₀ = n} (∑_{i + j = M} A i j) · (∑_{a₀ + b₀ = N₀} R a₀ b₀)`.

* `∑_{i+j=M} A i j` is real: conjugation exchanges `x` and `y` (`star_A`), and the antidiagonal is symmetric;
* `∑_{a₀+b₀=N₀} R a₀ b₀` is J7's `regcancel` sum at layer `q'`, times `(q'+1, s)`, hence real.

**`reality_gt`**: `(∑ᶠ … CoherentPairCarrier p q q' n b …).im = 0` on `timeBoxGt q q'` for `q' < q`, for every real
input family.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset ComplexConjugate
open scoped Classical

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-! ### Two algebraic lemmas -/

theorem four_sum {α β γ ε : Type*} (s₁ : Finset α) (s₂ : Finset β) (s₃ : Finset γ) (s₄ : Finset ε)
    (G : α → γ → ℂ) (H : β → ε → ℂ) :
    ∑ x ∈ s₁, ∑ B ∈ s₂, ∑ y ∈ s₃, ∑ Z ∈ s₄, G x y * H B Z =
      (∑ x ∈ s₁, ∑ y ∈ s₃, G x y) * (∑ B ∈ s₂, ∑ Z ∈ s₄, H B Z) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [Finset.mul_sum]

theorem antidiag_rearrange (A R : ℕ → ℕ → ℂ) (n : ℕ) :
    ∑ ab ∈ antidiagonal n, ∑ ia ∈ antidiagonal ab.1, ∑ jb ∈ antidiagonal ab.2, A ia.1 jb.1 * R ia.2 jb.2 =
      ∑ MN ∈ antidiagonal n, (∑ ij ∈ antidiagonal MN.1, A ij.1 ij.2) * (∑ cd ∈ antidiagonal MN.2, R cd.1 cd.2) := by
  have hL : ∑ ab ∈ antidiagonal n, ∑ ia ∈ antidiagonal ab.1, ∑ jb ∈ antidiagonal ab.2, A ia.1 jb.1 * R ia.2 jb.2 =
      ∑ e ∈ (antidiagonal n).sigma (fun ab => antidiagonal ab.1 ×ˢ antidiagonal ab.2),
        A e.2.1.1 e.2.2.1 * R e.2.1.2 e.2.2.2 := by
    rw [Finset.sum_sigma]
    exact Finset.sum_congr rfl fun ab _ => (Finset.sum_product (antidiagonal ab.1) (antidiagonal ab.2)
      (fun w => A w.1.1 w.2.1 * R w.1.2 w.2.2)).symm
  have hR : ∑ MN ∈ antidiagonal n, (∑ ij ∈ antidiagonal MN.1, A ij.1 ij.2) * (∑ cd ∈ antidiagonal MN.2, R cd.1 cd.2) =
      ∑ e ∈ (antidiagonal n).sigma (fun MN => antidiagonal MN.1 ×ˢ antidiagonal MN.2),
        A e.2.1.1 e.2.1.2 * R e.2.2.1 e.2.2.2 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun MN _ => ?_
    rw [Finset.sum_mul_sum]
    exact (Finset.sum_product (antidiagonal MN.1) (antidiagonal MN.2)
      (fun w => A w.1.1 w.1.2 * R w.2.1 w.2.2)).symm
  rw [hL, hR]
  let τ : (Σ _ : ℕ × ℕ, (ℕ × ℕ) × (ℕ × ℕ)) → Σ _ : ℕ × ℕ, (ℕ × ℕ) × (ℕ × ℕ) :=
    fun e => ⟨(e.2.1.1 + e.2.2.1, e.2.1.2 + e.2.2.2), ((e.2.1.1, e.2.2.1), (e.2.1.2, e.2.2.2))⟩
  have hmem : ∀ e ∈ (antidiagonal n).sigma (fun ab => antidiagonal ab.1 ×ˢ antidiagonal ab.2),
      τ e ∈ (antidiagonal n).sigma (fun ab => antidiagonal ab.1 ×ˢ antidiagonal ab.2) := by
    rintro ⟨⟨a, b⟩, ⟨i₁, i₂⟩, ⟨j₁, j₂⟩⟩ he
    simp only [τ, Finset.mem_sigma, Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal] at he ⊢
    exact ⟨by omega, trivial, trivial⟩
  have hinv : ∀ e ∈ (antidiagonal n).sigma (fun ab => antidiagonal ab.1 ×ˢ antidiagonal ab.2), τ (τ e) = e := by
    rintro ⟨⟨a, b⟩, ⟨i₁, i₂⟩, ⟨j₁, j₂⟩⟩ he
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal] at he
    obtain ⟨-, h1, h2⟩ := he
    simp only [τ, h1, h2]
  exact Finset.sum_nbij' τ τ hmem hmem hinv hinv fun e _ => rfl

section Real

variable {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ) (p q q' : ℕ) (t s : ℝ) (k : Mom d) (b : Option ℕ)

/-- The top-layer count of an upper labelled chain. -/
def κU (x : Σ _ : RegChain, List ℕ) : ℕ := if q = p then (sliceL x.1 x.2 q).size else 0

/-- The upper factor sum. -/
noncomputable def Aup (i j : ℕ) : ℂ :=
  ∑ x ∈ UP q q' i, ∑ y ∈ UP q q' j,
    if BM b (κU p q x + κU p q y) then upF δ F q q' t k x.1 x.2 * star (upF δ F q q' t k y.1 y.2) else 0

/-- The bottom factor sum. -/
noncomputable def Rlow (a₀ b₀ : ℕ) : ℂ :=
  ∑ B ∈ Mexp.domCodes a₀, ∑ Z ∈ Mexp.domTrees b₀,
    B.app δ q' (F q') (q' + 1) s k * star (Z.app δ q' (F q') 1 (q' + 1) s k)

theorem star_Aup (i j : ℕ) : star (Aup δ F p q q' t k b i j) = Aup δ F p q q' t k b j i := by
  unfold Aup
  rw [star_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [apply_ite star, star_zero, star_mul', star_star, add_comm]
  exact if_congr Iff.rfl (mul_comm _ _) rfl

theorem sum_Aup_real (M : ℕ) : (∑ ij ∈ antidiagonal M, Aup δ F p q q' t k b ij.1 ij.2).im = 0 := by
  have h : star (∑ ij ∈ antidiagonal M, Aup δ F p q q' t k b ij.1 ij.2) =
      ∑ ij ∈ antidiagonal M, Aup δ F p q q' t k b ij.1 ij.2 := by
    rw [star_sum]
    simp only [star_Aup]
    exact Finset.Nat.sum_antidiagonal_swap (f := fun ij => Aup δ F p q q' t k b ij.1 ij.2)
  exact Complex.conj_eq_iff_im.1 h

variable {p q q'}

theorem κC_compose (hlt : q' < q) {x : Σ _ : RegChain, List ℕ} (hx : LabOK (q' + 1) x.1 x.2 q) (B : RegCpl) :
    κC p q (composeC q' x.1 x.2 B).1 (composeC q' x.1 x.2 B).2 = κU p q x := by
  obtain ⟨U, lsU⟩ := x
  cases B with
  | type2 Xr Xm Qlp =>
    show (if q = p then (sliceL (appendChain U Xr) (lsU ++ List.replicate (topCount Xr) q') q).size else 0) = _
    rw [sliceL_join q U lsU q Xr hx, ite_eq_right (Nat.ne_of_gt hlt)]
    rfl
  | triv =>
    by_cases hn : U.isNil = true
    · have hU' := isNil_iff.1 hn
      subst hU'
      have : lsU = [] := hx
      subst this
      show 0 = if q = p then (RegChain.nil).size else 0
      split_ifs <;> rfl
    · have hc : composeC q' U lsU .triv = (.type2 U .nil .triv, lsU) := by simp [composeC, hn]
      rw [hc]
      rfl
  | type1 c Q₁ Q₂ Q₃ =>
    by_cases hn : U.isNil = true
    · have hU' := isNil_iff.1 hn
      subst hU'
      have : lsU = [] := hx
      subst this
      show 0 = if q = p then (RegChain.nil).size else 0
      split_ifs <;> rfl
    · have hc : composeC q' U lsU (.type1 c Q₁ Q₂ Q₃) = (.type2 U .nil (.type1 c Q₁ Q₂ Q₃), lsU) := by
        simp [composeC, hn]
      rw [hc]
      rfl

theorem κT_join (hlt : q' < q) {y : Σ _ : RegChain, List ℕ} (hy : LabOK (q' + 1) y.1 y.2 q) (Z : RegChain) :
    κT p q (appendChain y.1 Z) (y.2 ++ List.replicate (topCount Z) q') = κU p q y := by
  unfold κT κU
  rw [sliceL_join q y.1 y.2 q Z hy, ite_eq_right (Nat.ne_of_gt hlt)]

theorem term_eq (hlt : q' < q) {x y : Σ _ : RegChain, List ℕ} (hx : LabOK (q' + 1) x.1 x.2 q)
    (hy : LabOK (q' + 1) y.1 y.2 q) {B : RegCpl} (hB : B.wf = true) (Z : RegChain) :
    (if BM b (κC p q (composeC q' x.1 x.2 B).1 (composeC q' x.1 x.2 B).2 +
        κT p q (appendChain y.1 Z) (y.2 ++ List.replicate (topCount Z) q')) then
      appC δ F q q' t s k (composeC q' x.1 x.2 B).1 (composeC q' x.1 x.2 B).2 *
        star (appT δ F q q' t s k (appendChain y.1 Z) (y.2 ++ List.replicate (topCount Z) q')) else 0) =
    (if BM b (κU p q x + κU p q y) then upF δ F q q' t k x.1 x.2 * star (upF δ F q q' t k y.1 y.2) else 0) *
      (B.app δ q' (F q') (q' + 1) s k * star (Z.app δ q' (F q') 1 (q' + 1) s k)) := by
  rw [κC_compose hlt hx, κT_join hlt hy, appC_compose δ F t s k hlt hx hB, appT_join δ F t s k hlt hy]
  split_ifs
  · rw [star_mul']
    ring
  · rw [zero_mul]

end Real

end WaveTurbulence.PL234
