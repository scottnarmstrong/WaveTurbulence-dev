/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P1.Ext
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.BundleState
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.CarrierSum

/-! # P1: the mixed approximant families `Qf := mixFam`, `hsub`, `hQ0`, `hT0`, `hreal`

`Qf = mixFam tq Ex Lq Q₀` with `Lq b = cplRootLayer (zpObjC b)`, `Q₀ b` the root-layer instance of `SourceApp.couple` at the
second parent layer `L₂ = zpQ2` (so that `Qf` is the constant extension of the root-layer instance, TARGET L1893-L1925),
`tq b` = "the carrier-side couple is trivial" (R35: `Ex = F · 1_{t > Lq}`), and likewise for trees.

* `zp_hsub`: `b ∈ bsA ∪ bsB` with both roots `≤ L₄` lies in `bsA ∩ bsB`;
* `zp_hQ0`, `zp_hT0`: the endpoint vanishing for roots `> L₄` (needs `ZpLayers`);
* `zp_hreal`: the realness of the mixed leading sum, from `RealityAll` (PL234 `reality_all`) via `carrier_sum_eq`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P1
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.ConjCoh TTree
  WaveTurbulence.VineEstS4c

/-- **PL234 `reality_all`** (Prop 6.3 (iii), `PL234Draft/P4Gt.lean`), as a `Prop` (R46: a named input of exactly this type,
owner PL234, proved there). -/
def RealityAll : Prop :=
  ∀ {d : ℕ} (δ : ℝ) (F : ℕ → Mom d → ℝ) {p q q' : ℕ}, q' ≤ q → q ≤ p → ∀ (n : ℕ) (b : Option ℕ) (ts : Fin 2 → ℝ),
    ts ∈ timeBoxGt (q : ℝ) (q' : ℝ) → ∀ k : Mom d,
      (∑ᶠ (Q : RegCpl) (X : RegChain) (LQ : LayeredGarden 2) (LX : LayeredGarden 1)
        (_ : CoherentPairCarrier p q q' n b Q X LQ LX),
        SourceApp.couple δ F LQ Q q q' (ts 0) (ts 1) k * star (SourceApp.tree δ F LX X q q' (ts 0) (ts 1) k)).im = 0

section
variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} {d : ℕ} [Fintype ι] [DecidableEq ι]

/-- The root layer of the carrier-side couple of the index `b`. -/
noncomputable def zpLq (b : ST w ι pstar J) : ℕ := cplRootLayer (zpObjC b.1 pstar)

/-- The root layer of the carrier-side tree of the index `b`. -/
noncomputable def zpLt (b : ST w ι pstar J) : ℕ := treeRootLayer (zpObjT b.1 pstar)

/-- The carrier-side couple of `b` is the trivial couple. -/
def zpTrQ (b : ST w ι pstar J) : Prop := zpCodeC b.1 pstar = RegCpl.triv

/-- The carrier-side tree of `b` is the trivial tree. -/
def zpTrT (b : ST w ι pstar J) : Prop := zpCodeT b.1 pstar = RegChain.nil

/-- The root-layer instance of the couple approximant (TARGET L1893-L1925): `SourceApp.couple` at `(Lr, L₂)`. -/
noncomputable def zpQ0 (κ : KPar d) (A : FamilyReconstruction w ι) (b : ST w ι pstar J) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => LGSpine.SourceApp.couple κ.δ κ.F (zpObjC b.1 pstar) (zpCodeC b.1 pstar) (zpLq b) (zpQ2 A pstar) t s k

/-- The root-layer instance of the tree approximant: `SourceApp.tree` at `(Lr, L₂)`. -/
noncomputable def zpT0 (κ : KPar d) (A : FamilyReconstruction w ι) (b : ST w ι pstar J) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => LGSpine.SourceApp.tree κ.δ κ.F (zpObjT b.1 pstar) (zpCodeT b.1 pstar) (zpLt b) (zpQ2 A pstar) t s k

open Classical in
/-- R35: the exact kernel of a trivial couple, `F · 1_{t > Lq}` (the constant extension, cut off below the root layer). -/
noncomputable def zpEx (κ : KPar d) (A : FamilyReconstruction w ι) (b : ST w ι pstar J) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => if (zpLq b : ℝ) < t then extFam zpLq (zpQ0 κ A) b t s k else 0

open Classical in
/-- R35 for trees. -/
noncomputable def zpEt (κ : KPar d) (A : FamilyReconstruction w ι) (b : ST w ι pstar J) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => if (zpLt b : ℝ) < t then extFam zpLt (zpT0 κ A) b t s k else 0

/-- **`Qf`**: the approximant family of the couples (`mixFam`). -/
noncomputable def zpQfam (κ : KPar d) (A : FamilyReconstruction w ι) : ST w ι pstar J → ℝ → ℝ → Mom d → ℂ :=
  mixFam zpTrQ (zpEx κ A) zpLq (zpQ0 κ A)

/-- **`Tf`**: the approximant family of the trees (`mixFam`). -/
noncomputable def zpTfam (κ : KPar d) (A : FamilyReconstruction w ι) : ST w ι pstar J → ℝ → ℝ → Mom d → ℂ :=
  mixFam zpTrT (zpEt κ A) zpLt (zpT0 κ A)

variable (p kind J)
variable (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)

/-- **Layer numerals of the vine** (typing data, TARGET L1895-L1910; NOT proved here).  `L₂ ≤ L₄ ≤ p`; every state of `Zp(A)` has its
carrier-side couple coherent with second parent layer `L₂` (`(zpQQ G).2 = zpQ2`, `q' ≤ q ≤ p`), and its carrier-side tree has
lone-leaf layer `L₂` (`(zpBranchQ G).2 = zpQ2`).  These are the layer identities `(q, q') = (L_{u3}, L_{u2})`, `(L_{u4}, L_{u2})`
of TARGET L1900-L1910 and must be discharged by ZP-SURJ (as extra fields of `ZpSurj.coherent`) or from the molecule layering. -/
structure ZpLayers : Prop where
  le : zpQ2 A pstar ≤ zpQ4 A pstar
  le_p : zpQ4 A pstar ≤ p
  pair : ∀ G ∈ zpFinset p kind pstar J A sp0 hA, (zpQQ G.1 pstar).2 = zpQ2 A pstar ∧
    (zpQQ G.1 pstar).2 ≤ (zpQQ G.1 pstar).1 ∧ (zpQQ G.1 pstar).1 ≤ p
  branch : ∀ G ∈ zpFinset p kind pstar J A sp0 hA, (zpBranchQ G.1 pstar).2 = zpQ2 A pstar ∧
    (zpBranchQ G.1 pstar).2 ≤ (zpBranchQ G.1 pstar).1

variable {p kind J}

variable (p kind J) in
/-- `bsA ∪ bsB` with the classical union instance used by `replSum_decomp_ext`. -/
noncomputable def zpBsU : Finset (ST w ι pstar J) :=
  @Union.union (Finset (ST w ι pstar J)) (@Finset.instUnion _ fun a b => Classical.propDecidable (a = b))
    (bsA p kind J A sp0 hA) (bsB p kind J A sp0 hA)

theorem mem_zpBsU {b : ST w ι pstar J} : b ∈ zpBsU p kind J A sp0 hA ↔ b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA := by
  unfold zpBsU; exact @Finset.mem_union _ (fun a b => Classical.propDecidable (a = b)) _ _ _

theorem zp_mem_of_bs {b : ST w ι pstar J} (h : b ∈ zpBsU p kind J A sp0 hA) :
    b ∈ zpFinset p kind pstar J A sp0 hA := by
  classical
  rcases (mem_zpBsU A sp0 hA).mp h with h | h
  · exact (Finset.mem_filter.mp h).1
  · exact (Finset.mem_filter.mp h).1

open Classical in
/-- **`hsub`**: `b ∈ bsA ∪ bsB` with both roots `≤ L₄` lies in `bsA ∩ bsB`. -/
theorem zp_hsub : ∀ b ∈ zpBsU p kind J A sp0 hA, zpLq b ≤ zpQ4 A pstar → zpLt b ≤ zpQ4 A pstar →
    b ∈ bsA p kind J A sp0 hA ∧ b ∈ bsB p kind J A sp0 hA := by
  classical
  intro b hb h1 h2
  have hroots : ZpRootsLE A b.1 pstar := ⟨h1, h2⟩
  have hz := zp_mem_of_bs A sp0 hA hb
  have hn : nuOf b.1 pstar ≠ 1 := by
    intro hn1
    rcases (mem_zpBsU A sp0 hA).mp hb with h | h
    · rcases (Finset.mem_filter.mp h).2 with ⟨hn, -⟩ | ⟨-, hr⟩
      · exact hn hn1
      · exact hr hroots
    · exact (Finset.mem_filter.mp h).2 hn1
  refine ⟨Finset.mem_filter.mpr ⟨hz, Or.inl ⟨hn, hroots⟩⟩, Finset.mem_filter.mpr ⟨hz, hn⟩⟩

open Classical in
/-- The leading-sum index set is the set of II-b states with roots `≤ L₄`. -/
theorem zp_filter_eq :
    (zpBsU p kind J A sp0 hA).filter (fun b => zpLq b ≤ zpQ4 A pstar ∧ zpLt b ≤ zpQ4 A pstar) =
      zpMinusFin p kind pstar J A sp0 hA := by
  ext b
  simp only [Finset.mem_filter, zpMinusFin]
  constructor
  · rintro ⟨hb, h1, h2⟩
    have hz := zp_mem_of_bs A sp0 hA hb
    have hbb := zp_hsub A sp0 hA b hb h1 h2
    have hn : nuOf b.1 pstar ≠ 1 := (Finset.mem_filter.mp hbb.2).2
    exact ⟨hz, (units_ne_one_iff _).mp hn, h1, h2⟩
  · rintro ⟨hz, hn, h1, h2⟩
    have hn' : nuOf b.1 pstar ≠ 1 := (units_ne_one_iff _).mpr hn
    exact ⟨(mem_zpBsU A sp0 hA).mpr (Or.inr (Finset.mem_filter.mpr ⟨hz, hn'⟩)), h1, h2⟩

end
end WaveTurbulence.VineEstS5C.P1
