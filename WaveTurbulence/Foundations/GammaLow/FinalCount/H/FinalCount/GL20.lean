/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL20
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.Invariance
public import WaveTurbulence.Foundations.Spine.SourceVineSigma
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunE
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.VineLocalDartObjects
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.GL20`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **G3-LOWDEG (R48), part 20: invariance of the group predicates under a dart embedding that is onto the group darts.**
`GEmb M1 M2 ι S`: `ι : D1 → D2` is an injective, `atom/mate/out`-compatible embedding such that every dart of `M2` with both ends in
`S` is in the range (cover).  Then `degIn/outIn/inIn`, `GroupConnected`, `groupBonds`, `IsBlock`, `IsVine`, `IsSomeVine`, `Chain`, `IsVC`
agree on `S` (iff).  Used for `M.unloop ↪ M` (`S` without loop atoms) and `eraseBond (M.unloop) ↪ eraseBond M`. 

Low-range additions (L6-HLOW): `sigma_eqL`, `isVine_iffT` (L6-HTV's `TV.isTVine_iff_of_groupBonds_eq`) and the family
transport `isVine_iffS` (main's `isVine_iff` at (I), (II) plus `isVine_iffT`); the DV′ transports carry `σ = 1`
(`Src.IsDV` is `IsDVPrime`, which has the `σ` clause that main's `IsDV` lacks).-/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine
variable {V : Type*} [DecidableEq V] {D1 D2 : Type*} [Fintype D1] [DecidableEq D1] [Fintype D2] [DecidableEq D2]

namespace GEmb
open WaveTurbulence.FinalCountG3.GEmb
variable {M1 : Molecule V D1} {M2 : Molecule V D2} {ι : D1 → D2} {S : Finset V} (G : GEmb M1 M2 ι S)
include G

/-- `σ` (the number of bonds) between two atoms of the group is invariant (low-range addition, L6-HLOW). -/
theorem sigma_eqL {a b : V} (ha : a ∈ S) (hb : b ∈ S) : M2.sigma a b = M1.sigma a b := by
  unfold Molecule.sigma
  rw [LGSpine.bondsBetween_eq_count_groupBonds ha hb, LGSpine.bondsBetween_eq_count_groupBonds ha hb, G.groupBonds_eq]

alias _root_.WaveTurbulence.FinalCountG3.GEmb.sigma_eqL := _root_.WaveTurbulence.GammaLow.FinalCount.H.GEmb.sigma_eqL
/-- T-vines transport along the embedding (L6-HTV's `isTVine_iff_of_groupBonds_eq`; low-range addition, L6-HLOW). -/
theorem isVine_iffT (hat : M1.atoms = M2.atoms) {j₁ j₂ : V} : M2.IsTVine S j₁ j₂ ↔ M1.IsTVine S j₁ j₂ :=
  TV.isTVine_iff_of_groupBonds_eq G.groupBonds_eq (G.isBlock_iff hat)

alias _root_.WaveTurbulence.FinalCountG3.GEmb.isVine_iffT := _root_.WaveTurbulence.GammaLow.FinalCount.H.GEmb.isVine_iffT
/-- Family members transport along the embedding: main's `isVine_iff` at (I), (II), and `isVine_iffT`. -/
theorem isVine_iffS (hat : M1.atoms = M2.atoms) {j₁ j₂ : V} :
    Src.IsSomeVine Src.γL M2 S j₁ j₂ ↔ Src.IsSomeVine Src.γL M1 S j₁ j₂ := by
  rw [Src.isSomeVine_γL_iff, Src.isSomeVine_γL_iff]
  unfold Molecule.IsVineEnl
  simp only [G.isVine_iff hat, isVine_iffT G hat]

alias _root_.WaveTurbulence.FinalCountG3.GEmb.isVine_iffS := _root_.WaveTurbulence.GammaLow.FinalCount.H.GEmb.isVine_iffS
theorem isSomeVine_iffL (hat : M1.atoms = M2.atoms) {a b : V} : Src.IsSomeVine Src.γL M2 S a b ↔ Src.IsSomeVine Src.γL M1 S a b := by
  exact isVine_iffS G hat

alias _root_.WaveTurbulence.FinalCountG3.GEmb.isSomeVine_iffL := _root_.WaveTurbulence.GammaLow.FinalCount.H.GEmb.isSomeVine_iffL
theorem chain_iffL (hat : M1.atoms = M2.atoms) {S' : Finset V} (hsub : S' ⊆ S) {a b : V} {n : ℕ} :
    Src.Chain Src.γL M2 S' a b n ↔ Src.Chain Src.γL M1 S' a b n := by
  constructor
  · intro h
    revert hsub
    induction h with
    | single h => intro hs; exact Src.Chain.single (((G.mono hs).isSomeVine_iffL hat).1 h)
    | append hc hv hinter hne ih =>
      rename_i S₁ T₁ a₁ b₁ c₁ n₁
      intro hs
      exact Src.Chain.append (ih (fun x hx => hs (Finset.mem_union_left _ hx)))
        (((G.mono (fun x hx => hs (Finset.mem_union_right _ hx))).isSomeVine_iffL hat).1 hv) hinter hne
  · intro h
    revert hsub
    induction h with
    | single h => intro hs; exact Src.Chain.single (((G.mono hs).isSomeVine_iffL hat).2 h)
    | append hc hv hinter hne ih =>
      rename_i S₁ T₁ a₁ b₁ c₁ n₁
      intro hs
      exact Src.Chain.append (ih (fun x hx => hs (Finset.mem_union_left _ hx)))
        (((G.mono (fun x hx => hs (Finset.mem_union_right _ hx))).isSomeVine_iffL hat).2 hv) hinter hne

alias _root_.WaveTurbulence.FinalCountG3.GEmb.chain_iffL := _root_.WaveTurbulence.GammaLow.FinalCount.H.GEmb.chain_iffL
theorem isVC_iffL (hat : M1.atoms = M2.atoms) {a b : V} : Src.IsVC Src.γL M2 S a b ↔ Src.IsVC Src.γL M1 S a b := by
  unfold Src.IsVC
  rw [G.isBlock_iff hat]
  simp only [G.chain_iffL hat (Finset.Subset.refl S)]

alias _root_.WaveTurbulence.FinalCountG3.GEmb.isVC_iffL := _root_.WaveTurbulence.GammaLow.FinalCount.H.GEmb.isVC_iffL
theorem isDV_ofL (hat : M1.atoms = M2.atoms) {a b : V} (h : Src.IsDV Src.γL M2 S a b) : Src.IsDV Src.γL M1 S a b := by
  obtain ⟨hσ, A, B, hA, hB, hAB, rfl⟩ := h
  have hA' : Src.IsSomeVine Src.γL M2 A a b := hA
  refine ⟨?_, A, B, ((G.mono (Finset.subset_union_left)).isVine_iffS hat).1 hA,
    ((G.mono (Finset.subset_union_right)).isVine_iffS hat).1 hB, hAB, rfl⟩
  rw [← sigma_eqL G (Finset.mem_union_left _ hA'.ends.1) (Finset.mem_union_left _ hA'.ends.2.1)]
  exact hσ

alias _root_.WaveTurbulence.FinalCountG3.GEmb.isDV_ofL := _root_.WaveTurbulence.GammaLow.FinalCount.H.GEmb.isDV_ofL

end GEmb
end WaveTurbulence.GammaLow.FinalCount.H
