/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL26
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL25
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL21
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.GL26`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **G3-LOWDEG (R48), part 26: the collection data and the `subpro` obligations on `M.unloop`.**  `CollData.unloop`,
`SubproOblG.unloop`, `TripleDesig.unloop`, `DegenSGT.unloop`, from the data on `M`, the `ε`-support (`heq`) and `HingeNoLoop`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem Src.Object.lift_unloop {M : Molecule V D} (P : Src.Object Src.γL M) (h : LoopFreeSet M P.atoms) (h' : LoopFreeSet M (P.unloop h).atoms) :
    (P.unloop h).lift h' = P := by
  obtain ⟨S, a, b, sh⟩ := P
  cases sh with
  | vc hv => rfl
  | hyper R => rfl

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.lift_unloop := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.Object.lift_unloop
theorem Src.Object.unloop_lift {M : Molecule V D} (P : Src.Object Src.γL M.unloop) (h : LoopFreeSet M P.atoms) (h' : LoopFreeSet M (P.lift h).atoms) :
    (P.lift h).unloop h' = P := by
  obtain ⟨S, a, b, sh⟩ := P
  cases sh with
  | vc hv => rfl
  | hyper R => rfl

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.unloop_lift := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.Object.unloop_lift
/-- The designated bonds of a hinge are not loop darts: `HingeNoLoop`. -/
def HingeNoLoop {M : Molecule V D} (C : CollData M) : Prop :=
  ∀ v ∈ C.hinges, ∀ y : D, M.atom y = v → M.atom (M.mate y) ≠ v

/-- The collection data transported to `M.unloop` (the collected objects are loop-free). -/
noncomputable def CollData.unloop {M : Molecule V D} (C : CollData M) : CollData M.unloop where
  n := C.n
  collection := fun i => (C.collection i).unloop (Src.Object.loopFree _)
  hinges := C.hinges
  first := fun v => (C.first v).bind (toNL M)
  second := fun v => (C.second v).bind (toNL M)

theorem isDV_loopFree {M : Molecule V D} {S : Finset V} {a b : V} (h : Src.IsDV Src.γL M S a b) : LoopFreeSet M S := by
  obtain ⟨-, A, B, hA, hB, -, rfl⟩ := h
  intro y hy
  rcases Finset.mem_union.1 hy with h | h
  · exact isSomeVine_noLoopL hA y h
  · exact isSomeVine_noLoopL hB y h

variable {R' : ℕ} {M : Molecule V D} {C : CollData M} {L γ η : ℝ} {w : Mom d} {κ : D → Fin d → ℤ}

/-- The hypotheses of the loop transport (named inputs): the bounds of `M`, the conservation hypotheses of the decoration, and the
`ε`-support `heq` (all legs of a loop atom carry the same label). -/
structure LoopCtx (L : ℝ) (w : Mom d) (κ : D → Fin d → ℤ) (R' : ℕ) (M : Molecule V D) : Prop where
  hS : SubHypL R' M.unloop
  hb : ∀ a ∈ M.atoms, M.deg a ≤ 4
  hκ : ∀ x, κ (M.mate x) = κ x
  heq : ∀ y : D, M.atom y = M.atom (M.mate y) → ∀ z : D, M.atom z = M.atom y → κ z = κ y
  h0 : ∀ a ∈ M.unloop.atoms, M.unloop.deg a = 4 →
    ∑ x ∈ M.unloop.dartsAt a, M.unloop.dartSign x • Molecule.kvec L w (fun y : NonLoop M => κ y.1) x = 0

theorem LoopCtx.noLoop (hC : LoopCtx L w κ R' M) (γ η : ℝ) (P : Src.Object Src.γL M.unloop)
    (hSG : P.HasGapKind L γ η w (fun y : NonLoop M => κ y.1) .SG) : LoopFreeSet M P.atoms :=
  Src.Object.noLoop_of_SG hC.hS hC.hb L γ η w κ hC.hκ hC.heq hC.h0 P hSG

theorem SubproOblG.unloopL (hC : LoopCtx L w κ R' M) (hH : HingeNoLoop C) (obl : SubproOblG C L γ η w κ) :
    SubproOblG C.unloop L γ η w (fun y : NonLoop M => κ y.1) where
  contained := by
    intro P hSG hOut hdis
    have hlf := hC.noLoop γ η P hSG
    have hSG' : (P.lift hlf).HasGapKind L γ η w κ .SG := (Src.Object.lift_hasGapKind P hlf L γ η w κ _).2 hSG
    have hOut' : C.Outside (P.lift hlf) := fun i hi => hOut i (by
      have : (P.lift hlf).atoms = P.atoms := rfl
      rw [this] at hi; exact hi)
    obtain hh := obl.contained (P.lift hlf) hSG' hOut' hdis
    rcases hh with ⟨S, a, b, hdv, hsub, hd1, hd2⟩ | ⟨Q, hPQ, hQk, hQ1, hQ2⟩
    · left
      exact ⟨S, a, b, (unloopEmb M (isDV_loopFree hdv)).isDV_ofL rfl hdv, hsub, hd1, fun i => hd2 i⟩
    · right
      refine ⟨Q.unloop (Src.Object.loopFree Q), hPQ, ?_, hQ1, fun i => hQ2 i⟩
      rcases hQk with h | h
      · exact Or.inl ((Src.Object.unloop_hasGapKind Q _ L γ η w κ _).2 h)
      · exact Or.inr ((Src.Object.unloop_hasGapKind Q _ L γ η w κ _).2 h)
  hingeSG := by
    intro v hv
    obtain ⟨x, y, hx, hy, hT, hsg⟩ := obl.hingeSG v hv
    have hnx : M.atom x ≠ M.atom (M.mate x) := by rw [hT.1]; exact (hH v hv x hT.1).symm
    have hny : M.atom y ≠ M.atom (M.mate y) := by rw [hT.2.1]; exact (hH v hv y hT.2.1).symm
    exact ⟨⟨x, hnx⟩, ⟨y, hny⟩, by simp [CollData.unloop, hx, toNL_some hnx], by simp [CollData.unloop, hy, toNL_some hny],
      tripleAtM_unloop hnx hny hT, hsg⟩
  hingeJoint := by
    intro v hv i hvi
    obtain ⟨x, y, hx, hy, hxc, hyc⟩ := obl.hingeJoint v hv i hvi
    obtain ⟨x₀, y₀, hx₀, hy₀, hT, -⟩ := obl.hingeSG v hv
    have hxx : x₀ = x := Option.some.inj (hx₀.symm.trans hx)
    have hyy : y₀ = y := Option.some.inj (hy₀.symm.trans hy)
    subst hxx hyy
    have hnx : M.atom x₀ ≠ M.atom (M.mate x₀) := by rw [hT.1]; exact (hH v hv x₀ hT.1).symm
    have hny : M.atom y₀ ≠ M.atom (M.mate y₀) := by rw [hT.2.1]; exact (hH v hv y₀ hT.2.1).symm
    refine ⟨⟨x₀, hnx⟩, ⟨y₀, hny⟩, by simp [CollData.unloop, hx, toNL_some hnx], by simp [CollData.unloop, hy, toNL_some hny], ?_, ?_⟩
    · exact (Src.Object.unloop_containsDart (C.collection i) _ ⟨x₀, hnx⟩).2 hxc
    · exact (Src.Object.unloop_containsDart (C.collection i) _ ⟨y₀, hny⟩).2 hyc
  crossing := by
    intro P hSG hOut hnd
    have hlf := hC.noLoop γ η P hSG
    have hSG' : (P.lift hlf).HasGapKind L γ η w κ .SG := (Src.Object.lift_hasGapKind P hlf L γ η w κ _).2 hSG
    have hOut' : C.Outside (P.lift hlf) := fun i hi => hOut i (by
      have : (P.lift hlf).atoms = P.atoms := rfl
      rw [this] at hi; exact hi)
    obtain ⟨v, hvH, hvP, hcase⟩ := obl.crossing (P.lift hlf) hSG' hOut' hnd
    refine ⟨v, hvH, hvP, ?_⟩
    rcases hcase with ⟨h1, h2⟩ | ⟨hj, x, y, hx, hy, hxor⟩
    · exact Or.inl ⟨h1, h2⟩
    · right
      refine ⟨hj, ?_⟩
      obtain ⟨x₀, y₀, hx₀, hy₀, hT, -⟩ := obl.hingeSG v hvH
      have hxx : x₀ = x := Option.some.inj (hx₀.symm.trans hx)
      have hyy : y₀ = y := Option.some.inj (hy₀.symm.trans hy)
      subst hxx hyy
      have hnx : M.atom x₀ ≠ M.atom (M.mate x₀) := by rw [hT.1]; exact (hH v hvH x₀ hT.1).symm
      have hny : M.atom y₀ ≠ M.atom (M.mate y₀) := by rw [hT.2.1]; exact (hH v hvH y₀ hT.2.1).symm
      refine ⟨⟨x₀, hnx⟩, ⟨y₀, hny⟩, by simp [CollData.unloop, hx, toNL_some hnx], by simp [CollData.unloop, hy, toNL_some hny], ?_⟩
      have e1 := Src.Object.lift_containsDart P hlf ⟨x₀, hnx⟩
      have e2 := Src.Object.lift_containsDart P hlf ⟨y₀, hny⟩
      simp only [Xor'] at hxor ⊢
      rw [e1, e2] at hxor
      exact hxor

theorem TripleDesig.unloopL (hH : HingeNoLoop C) (hT3 : TripleDesig C) : TripleDesig C.unloop := by
  intro a b ha hb hab h3
  have e := unloop_bondsBetween M hab
  obtain ⟨v, c, x, y, hvc, hv, hx, hy, hT, hcx, hcy⟩ := hT3 a b ha hb hab (by rw [← e]; exact h3)
  have hvc' : v ≠ c := by rcases hvc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hab; exact hab.symm]
  have hnx : M.atom x ≠ M.atom (M.mate x) := by rw [hT.1, hcx]; exact hvc'
  have hny : M.atom y ≠ M.atom (M.mate y) := by rw [hT.2.1, hcy]; exact hvc'
  exact ⟨v, c, ⟨x, hnx⟩, ⟨y, hny⟩, hvc, hv, by simp [CollData.unloop, hx, toNL_some hnx],
    by simp [CollData.unloop, hy, toNL_some hny], tripleAtM_unloop hnx hny hT, hcx, hcy⟩

theorem DegenSGT.unloopL {Tm : V → Prop} (hC : LoopCtx L w κ R' M) (hdeg : DegenSGT M L γ η w κ Tm) :
    DegenSGT M.unloop L γ η w (fun y : NonLoop M => κ y.1) Tm := by
  intro a ha x y hx hy hox hoy hne hzg
  rcases hdeg a ha x.1 y.1 hx hy hox hoy (fun e => hne (Subtype.ext e)) hzg with ⟨x₀, y₀, h1, h2, h3, h4, h5, h6⟩ | hT
  · left
    have hnx : M.atom x₀ ≠ M.atom (M.mate x₀) := by
      intro hl
      have := hC.heq x₀ hl y₀ (h2.trans h1.symm)
      unfold Molecule.gapAt Molecule.kvec at h6
      rw [this] at h6; simp [gapKind_zero] at h6
    have hny : M.atom y₀ ≠ M.atom (M.mate y₀) := by
      intro hl
      have := hC.heq y₀ hl x₀ (h1.trans h2.symm)
      unfold Molecule.gapAt Molecule.kvec at h6
      rw [this] at h6; simp [gapKind_zero] at h6
    exact ⟨⟨x₀, hnx⟩, ⟨y₀, hny⟩, h1, h2, h3, h4, fun e => h5 (congrArg Subtype.val e), h6⟩
  · exact Or.inr hT

end WaveTurbulence.GammaLow.FinalCount.H
