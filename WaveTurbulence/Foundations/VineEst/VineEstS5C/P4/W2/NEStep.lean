/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowNE

/-! # P4-W2 (a): the native-except row form is preserved by the glue step and by the bottom summand

* `DomX R lay Bex t₀ t₁ t₂ u`: the native clock domain of the region `R` (windows, parent-clock order of every interior branch, boundary
  conditions `t₁ < u_b`, `t₂ < u_b` at the bottom joint) with the parent-clock condition dropped at the branches of `Bex`.
* `domX_glue`: `DomF S a b u ∧ DomX RT Bex' (u b) t₁ t₂ u ↔ DomX RU (insert b Bex') t₀ t₁ t₂ u` when `u a = t₀`.
* **`rowFormNE_step`**: if `Ψ'` has a native-except row form on `T` (exceptional pairs `Pex'`, branches `Bex'`), then the glued summand
  `spartFrame(S,a,b,p₀)(rA x,u) · X(rA x,u) · Ψ'(rB x, (u b, t₁, t₂), u)` has one on `U = S ∪ T` with `Pex = {p₀} ∪ Pex'`, `Bex = {b} ∪ Bex'`.
* **`rowFormNE_bot`**: the bottom summand `spartFrame(U,a,b,p₀) · bFac · X` has one with `Pex = {p₀}`, `Bex = {b}`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot

variable {w d : ℕ} {G : Garden w}

/-- The native clock domain of a region with the parent-clock condition dropped at the branches of `Bex`. -/
def DomX {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b) (lay : GBranch G.tree → ℕ)
    (Bex : Finset (GBranch G.tree)) (t0 t1 t2 : ℝ) (u : GBranch G.tree → ℝ) : Prop :=
  (∀ v ∈ clInteriorBranches R, (lay v : ℝ) < u v ∧ u v < lay v + 1 ∧ 0 < u v ∧
      (v ∉ Bex → u v < parentClock t0 u v.toNode)) ∧
    ((b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching → t1 < u b) ∧
    ((b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching → t2 < u b)

theorem domX_empty {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b) (lay : GBranch G.tree → ℕ)
    (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) : DomX R lay ∅ (t 0) (t 1) (t 2) u ↔ ClDom R lay t u := by
  unfold DomX ClDom
  simp only [Finset.notMem_empty, not_false_eq_true, forall_const]

section Step
variable {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
  (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c)

include hS hT hi hU in
theorem domX_glue (RU : CLRegionData G (S ∪ T) a c) (RT : CLRegionData G T b c) (lay : GBranch G.tree → ℕ)
    (Bex' : Finset (GBranch G.tree)) (hB' : Bex' ⊆ T.erase b) (t0 t1 t2 : ℝ) (u : GBranch G.tree → ℝ) (hu : u a = t0) :
    (DomF lay S a b u ∧ DomX RT lay Bex' (u b) t1 t2 u) ↔ DomX RU lay (insert b Bex') t0 t1 t2 u := by
  have hpos := (split_positive_c hS hT hi hU RU RT).1
  have hneg := (split_positive_c hS hT hi hU RU RT).2
  have hxT : ∀ v ∈ T.erase b, v.toNode ∈ clRealizationNodes G T ∧ v.toNode ≠ b.toNode := by
    intro v hv
    obtain ⟨hvb, hvT⟩ := Finset.mem_erase.mp hv
    exact ⟨(branch_mem_clRealizationNodes v).mpr hvT, fun h => hvb (Mole.branch_toNode_injective h)⟩
  have hpc : ∀ v ∈ T.erase b, parentClock (u b) u v.toNode = parentClock t0 u v.toNode := by
    intro v hv
    obtain ⟨hr, hn⟩ := hxT v hv
    obtain ⟨hn', hp⟩ := cl_realization_parent hT RT v.toNode hr hn
    rw [parentClock_nonroot _ _ _ hn', parentClock_nonroot _ _ _ hn']
  have hSB : ∀ v ∈ S.erase a, v ∉ Bex' := fun v hv hm =>
    Finset.disjoint_left.mp (split_interior_disjoint hS hT hi hU) hv (hB' hm)
  unfold DomF DomX
  rw [← hpos, ← hneg]
  change _ ↔ (∀ v ∈ (S ∪ T).erase a, _) ∧ _
  rw [split_interior hS hT hi hU]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun v hv => ?_, h3, h4⟩
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨w1, w2, w3, w4⟩ := h1 v hv
      refine ⟨w1, w2, w3, fun hn => ?_⟩
      have hvb : v ≠ b := fun e => hn (e ▸ Finset.mem_insert_self _ _)
      have := w4 hvb
      rwa [hu] at this
    · obtain ⟨w1, w2, w3, w4⟩ := h2 v hv
      refine ⟨w1, w2, w3, fun hn => ?_⟩
      have := w4 (fun h => hn (Finset.mem_insert_of_mem h))
      rwa [hpc v hv] at this
  · rintro ⟨h1, h3, h4⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_, h3, h4⟩
    · obtain ⟨w1, w2, w3, w4⟩ := h1 v (Finset.mem_union_left _ hv)
      refine ⟨w1, w2, w3, fun hvb => ?_⟩
      have := w4 (by
        rw [Finset.mem_insert]
        rintro (e | e)
        · exact hvb e
        · exact hSB v hv e)
      rwa [hu]
    · obtain ⟨w1, w2, w3, w4⟩ := h1 v (Finset.mem_union_right _ hv)
      refine ⟨w1, w2, w3, fun hn => ?_⟩
      have := w4 (by
        rw [Finset.mem_insert]
        rintro (e | e)
        · exact (Finset.mem_erase.mp hv).1 e
        · exact hn e)
      rwa [← hpc v hv] at this

include hS hT hi hU in
/-- **The native-except row form is preserved by the glue step.** -/
theorem rowFormNE_step (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (hL : L ≠ 0) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b) (RT : CLRegionData G T b c)
    (p0 : SourcePair G) (hp0 : p0 ∈ clRegionalPairs hG S) (hb : b ∈ S.erase a)
    (X : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ) (Ψ' : PsiT G d)
    {Dm' : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop} {Pex' : Finset (SourcePair G)} {Bex' : Finset (GBranch G.tree)}
    {Xq' : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ}
    (hP' : Pex' ⊆ clRegionalPairs hG T) (hB' : Bex' ⊆ T.erase b)
    (hΨ : RowFormNE D hG L γ δ F layer hLayer RT base Ψ' Dm' Pex' Bex' Xq') :
    open Classical in
    RowFormNE D hG L γ δ F layer hLayer RU base
      (fun x t u => spartFrame D hG L γ δ F layer hLayer base S a b p0 (rA RS x) u * X (rA RS x) u *
        Ψ' (rB RT x) ![u b, t 1, t 2] u)
      (fun t u => DomF (fun v => layer (D.coreBranch hG v).toNode) S a b u ∧ Dm' ![u b, t 1, t 2] u)
      (insert p0 Pex') (insert b Bex')
      (fun p t u x => if p = p0 then X (rA RS x) u else Xq' p ![u b, t 1, t 2] u (rB RT x)) := by
  classical
  have hstep := rowForm_step hS hT hi hU D hG L γ δ hL F layer hLayer base RU RS RT p0 hp0 hb X Ψ' hΨ
  refine rowForm_congr hG RU L γ δ base _ _ hstep ?_ ?_
  · intro p hp t u x
    have hpU : p ∈ clRegionalPairs hG S ∪ clRegionalPairs hG T := by rwa [← split_pairs hS hT hi hU hG]
    have hdis := split_pairs_disjoint hS hT hi hU hG
    by_cases hpS : p ∈ clRegionalPairs hG S
    · have hpT : p ∉ clRegionalPairs hG T := Finset.disjoint_left.mp hdis hpS
      have hnP : p ≠ p0 → p ∉ Pex' := fun _ h => hpT (hP' h)
      have hq : qRow D hG L γ δ F layer hLayer base (u a) (rA RS x) u p = qRow D hG L γ δ F layer hLayer base (t 0) x u p := by
        rw [qRow_restrict D hG L γ δ F layer hLayer base (U := S) hpS (u a) (x' := x) (rA_real RS x) u]
        exact qRow_top D hG L γ δ F layer hLayer base hS RS hpS _ _ x u
      simp only [if_pos hpS]
      by_cases he : p = p0
      · subst he; simp
      · simp [he, hnP he, hq]
    · have hpT : p ∈ clRegionalPairs hG T := (Finset.mem_union.mp hpU).resolve_left hpS
      have hne : p ≠ p0 := fun e => hpS (e ▸ hp0)
      have hq : qRow D hG L γ δ F layer hLayer base (u b) (rB RT x) u p =
          qRow D hG L γ δ F layer hLayer base (t 0) x u p := by
        rw [qRow_restrict D hG L γ δ F layer hLayer base (U := T) hpT _ (x' := x) (rB_real RT x) u]
        exact qRow_top D hG L γ δ F layer hLayer base hT RT hpT _ _ x u
      simp only [if_neg hpS, Finset.mem_insert, hne, false_or, if_neg hne]
      by_cases hP : p ∈ Pex'
      · simp [hP]
      · simp [hP, hq]
  · intro v hv t u x
    have hvU : v ∈ S.erase a ∪ T.erase b := by rwa [← split_interior hS hT hi hU]
    have hdis := split_interior_disjoint hS hT hi hU
    by_cases hvS : v ∈ S.erase a
    · have hvT : v ∉ T.erase b := Finset.disjoint_left.mp hdis hvS
      have hnB : v ≠ b → v ∉ Bex' := fun _ h => hvT (hB' h)
      have ht : tRow D hG L γ δ F layer hLayer base (u a) (rA RS x) u v = tRow D hG L γ δ F layer hLayer base (t 0) x u v := by
        rw [tRow_restrict D hG L γ δ F layer hLayer base (U := S) (Finset.mem_of_mem_erase hvS) (u a) (x' := x) (rA_real RS x) u]
        exact tRow_top D hG L γ δ F layer hLayer base hS RS hvS _ _ x u
      simp only [if_pos hvS]
      by_cases he : v = b
      · subst he; simp
      · simp [he, hnB he, ht]
    · have hvT : v ∈ T.erase b := (Finset.mem_union.mp hvU).resolve_left hvS
      have hne : v ≠ b := (Finset.mem_erase.mp hvT).1
      have ht : tRow D hG L γ δ F layer hLayer base (u b) (rB RT x) u v =
          tRow D hG L γ δ F layer hLayer base (t 0) x u v := by
        rw [tRow_restrict D hG L γ δ F layer hLayer base (U := T) (Finset.mem_of_mem_erase hvT) _ (x' := x) (rB_real RT x) u]
        exact tRow_top D hG L γ δ F layer hLayer base hT RT hvT _ _ x u
      simp only [if_neg hvS, Finset.mem_insert, hne, false_or]
      by_cases hB : v ∈ Bex'
      · simp [hB]
      · simp [hB, ht]

end Step

/-- **The native-except row form of the bottom summand.** -/
theorem rowFormNE_bot (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (p0 : SourcePair G) (hp0 : p0 ∈ clRegionalPairs hG U) (hb : b ∈ U.erase a)
    (X : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ) :
    RowFormNE D hG L γ δ F layer hLayer R base
      (fun x t u => spartFrame D hG L γ δ F layer hLayer base U a b p0 x u * bFac R L γ δ base x t u * X x u)
      (fun t u => DomF (fun v => layer (D.coreBranch hG v).toNode) U a b u ∧ bTimeOK R t u)
      {p0} {b} (fun _ _ u x => X x u) := by
  classical
  have hbot := rowForm_bot D hG L γ δ F layer hLayer base R p0 hp0 hb X
  refine rowForm_congr hG R L γ δ base _ _ hbot ?_ ?_
  · intro p hp t u x
    by_cases he : p = p0
    · subst he; simp
    · simp only [he, if_false, Finset.mem_singleton]
      exact qRow_top D hG L γ δ F layer hLayer base hU R hp _ _ x u
  · intro v hv t u x
    by_cases he : v = b
    · subst he; simp
    · simp only [he, if_false, Finset.mem_singleton]
      exact tRow_top D hG L γ δ F layer hLayer base hU R hv _ _ x u

end WaveTurbulence.VineEstS5C.P4.W2
