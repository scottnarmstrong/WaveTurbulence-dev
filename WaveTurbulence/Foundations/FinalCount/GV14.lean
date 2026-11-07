/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GV13
public import WaveTurbulence.Foundations.FinalCount.G3VineBridge
public import WaveTurbulence.Foundations.FinalCount.GL13
public import WaveTurbulence.Foundations.FinalCount.GL12
/-! **G3-LOWDEG port of `G3VineLG10`** (only the declarations that change: `SubHypL->SubHypL`, `HRunL->HRunL`, `InvL->InvL`, `FinalStructM->FinalStructM`, `Prop95ConclAtL->Prop95ConclAtL`; names get suffix `L`). -/
@[expose] public section
open WaveTurbulence.VineParamContract

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {R : ℕ} {M₀ : Molecule V D₀} {hf : HSt V D₀} {Tm : V → Prop}

/-- A vine component of the final molecule has the shape `FinalJoints` (LOW: the component has no low-degree `ε`-atom). -/
theorem finalJoints_of_vineL {hf : HSt V D₀} {a₀ j₁ j₂ : V} (hst : FinalStructM R hf.s) (hE : LowFree hf a₀) {X : VineType}
    (hv : (compMol hf.s.M a₀).IsVine X (compMol hf.s.M a₀).atoms j₁ j₂) (ha₀ : a₀ ∈ hf.s.M.atoms) :
    FinalJoints hf a₀ j₁ j₂ := by
  obtain ⟨-, h1, h2, hne, o1, i1, o2, i2, hd, -⟩ := hv.1
  have m1 := (mem_compMol _ _).1 h1
  have m2 := (mem_compMol _ _).1 h2
  have hg := compMol_grp hf a₀
  have d1 : hf.s.M.deg j₁ = 2 := by
    rw [← compMol_deg hf.s.M a₀ m1.2, deg_eq, ← outIn_of_all hg, ← inIn_of_all hg, o1, i1]
  have d2 : hf.s.M.deg j₂ = 2 := by
    rw [← compMol_deg hf.s.M a₀ m2.2, deg_eq, ← outIn_of_all hg, ← inIn_of_all hg, o2, i2]
  refine ⟨m1.1, m2.1, hne, m1.2, m2.2, d1, d2, ?_, ?_, ?_⟩
  · intro h; have := hE j₁ (Finset.mem_filter.2 m1) h; omega
  · intro h; have := hE j₂ (Finset.mem_filter.2 m2) h; omega
  · intro b hb hbc
    by_cases e1 : b = j₁
    · exact Or.inl e1
    by_cases e2 : b = j₂
    · exact Or.inr (Or.inl e2)
    right; right
    have hbm : b ∈ (compMol hf.s.M a₀).atoms := (mem_compMol _ _).2 ⟨hb, hbc⟩
    have h4 := hd b hbm e1 e2
    have hdeg : hf.s.M.deg b = 4 := by
      rw [← compMol_deg hf.s.M a₀ hbc, ← degIn_of_all hg]; exact h4
    refine ⟨?_, hdeg⟩
    by_contra hne'
    have := hst.ab_deg b hb hne'
    omega

/-- **The LOW run with the collection data of Operation 1** (`HRunL` + Step 1 removes the collected objects, L2101). -/
def HRunLC (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (M₀ : Molecule V D₀) (hf : HSt V D₀) (C : CollData M₀)
    (Unsel : Set (Object M₀)) : Prop :=
  ∃ h₁ h₂ h₃ h₄ : HSt V D₀,
    Relation.ReflTransGen (HStep1L C L γ η w κ) (HSt.init M₀) h₁ ∧ NoTripleCut C L γ η w κ h₁ ∧
    Relation.ReflTransGen (HStepD3 C L γ η w κ) h₁ h₂ ∧ NoD3 C L w κ h₂ ∧
    Relation.ReflTransGen (HStep2C C L γ η w κ) h₂ h₃ ∧ NoEligibleTriangle C L γ η w κ h₃ ∧
    Relation.ReflTransGen (HStep3C C L γ η w κ) h₃ h₄ ∧ NoSGLeft L γ η w κ (HSt.init M₀).s h₄.s ∧
    Relation.ReflTransGen (HStep4 L w κ) h₄ hf ∧ NoBetaCut L w κ hf.s ∧
    (∀ U, ((∃ i, U = C.collection i) ∨ U ∈ C.C2Can L γ η w κ Unsel) → ∀ x : h₁.s.D, ¬ U.ContainsDart (h₁.s.down x))

theorem HRunLC.toHRunL {C : CollData M₀} {Unsel : Set (Object M₀)} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    (h : HRunLC L γ η w κ M₀ hf C Unsel) : HRunL C L γ η w κ (HSt.init M₀) hf := by
  obtain ⟨h₁, h₂, h₃, h₄, a1, n1, a2, n2, a3, n3, a4, n4, a5, n5, -⟩ := h
  exact ⟨h₁, h₂, h₃, h₄, a1, n1, a2, n2, a3, n3, a4, n4, a5, n5⟩

theorem HStepD3.sub {C : CollData M₀} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {h h' : HSt V D₀}
    (hs : HStepD3 C L γ η w κ h h') : St.Sub h'.s h.s := by
  obtain ⟨v, x₁, x₂, hD, rfl⟩ := hs.data
  show Set.range (h.s.betaSt v).down ⊆ Set.range h.s.down
  rw [St.betaSt_down]; exact fun _ h => h

theorem HRunLC.rem {C : CollData M₀} {Unsel : Set (Object M₀)} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    (h : HRunLC L γ η w κ M₀ hf C Unsel) :
    (∀ i, ∀ x : hf.s.D, ¬ (C.collection i).ContainsDart (hf.s.down x)) ∧
    (∀ U ∈ C.C2Can L γ η w κ Unsel, ∀ x : hf.s.D, ¬ U.ContainsDart (hf.s.down x)) := by
  obtain ⟨h₁, h₂, h₃, h₄, a1, n1, a2, n2, a3, n3, a4, n4, a5, n5, hrem⟩ := h
  have s5 : St.Sub hf.s h₄.s := rtg_sub (fun _ _ h => h.sub) a5
  have s4 : St.Sub h₄.s h₃.s := rtg_sub (fun _ _ h => h.toHStep3.sub) a4
  have s3 : St.Sub h₃.s h₂.s := rtg_sub (fun _ _ h => h.toHStep2.sub) a3
  have s2 : St.Sub h₂.s h₁.s := rtg_sub (fun _ _ h => h.sub) a2
  have key : ∀ U, ((∃ i, U = C.collection i) ∨ U ∈ C.C2Can L γ η w κ Unsel) → ∀ x : hf.s.D,
      ¬ U.ContainsDart (hf.s.down x) := by
    intro U hU x hx
    obtain ⟨x', hx'⟩ := (s5.trans (s4.trans (s3.trans s2))) ⟨x, rfl⟩
    exact hrem U hU x' (by rw [hx']; exact hx)
  exact ⟨fun i x => key _ (Or.inl ⟨i, rfl⟩) x, fun U hU x => key U (Or.inr hU) x⟩

/-- The per-decoration run data of the LOW case: collection, selection, obligations of `subpro`, run with designated pairs. -/
def RunDataL (L γ η : ℝ) (M₀ : Molecule V D₀) (hf : HSt V D₀) (AdmRun : (D₀ → (Fin d → ℤ)) → Prop) : Prop :=
  ∀ κ, AdmRun κ → ∃ (C : CollData M₀) (Unsel : Set (Object M₀)), SubproOblG C L γ η (0 : Mom d) κ ∧ TripleDesig C ∧
    C.UnselOK L γ η (0 : Mom d) κ Unsel ∧ HRunLC L γ η (0 : Mom d) κ M₀ hf C Unsel

theorem vineLG_of_runL [Infinite V] (hS : SubHypL R M₀) (AdmRun : (D₀ → (Fin d → ℤ)) → Prop)
    (hrun : RunDataL L γ η M₀ hf AdmRun) (hdeg : ∀ κ, AdmRun κ → DegenSGT M₀ L γ η (0 : Mom d) κ Tm)
    (h0 : ∀ κ, AdmRun κ → ∀ a ∈ M₀.atoms, M₀.deg a = 4 →
      ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0)
    {a₀ : V} (ha₀ : a₀ ∈ hf.s.M.atoms) (hT : TameFree hf Tm a₀) (hE : LowFree hf a₀) : VineLGAtL L γ η hf a₀ AdmRun := by
  intro hvine κ' ⟨κ, hκ, hκ'⟩ x y hxy hout
  subst hκ'
  obtain ⟨C, Unsel, obl, hT3, hU, hrC⟩ := hrun κ hκ
  have hr := hrC.toHRunL
  obtain ⟨R', -, hI⟩ := hr.inv (InvL.init hS (h0 κ hκ))
  have hC := (hr.prop95L hS obl hT3 (hdeg κ hκ) (h0 κ hκ)).toAtL (fun a ha => hI.good.2 a ha)
  obtain ⟨⟨hdp, hA, hdes⟩, -⟩ := hr.final hS obl (h0 κ hκ) rfl
  have hD := hI.rel
  have hrec := hI.hrec
  obtain ⟨hrem1, hrem2⟩ := hrC.rem
  have hxm := (mem_compMol _ _).1 ((compMol hf.s.M a₀).atom_mem x)
  have hx' : hf.s.M.atom x.1 = (compMol hf.s.M a₀).atom x := rfl
  by_cases hε : hf.s.cls (hf.s.M.atom x.1) = .eps
  · exact dec_epsLGL (hf := hf) (hC := hC) (a₀ := a₀) hxm.1 hε (hT.of_sc hxm.2) x y rfl (by rw [← hxy]) hout
  · obtain ⟨X, j₁, j₂, hv⟩ := vine_of_vineOrDoubleL hC ha₀ hE hvine
    have J := finalJoints_of_vineL hC.struct hE hv ha₀
    have hcomp := J.comp _ hxm.1 hxm.2
    have hy : hf.s.M.atom y.1 = hf.s.M.atom x.1 := by rw [show hf.s.M.atom y.1 = (compMol hf.s.M a₀).atom y from rfl, ← hxy]; rfl
    have hout' : hf.s.M.out x.1 ≠ hf.s.M.out y.1 := hout
    rcases hcomp with h | h | ⟨h, -⟩
    · exact joint_LG2L hS hA hD hC hT hrec hdp obl hU hrem1 hrem2 hdes J hv x.1 y.1 h (hy.trans h) hout'
    · exact joint_LG2L hS hA hD hC hT hrec hdp obl hU hrem1 hrem2 hdes J.symm (isVine_symm hv) x.1 y.1 h (hy.trans h) hout'
    · exact absurd h hε

theorem finalDec_compL [Infinite V] (hS : SubHypL R M₀) (AdmRun : (D₀ → (Fin d → ℤ)) → Prop)
    (hrun : RunDataL L γ η M₀ hf AdmRun) (hdeg : ∀ κ, AdmRun κ → DegenSGT M₀ L γ η (0 : Mom d) κ Tm)
    (h0 : ∀ κ, AdmRun κ → ∀ a ∈ M₀.atoms, M₀.deg a = 4 →
      ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0)
    (hne : ∃ κ, AdmRun κ) (hL : 1 ≤ L) (hη : 0 ≤ η) {a₀ : V} (ha₀ : a₀ ∈ hf.s.M.atoms) (hT : TameFree hf Tm a₀)
    (hE : LowFree hf a₀) :
    G8Copy.FinalDec (compMol hf.s.M a₀) (fun a => toCls (hf.s.cls a)) L γ η (compAdmL hf a₀ AdmRun) :=
  finalDec_comp_of_vineL AdmRun (fun κ hκ => by
      obtain ⟨C, Unsel, obl, hT3, -, hrC⟩ := hrun κ hκ
      obtain ⟨R', -, hI⟩ := hrC.toHRunL.inv (InvL.init hS (h0 κ hκ))
      exact (hrC.toHRunL.prop95L hS obl hT3 (hdeg κ hκ) (h0 κ hκ)).toAtL (fun a ha => hI.good.2 a ha)) hne hL hη ha₀ hT
    (vineLG_of_runL hS AdmRun hrun hdeg h0 ha₀ hT hE)

end WaveTurbulence.FinalCountG3
