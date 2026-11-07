/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineLG8
public import WaveTurbulence.Foundations.FinalCount.G3ConclN
/-! **FINALCOUNT-G3 (R29 item 2): `vineLG_of_runN` and `finalDec_compN`** for the state after Operations 1--4 (`HRunN`), for the
components WITHOUT tame atoms (A2): the `vineLG` field of `FinalDec` is proved from the run (with the collected objects removed in
Step 1, `HRunNC`), the named `subpro` obligations (`SubproOblG`, S4) and the DV selection rule (`UnselOK`).  `DesRec` is the theorem
`HRunN.desRec`; `NoSGTriangle` is replaced by `NoEligibleTriangle`; the hinge cuts of Steps 1, 3 are along designated pairs
(`HStep1C`, `HStep3C`, model definition).  No conclusion-shaped hypothesis. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {R : ℕ} {M₀ : Molecule V D₀} {hf : HSt V D₀} {Tm : V → Prop}

/-- `HRunN` with the collection data of Operation 1: Step 1 removes the collected objects (L2101). -/
def HRunNC (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (M₀ : Molecule V D₀) (hf : HSt V D₀) (C : CollData M₀)
    (Unsel : Set (Object M₀)) : Prop :=
  ∃ h₁ h₂ h₃ : HSt V D₀,
    Relation.ReflTransGen (HStep1C C L γ η w κ) (HSt.init M₀) h₁ ∧ NoTripleCut C L γ η w κ h₁ ∧
    Relation.ReflTransGen (HStep2C C L γ η w κ) h₁ h₂ ∧ NoEligibleTriangle C L γ η w κ h₂ ∧
    Relation.ReflTransGen (HStep3C C L γ η w κ) h₂ h₃ ∧ NoSGLeft L γ η w κ (HSt.init M₀).s h₃.s ∧
    Relation.ReflTransGen (HStep4 L w κ) h₃ hf ∧ NoBetaCut L w κ hf.s ∧
    (∀ U, ((∃ i, U = C.collection i) ∨ U ∈ C.C2Can L γ η w κ Unsel) → ∀ x : h₁.s.D, ¬ U.ContainsDart (h₁.s.down x))

theorem HRunNC.toHRunN {C : CollData M₀} {Unsel : Set (Object M₀)} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    (h : HRunNC L γ η w κ M₀ hf C Unsel) : HRunN C L γ η w κ (HSt.init M₀) hf := by
  obtain ⟨h₁, h₂, h₃, a1, n1, a2, n2, a3, n3, a4, n4, -⟩ := h
  exact ⟨h₁, h₂, h₃, a1, n1, a2, n2, a3, n3, a4, n4⟩

theorem HRunNC.rem {C : CollData M₀} {Unsel : Set (Object M₀)} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    (h : HRunNC L γ η w κ M₀ hf C Unsel) :
    (∀ i, ∀ x : hf.s.D, ¬ (C.collection i).ContainsDart (hf.s.down x)) ∧
    (∀ U ∈ C.C2Can L γ η w κ Unsel, ∀ x : hf.s.D, ¬ U.ContainsDart (hf.s.down x)) := by
  obtain ⟨h₁, h₂, h₃, a1, n1, a2, n2, a3, n3, a4, n4, hrem⟩ := h
  have s4 : St.Sub hf.s h₃.s := rtg_sub (fun _ _ h => h.sub) a4
  have s3 : St.Sub h₃.s h₂.s := rtg_sub (fun _ _ h => h.toHStep3.sub) a3
  have s2 : St.Sub h₂.s h₁.s := rtg_sub (fun _ _ h => h.toHStep2.sub) a2
  have key : ∀ U, ((∃ i, U = C.collection i) ∨ U ∈ C.C2Can L γ η w κ Unsel) → ∀ x : hf.s.D,
      ¬ U.ContainsDart (hf.s.down x) := by
    intro U hU x hx
    obtain ⟨x', hx'⟩ := (s4.trans (s3.trans s2)) ⟨x, rfl⟩
    exact hrem U hU x' (by rw [hx']; exact hx)
  exact ⟨fun i x => key _ (Or.inl ⟨i, rfl⟩) x, fun U hU x => key U (Or.inr hU) x⟩


/-- The per-decoration run data: collection, selection, obligations of `subpro`, run with designated pairs. -/
def RunDataN (L γ η : ℝ) (M₀ : Molecule V D₀) (hf : HSt V D₀) (AdmRun : (D₀ → (Fin d → ℤ)) → Prop) : Prop :=
  ∀ κ, AdmRun κ → ∃ (C : CollData M₀) (Unsel : Set (Object M₀)), SubproOblG C L γ η (0 : Mom d) κ ∧ TripleDesig C ∧
    C.UnselOK L γ η (0 : Mom d) κ Unsel ∧ HRunNC L γ η (0 : Mom d) κ M₀ hf C Unsel

theorem vineLG_of_runN [Infinite V] (hS : SubHyp R M₀) (AdmRun : (D₀ → (Fin d → ℤ)) → Prop)
    (hrun : RunDataN L γ η M₀ hf AdmRun) (hdeg : ∀ κ, AdmRun κ → DegenSGT M₀ L γ η (0 : Mom d) κ Tm)
    (h0 : ∀ κ, AdmRun κ → ∀ a ∈ M₀.atoms, M₀.deg a = 4 →
      ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0)
    {a₀ : V} (ha₀ : a₀ ∈ hf.s.M.atoms) (hT : TameFree hf Tm a₀) : VineLGAt L γ η hf a₀ AdmRun := by
  intro hvine κ' ⟨κ, hκ, hκ'⟩ x y hxy hout
  subst hκ'
  obtain ⟨C, Unsel, obl, hT3, hU, hrC⟩ := hrun κ hκ
  have hr := hrC.toHRunN
  have hC := hr.prop95At hS obl hT3 (hdeg κ hκ) (h0 κ hκ)
  have hI := hr.invN (InvE.init hS (h0 κ hκ))
  obtain ⟨hdes, hA⟩ := hr.desRec obl
  have hD := hI.rel
  have hrec := hI.hrec
  have hdp := hr.dp
  obtain ⟨hrem1, hrem2⟩ := hrC.rem
  have hxm := (mem_compMol _ _).1 ((compMol hf.s.M a₀).atom_mem x)
  have hx' : hf.s.M.atom x.1 = (compMol hf.s.M a₀).atom x := rfl
  by_cases hε : hf.s.cls (hf.s.M.atom x.1) = .eps
  · exact dec_epsLG (hf := hf) (hC := hC) (a₀ := a₀) hxm.1 hε (hT.of_sc hxm.2) x y rfl (by rw [← hxy]) hout
  · obtain ⟨X, j₁, j₂, hv⟩ := vine_of_vineOrDouble hC ha₀ hvine
    have J := finalJoints_of_vine hC.struct hv ha₀
    have hcomp := J.comp _ hxm.1 hxm.2
    have hy : hf.s.M.atom y.1 = hf.s.M.atom x.1 := by rw [show hf.s.M.atom y.1 = (compMol hf.s.M a₀).atom y from rfl, ← hxy]; rfl
    have hout' : hf.s.M.out x.1 ≠ hf.s.M.out y.1 := hout
    rcases hcomp with h | h | ⟨h, -⟩
    · exact joint_LG2 hS hA hD hC hT hrec hdp obl hU hrem1 hrem2 hdes J hv x.1 y.1 h (hy.trans h) hout'
    · exact joint_LG2 hS hA hD hC hT hrec hdp obl hU hrem1 hrem2 hdes J.symm (isVine_symm hv) x.1 y.1 h (hy.trans h) hout'
    · exact absurd h hε

theorem finalDec_compN [Infinite V] (hS : SubHyp R M₀) (AdmRun : (D₀ → (Fin d → ℤ)) → Prop)
    (hrun : RunDataN L γ η M₀ hf AdmRun) (hdeg : ∀ κ, AdmRun κ → DegenSGT M₀ L γ η (0 : Mom d) κ Tm)
    (h0 : ∀ κ, AdmRun κ → ∀ a ∈ M₀.atoms, M₀.deg a = 4 →
      ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0)
    (hne : ∃ κ, AdmRun κ) (hL : 1 ≤ L) (hη : 0 ≤ η) {a₀ : V} (ha₀ : a₀ ∈ hf.s.M.atoms) (hT : TameFree hf Tm a₀) :
    G8Copy.FinalDec (compMol hf.s.M a₀) (fun a => toCls (hf.s.cls a)) L γ η (compAdm hf a₀ AdmRun) :=
  finalDec_comp_of_vine AdmRun (fun κ hκ => by
      obtain ⟨C, Unsel, obl, hT3, -, hrC⟩ := hrun κ hκ
      exact hrC.toHRunN.prop95At hS obl hT3 (hdeg κ hκ) (h0 κ hκ)) hne hL hη ha₀ hT
    (vineLG_of_runN hS AdmRun hrun hdeg h0 ha₀ hT)

end WaveTurbulence.FinalCountG3
