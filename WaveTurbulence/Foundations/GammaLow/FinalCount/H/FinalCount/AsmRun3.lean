/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmRun3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmRun3`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY, M7 (phase 3): existence of the SG-cut phase.**  From a state satisfying `InvE` and `AncRel`, the
phase-3 steps `HStep3C` (cuts of `ε` SG atoms along an SG pair, at a hinge along the designated pair) can be run until `NoSGLeft`.
Fresh atom names exist since `V` is infinite; labels by `exists_label_of_SG`; `kp` is decided by `IotaHit`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {M₀ : Molecule V D₀} {R : ℕ}

theorem epsCount_step3C {C : CollData M₀} {h h' : HSt V D₀} (hs : HStep3C C L γ η w κ h h') :
    epsCount h'.s < epsCount h.s := by
  cases hs with
  | cut v v₂ x₁ x₂ hc R' kp hR hkp hε hsg hsim hι h3 hdes =>
    have hab : (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then Cls.alpha R' kp else Cls.beta) ≠ Cls.eps := by
      split_ifs <;> simp
    exact epsCount_cutSt_lt h.s hc hε _ _ hab hab

/-- The oriented designated pair of a hinge. -/
theorem hinge_oriented {C : CollData M₀} (obl : SubproOblG C L γ η w κ) {v : V} (hv : v ∈ C.hinges) :
    ∃ f s x y : D₀, C.first v = some f ∧ C.second v = some s ∧ M₀.atom x = v ∧ M₀.atom y = v ∧
      y ≠ M₀.mate x ∧ M₀.out x = false ∧ M₀.out y = true ∧
      Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .SG ∧ ({x, y} : Set D₀) = {f, s} := by
  obtain ⟨f, s, h1, h2, ⟨hf, hs, hfs, hout⟩, hsg⟩ := obl.hingeSG v hv
  cases hof : M₀.out f
  · have hos : M₀.out s = true := by
      cases h : M₀.out s
      · exact absurd (hof.trans h.symm) hout
      · rfl
    exact ⟨f, s, f, s, h1, h2, hf, hs, hfs, hof, hos, hsg, rfl⟩
  · have hos : M₀.out s = false := by
      cases h : M₀.out s
      · rfl
      · exact absurd (hof.trans h.symm) hout
    refine ⟨f, s, s, f, h1, h2, hs, hf, ?_, hos, hof, ?_, Set.pair_comm _ _⟩
    · intro e; apply hfs; rw [e, M₀.mate_mate]
    have hsw : Molecule.gapAt L w κ s f = -Molecule.gapAt L w κ f s := by
      unfold Molecule.gapAt; abel
    rw [hsw, gapKind_eq_of_norm_eq (L := L) (γ := γ) (η := η) (norm_neg (Molecule.gapAt L w κ f s))]
    exact hsg

/-- **Step-3 existence**: an `ε` atom that is SG in `M_sub` has a step `HStep3C` (given a fresh name). -/
theorem exists_step3C [Infinite V] {C : CollData M₀} (obl : SubproOblG C L γ η w κ) (hL : 0 < L)
    (h2 : 2 / L ≤ L ^ (-γ + η)) {h : HSt V D₀} (hI : InvE M₀ R 0 L γ η w κ h) (hA : AncRel M₀ h.s h.anc)
    {v : V} (hv : v ∈ h.s.M.atoms) (hε : h.s.cls v = .eps) (hSG : SGat M₀ L γ η w κ v) :
    ∃ h', HStep3C C L γ η w κ h h' := by
  have hD : DartRel M₀ h.s := hI.rel
  have h3 : 3 ≤ h.s.M.deg v := deg_eps_ge_three (hI.flat rfl) hv hε
  have hanc : h.anc v = v := hA.eps v hv hε
  obtain ⟨v₂, hv₂⟩ := Infinite.exists_notMem_finset h.s.M.atoms
  -- the pair of darts
  obtain ⟨x, y, hxv, hyv, hne, hxo, hyo, hsgxy, hdes⟩ : ∃ x y : D₀, M₀.atom x = v ∧ M₀.atom y = v ∧ y ≠ M₀.mate x ∧
      M₀.out x = false ∧ M₀.out y = true ∧ Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .SG ∧
      (v ∈ C.hinges → ∃ f s, C.first v = some f ∧ C.second v = some s ∧ ({x, y} : Set D₀) = {f, s}) := by
    by_cases hh : v ∈ C.hinges
    · obtain ⟨f, s, x, y, h1, h2, hx, hy, hne, ho1, ho2, hsg, hset⟩ := hinge_oriented obl hh
      exact ⟨x, y, hx, hy, hne, ho1, ho2, hsg, fun _ => ⟨f, s, h1, h2, hset⟩⟩
    · obtain ⟨x, y, hx, hy, ho1, ho2, hne, hsg⟩ := hSG
      exact ⟨x, y, hx, hy, hne, ho1, ho2, hsg, fun h' => absurd h' hh⟩
  obtain ⟨x₁, hx₁d, hx₁a, hx₁o⟩ := eps_lift hA hD hv hε hxv
  obtain ⟨x₂, hx₂d, hx₂a, hx₂o⟩ := eps_lift hA hD hv hε hyv
  have hne' : x₂ ≠ h.s.M.mate x₁ := by
    intro e
    apply hne
    rw [← hx₂d, e, ← hD.mate, hx₁d]
  have hc : h.s.M.IsCutData v v₂ x₁ x₂ := ⟨hv, hv₂, hx₁a, hx₂a, hne', by simp [hx₁o, hxo], by simp [hx₂o, hyo]⟩
  have hsg' : Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) x₁ x₂) = .SG := by
    have : Molecule.gapAt L w (κ ∘ h.s.down) x₁ x₂ = Molecule.gapAt L w κ x y := by
      unfold Molecule.gapAt Molecule.kvec; simp [hx₁d, hx₂d]
    rw [this]; exact hsgxy
  obtain ⟨R', hR', hsim⟩ := exists_label_of_SG w (κ ∘ h.s.down) x₁ x₂ hL h2 hsg'
  by_cases hIo : IotaHit L η w κ h.alive (h.s.pr x₁ x₂) R'
  · refine ⟨_, HStep3C.cut h v v₂ x₁ x₂ hc R' 50 hR' (Or.inr rfl) hε hsg' hsim (by simp [hIo]) h3 ?_⟩
    intro hh
    rw [hanc] at hh
    obtain ⟨f, s, h1, h2', hset⟩ := hdes hh
    rw [hanc]
    refine ⟨f, s, h1, h2', Or.inl ?_⟩
    simpa [St.pr, hx₁d, hx₂d] using hset
  · refine ⟨_, HStep3C.cut h v v₂ x₁ x₂ hc R' 0 hR' (Or.inl rfl) hε hsg' hsim (by simp [hIo]) h3 ?_⟩
    intro hh
    rw [hanc] at hh
    obtain ⟨f, s, h1, h2', hset⟩ := hdes hh
    rw [hanc]
    refine ⟨f, s, h1, h2', Or.inl ?_⟩
    simpa [St.pr, hx₁d, hx₂d] using hset

/-- **Phase 3 exists.** -/
theorem exists_phase3 [Infinite V] {C : CollData M₀} (obl : SubproOblG C L γ η w κ) (hL : 0 < L)
    (h2 : 2 / L ≤ L ^ (-γ + η)) (h₂ : HSt V D₀) (hI : InvE M₀ R 0 L γ η w κ h₂) (hA : AncRel M₀ h₂.s h₂.anc) :
    ∃ h₃ : HSt V D₀, Relation.ReflTransGen (HStep3C C L γ η w κ) h₂ h₃ ∧ InvE M₀ R 0 L γ η w κ h₃ ∧
      AncRel M₀ h₃.s h₃.anc ∧ NoSGLeft L γ η w κ (HSt.init M₀).s h₃.s := by
  obtain ⟨h₃, hr, hP, hstuck⟩ := exists_stuck_inv (HStep3C C L γ η w κ) (fun h => epsCount h.s)
    (fun h => InvE M₀ R 0 L γ η w κ h ∧ AncRel M₀ h.s h.anc) (fun _ _ hs => epsCount_step3C hs)
    (fun _ _ hs hp => ⟨hp.1.step3 hs.toHStep3, hs.toHStep3.anc hp.2⟩) h₂ ⟨hI, hA⟩
  refine ⟨h₃, hr, hP.1, hP.2, ?_⟩
  intro v hv hε hSG
  obtain ⟨h', hs'⟩ := exists_step3C obl hL h2 hP.1 hP.2 hv hε hSG
  exact hstuck _ hs'

end WaveTurbulence.GammaLow.FinalCount.H
