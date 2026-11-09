/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmP1Rho
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmP1Dev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase2d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3TVineRho
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.InputsProved
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmP1Rho`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY, phase 1 (d): `ρ` and `critCount` under a vine removal.** 

**Low-range change (L6-HASM).** `rho_vine_isVine`: a member of the low family (the porter's binder rule; its doubled
`Src.γL` fixed by hand); the ρ-loss bound comes from H-G3's `someVine_ladderLoss_le_of_agree` (T-vines by N3 Thm 6 (iv))
instead of main's drawn-type `VineRho.vine_ladderLoss_le`. N3 Thm 6 (iv) is proved by L3 (`Ladders.ladders_holds`), so
H-G3's class `Src.G3Inputs` is a global instance (`H.InputsProved`) and the statement is unconditional.-/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The molecule after a vine removal agrees with `M` off the removed object. -/
theorem vineAvoid {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : Step1.VineCut Src.γL M) {a : V}
    (ha : a ∈ M.atoms.filter (fun a => a ∉ K.C.atoms)) :
    a ≠ K.C.upper ∧ a ≠ K.C.lower ∧ a ≠ K.fa ∧ a ≠ K.fb := by
  have := Finset.mem_filter.1 ha
  exact ⟨fun e => this.2 (e ▸ K.a_mem), fun e => this.2 (e ▸ K.b_mem), fun e => K.fa_fresh (e ▸ this.1),
    fun e => K.fb_fresh (e ▸ this.1)⟩

theorem vineTransfer {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : Step1.VineCut Src.γL M) (hdeg : M.deg K.C.upper ≤ 4)
    (hdegl : M.deg K.C.lower ≤ 4) :
    LadderTransfer M K.post (M.atoms.filter (fun a => a ∉ K.C.atoms)) where
  subM a ha := (Finset.mem_filter.1 ha).1
  subM' a ha := by
    have := Finset.mem_filter.1 ha
    show a ∈ (K.cutMol.atoms).filter (fun a => a ∉ K.C.atoms)
    refine Finset.mem_filter.2 ⟨?_, this.2⟩
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem this.1)
  bonds a ha b hb := by
    obtain ⟨hau, hal, haf, haf'⟩ := vineAvoid K ha
    obtain ⟨hbu, hbl, hbf, hbf'⟩ := vineAvoid K hb
    show (restrictP K.cutMol (fun a => a ∉ K.C.atoms) K.closed).bondsBetween a b = M.bondsBetween a b
    rw [restrictP_bondsBetween K.cutMol _ K.closed (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2]
    show ((M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).bondsBetween a b = _
    rw [cut_bondsBetween_eq (M.cut K.C.upper K.fa K.x₁ K.x₂) hal haf' hbl hbf', cut_bondsBetween_eq M hau haf hbu hbf]
  dir a ha b hb := by
    obtain ⟨hau, hal, haf, haf'⟩ := vineAvoid K ha
    obtain ⟨hbu, hbl, hbf, hbf'⟩ := vineAvoid K hb
    show (restrictP K.cutMol (fun a => a ∉ K.C.atoms) K.closed).Directed a b ↔ M.Directed a b
    rw [restrictP_directed K.cutMol _ K.closed (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2]
    show ((M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).Directed a b ↔ _
    rw [cut_directed_iff (M.cut K.C.upper K.fa K.x₁ K.x₂) hal haf' hbl hbf', cut_directed_iff M hau haf hbu hbf]
  low x hx hxA := by
    have hx' := Finset.mem_filter.1 hx
    have hxc : x ∈ K.cutMol.atoms := hx'.1
    have hxM : x ∉ M.atoms := fun h => hxA (Finset.mem_filter.2 ⟨h, hx'.2⟩)
    have hfa : x = K.fa ∨ x = K.fb := by
      rcases Finset.mem_insert.1 hxc with h | h
      · exact Or.inr h
      · rcases Finset.mem_insert.1 h with h | h
        · exact Or.inl h
        · exact absurd h hxM
    show (restrictP K.cutMol (fun a => a ∉ K.C.atoms) K.closed).deg x ≤ 2
    rw [restrictP_deg K.cutMol _ K.closed hx'.2]
    have e1 := cut_deg_v₂ M K.cut_a
    have e2 := cut_deg_v₂ (M.cut K.C.upper K.fa K.x₁ K.x₂) K.cut_b
    have e3 : (M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = M.deg K.C.lower :=
      cut_deg_other K.cut_a K.ab_ne.symm K.fa_ne_b.symm
    rcases hfa with h | h
    · rw [h]
      show ((M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg K.fa ≤ 2
      rw [cut_deg_other K.cut_b (fun e => K.fa_ne_b e) K.fa_ne_fb]
      omega
    · rw [h]
      show ((M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg K.fb ≤ 2
      omega

/-- `ρ` of a vine removal: loss is `ladderLoss M (atoms ∖ C)`. -/
theorem rho_vine_le {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : Step1.VineCut Src.γL M)
    (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) :
    M.rho ≤ K.post.rho + ladderLoss M (M.atoms.filter (fun a => a ∉ K.C.atoms)) :=
  (vineTransfer K (hM _ K.a_atom) (hM _ K.b_atom)).rho_le

/-- Single vine (`IsVine`): `ρ`-loss at most `42` (VINE-RHO). -/
theorem rho_vine_isVine {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : Step1.VineCut Src.γL M) (hMol : M.IsMolecule)
    (hV : Src.IsSomeVine Src.γL M K.C.atoms K.C.upper K.C.lower) :
    M.rho ≤ K.post.rho + 42 := by
  have hM : ∀ x ∈ M.atoms, M.deg x ≤ 4 := fun x hx => Mole.deg_le_four M hMol hx
  have h1 := rho_vine_le K hM
  have h2 := someVine_ladderLoss_le_of_agree M hMol M hMol (VineRho.Agree.refl M K.C.upper K.C.upper) hV
    (fun _ => Or.inl rfl) (fun _ => Or.inl rfl)
  rw [sdiff_eq_filter_atoms] at h2
  omega

/-- A removed object with at most `n` atoms: `ρ`-loss at most `n`. -/
theorem rho_vine_card {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : Step1.VineCut Src.γL M)
    (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) {n : ℕ} (hn : K.C.atoms.card ≤ n) :
    M.rho ≤ K.post.rho + n := by
  have h1 := rho_vine_le K hM
  have h2 := ladderLoss_le_card M hM (M.atoms.filter (fun a => a ∉ K.C.atoms))
  have h3 : (M.atoms \ M.atoms.filter (fun a => a ∉ K.C.atoms)) ⊆ K.C.atoms := by
    intro a ha
    rw [Finset.mem_sdiff, Finset.mem_filter] at ha
    by_contra hc; exact ha.2 ⟨ha.1, hc⟩
  have := Finset.card_le_card h3
  omega

/-- `critCount` drops by at most `2` when the interior atoms of the removed object are not critical. -/
theorem critCount_vineSt (crit : V → Prop) (s : St.{u} V D₀) (K : Step1.VineCut Src.γL s.M) (c : Cls) (hc : c ≠ .eps)
    (hint : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a) :
    critCount crit s ≤ critCount crit (vineSt s K c) + 2 := by
  unfold critCount
  set S := s.M.atoms.filter fun a => s.cls a = .eps ∧ crit a
  have hsub : S \ {K.C.upper, K.C.lower} ⊆
      (vineSt s K c).M.atoms.filter fun a => (vineSt s K c).cls a = .eps ∧ crit a := by
    intro a ha
    obtain ⟨haS, hat⟩ := Finset.mem_sdiff.1 ha
    obtain ⟨ham, hε, hcr⟩ := Finset.mem_filter.1 haS
    have hu : a ≠ K.C.upper := fun e => hat (by simp [e])
    have hl : a ≠ K.C.lower := fun e => hat (by simp [e])
    have haC : a ∉ K.C.atoms := fun h => hint a h hu hl hcr
    refine Finset.mem_filter.2 ⟨?_, ?_, hcr⟩
    · rw [vineSt_atoms, Finset.mem_filter]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ham), haC⟩
    · rw [vineSt_cls_old_AsmP1Basic s K c ham haC]; exact hε
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_sdiff_add_card_inter S {K.C.upper, K.C.lower}
  have h3 : (S ∩ {K.C.upper, K.C.lower}).card ≤ 2 :=
    (Finset.card_le_card Finset.inter_subset_right).trans (Finset.card_le_two)
  omega

end WaveTurbulence.GammaLow.FinalCount.H
