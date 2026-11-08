/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKChain.Reach
public import WaveTurbulence.Foundations.FinalCount.GV14

/-! # C1b2 MK-CHAIN (7): `no_SGL` with survivors (terminal step, C0's sweep)

Copy-thread of main's GV10 (`no_SGL`) and GV13 (`joint_LGL`, `joint_LG2L`), and of G3VineLG1's `CollData.cover`,
`CollData.coverCan` on the forbidden pool (`coverF`, `coverCanF`). A final vine component `P` of the run is not SG:
- `P` inside a `𝒞₁` object or inside a survivor: a dart of it survives, but those objects are dartless (`HRunLCE.rem`);
- `P` meets a survivor joint: `SubproOblGMK.meetB` (inside a survivor; sharing a dart with a survivor, which is
  dartless; or the hinge case);
- `P` misses the joints and meets a hinge: `crossing` (the hinge case, main's argument);
- otherwise `contained` gives `HostE`, whose container avoids every survivor, so `P` is in the forbidden pool `InPF`
  (C0's math check (1), R164) and main's maximality/`UnselOK` argument runs on `C2CanF`/`UnselOKF`. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.Flower.FinalMKChain
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section cover
variable {M₀ : Molecule V D₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

/-- **Cover on the forbidden pool** (main's `CollData.cover`). -/
theorem coverF_MK (C : CollDataMK M₀) (Unsel : Set (Object M₀)) {P : Object M₀}
    (hP : C.InPF L γ η w κ P) : P ∈ Unsel ∨ ∃ U ∈ C.C2OfF L γ η w κ Unsel, P.atoms ⊆ U.atoms := by
  by_cases hU : P ∈ Unsel
  · exact Or.inl hU
  right
  let T : Set (Object M₀) := {Q | (C.InPF L γ η w κ Q ∧ Q ∉ Unsel) ∧ P.atoms ⊆ Q.atoms}
  have hTne : P ∈ T := ⟨⟨hP, hU⟩, Finset.Subset.refl _⟩
  obtain ⟨U, hUT, hmax⟩ : ∃ U ∈ T, ∀ Q ∈ T, Q.atoms.card ≤ U.atoms.card := by
    by_contra hcon
    push Not at hcon
    have key : ∀ n : ℕ, ∃ Q ∈ T, n ≤ Q.atoms.card := by
      intro n
      induction n with
      | zero => exact ⟨P, hTne, Nat.zero_le _⟩
      | succ n ih =>
        obtain ⟨Q, hQ, hn⟩ := ih
        obtain ⟨Q', hQ', hlt⟩ := hcon Q hQ
        exact ⟨Q', hQ', by omega⟩
    obtain ⟨Q, hQ, hn⟩ := key (M₀.atoms.card + 1)
    have := Finset.card_le_card (objectAtoms_sub Q)
    omega
  refine ⟨U, ⟨hUT.1, fun Q hQ hUQ => ?_⟩, hUT.2⟩
  have hQT : Q ∈ T := ⟨hQ, hUT.2.trans hUQ⟩
  have heq : U.atoms = Q.atoms := Finset.eq_of_subset_of_card_le hUQ (hmax Q hQT)
  exact heq.symm.subset

/-- **Cover on the forbidden pool, canonical form** (main's `CollData.coverCan`). -/
theorem coverCanF_MK (C : CollDataMK M₀) (Unsel : Set (Object M₀)) {P : Object M₀}
    (hP : C.InPF L γ η w κ P) : P ∈ Unsel ∨ ∃ U ∈ C.C2CanF L γ η w κ Unsel, P.atoms ⊆ U.atoms := by
  rcases coverF_MK C Unsel hP with h | ⟨U, hU, hsub⟩
  · exact Or.inl h
  right
  by_cases hh : ∃ R, U.shape = .hyper R
  · let S : Set ℕ := {n | ∃ Q ∈ C.C2OfF L γ η w κ Unsel, Q.atoms = U.atoms ∧ (∃ R, Q.shape = .hyper R) ∧
      Q.hyperRankG = n}
    have hne : ∃ n, n ∈ S := ⟨_, U, hU, rfl, hh, rfl⟩
    obtain ⟨Q, hQ, hQat, hQh, hQn⟩ := Nat.find_spec hne
    refine ⟨Q, ⟨hQ, fun Q' hQ' hat _ hQ'h => ?_⟩, hQat ▸ hsub⟩
    have := Nat.find_min' hne (show Q'.hyperRankG ∈ S from ⟨Q', hQ', hat.trans hQat, hQ'h, rfl⟩)
    rw [hQn]; exact this
  · exact ⟨U, ⟨hU, fun _ _ _ h => absurd h hh⟩, hsub⟩

/-- `HostE` (containers avoiding the hinges, the survivor joints, `𝒞₁` and the survivors) gives `HostF` for
`forb = survAtomsM E`, and the object avoids `forb`. -/
theorem hostF_of_hostE {m : ℕ} {C : CollDataMK M₀} {E : Fin m → Object M₀} (hforb : C.forb = survAtomsM E)
    {P : Object M₀} (hH : HostE C.toCollData E L γ η w κ P) :
    C.HostF L γ η w κ P ∧ Disjoint P.atoms C.forb := by
  have key : ∀ S : Finset V, P.atoms ⊆ S → (∀ i, Disjoint S (E i).atoms) → Disjoint S C.forb ∧ Disjoint P.atoms C.forb := by
    intro S hPS hSE
    have h1 : Disjoint S C.forb := by
      rw [hforb, survAtomsM, Finset.disjoint_biUnion_right]
      exact fun i _ => hSE i
    exact ⟨h1, Finset.disjoint_of_subset_left hPS h1⟩
  rcases hH with ⟨S, a, b, hDV, hPS, hSB, hSC, hSE⟩ | ⟨Q, hPQ, hkind, hQB, hQC, hQE⟩
  · obtain ⟨h1, h2⟩ := key S hPS hSE
    refine ⟨Or.inl ⟨S, a, b, hDV, hPS, ?_, hSC⟩, h2⟩
    rw [Finset.disjoint_union_right] at hSB ⊢
    exact ⟨hSB.1, h1⟩
  · obtain ⟨h1, h2⟩ := key Q.atoms hPQ hQE
    refine ⟨Or.inr ⟨Q, hPQ, hkind, ?_, hQC⟩, h2⟩
    rw [Finset.disjoint_union_right] at hQB ⊢
    exact ⟨hQB.1, h1⟩

end cover

section nosgl
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R R₀ : ℕ} {Tm : V → Prop}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀} {a₀ j₁ j₂ : V}

/-- **The hinge case of `no_SGL`** (main's `no_SGL`, the `crossing` branch): a final vine component meeting a hinge
inside, or at a joint where its darts split the designated pair, is not SG. -/
theorem no_SGL_hinge (hS : SubHypL R₀ M₀) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hC : Prop95ConclAtL L γ η w κ R hf Tm) (hT : TameFree hf Tm a₀) (hrec : HInv L γ η w κ hf) (hdp : DPInv hf)
    {C : CollData M₀} (hH : HingeSG C L γ η w κ) (hdes : DesRecN C hf) (J : FinalJoints hf a₀ j₁ j₂)
    (P : Object M₀) (hPat : P.atoms = AncGroup hf a₀) (hPup : P.upper = hf.anc j₁) (hPlo : P.lower = hf.anc j₂)
    (hPa : ∀ x : hf.s.D, hf.s.M.SameComponent a₀ (hf.s.M.atom x) → P.ContainsDart (hf.s.down x))
    (hPb : ∀ z, P.ContainsDart z → ∃ x : hf.s.D, hf.s.M.SameComponent a₀ (hf.s.M.atom x) ∧ hf.s.down x = z)
    (hcr : ∃ v ∈ C.hinges, v ∈ P.atoms ∧ ((v ≠ P.upper ∧ v ≠ P.lower) ∨
      ((v = P.upper ∨ v = P.lower) ∧
        HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))) : False := by
  obtain ⟨v, hvH, hvP, hcase⟩ := hcr
  obtain ⟨f0, s0, hf0, hs0, hsg0⟩ := hH v hvH
  rcases hcase with ⟨h1, h2⟩ | ⟨hjoint, x, y, hx, hy, hxor⟩
  · exact hinge_interiorL hA hD hC hT J (hPat ▸ hvP) (hPup ▸ h1) (hPlo ▸ h2) hsg0.1 hsg0.2
  · have hfx : f0 = x := Option.some.inj (hf0.symm.trans hx)
    have hsy : s0 = y := Option.some.inj (hs0.symm.trans hy)
    subst hfx hsy
    obtain ⟨j, hjc, hjv⟩ : ∃ j, (j = j₁ ∨ j = j₂) ∧ v = hf.anc j := by
      rcases hjoint with h | h
      · exact ⟨j₁, Or.inl rfl, by rw [← hPup, h]⟩
      · exact ⟨j₂, Or.inr rfl, by rw [← hPlo, h]⟩
    have hjm : j ∈ hf.s.M.atoms := by rcases hjc with rfl | rfl; exacts [J.m1, J.m2]
    have hjd : hf.s.M.deg j = 2 := by rcases hjc with rfl | rfl; exacts [J.d1, J.d2]
    obtain ⟨p, vis, hr⟩ := record_of_nonEpsL hrec hC hjm (by rcases hjc with rfl | rfl; exacts [J.n1, J.n2])
    have hdpj := hdp.ok j hjm p vis hr
    obtain ⟨f, s, hf1, hs1, hset⟩ := hdes j p vis hr (hjv ▸ hvH)
    rw [← hjv] at hf1 hs1
    have hff : f = f0 := Option.some.inj (hf1.symm.trans hf0)
    have hss : s = s0 := Option.some.inj (hs1.symm.trans hs0)
    subst hff hss
    exact hinge_joint_xorL hA hD hS J hPa hPb hjc hdpj hset (fun e => hsg0.1.2.2.2 (by rw [e])) hjd
      (hjv ▸ hsg0.1.1) (hjv ▸ hsg0.1.2.1) hxor

/-- **`no_SGL` with survivors** (main's `no_SGL`, GV10): a final vine component of the survivor run is not SG. -/
theorem no_SGLE (hS : SubHypL R₀ M₀) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hC : Prop95ConclAtL L γ η w κ R hf Tm) (hT : TameFree hf Tm a₀) (hrec : HInv L γ η w κ hf) (hdp : DPInv hf)
    {m : ℕ} {C : CollDataMK M₀} {E : Fin m → Object M₀} {Unsel : Set (Object M₀)}
    (obl : SubproOblGMK C.toCollData E L γ η w κ) (hU : C.UnselOKF L γ η w κ Unsel) (hforb : C.forb = survAtomsM E)
    (hrem : ∀ U, CollectedF C Unsel L γ η w κ U → ∀ x : hf.s.D, ¬ U.ContainsDart (hf.s.down x))
    (hremE : ∀ i, ∀ x : hf.s.D, ¬ (E i).ContainsDart (hf.s.down x))
    (hdes : DesRecN C.toCollData hf) (J : FinalJoints hf a₀ j₁ j₂)
    (P : Object M₀) (hPat : P.atoms = AncGroup hf a₀) (hPup : P.upper = hf.anc j₁) (hPlo : P.lower = hf.anc j₂)
    (hPa : ∀ x : hf.s.D, hf.s.M.SameComponent a₀ (hf.s.M.atom x) → P.ContainsDart (hf.s.down x))
    (hPb : ∀ z, P.ContainsDart z → ∃ x : hf.s.D, hf.s.M.SameComponent a₀ (hf.s.M.atom x) ∧ hf.s.down x = z) :
    ¬ P.HasGapKind L γ η w κ .SG := by
  intro hSG
  have hnl := hC.noloop
  have hHc := no_SGL_hinge hS hA hD hC hT hrec hdp (SubproOblGMK.hingeSGP obl) hdes J P hPat hPup hPlo hPa hPb
  by_cases hOut : C.toCollData.Outside P
  swap
  · obtain ⟨i, hi⟩ : ∃ i, P.atoms ⊆ (C.collection i).atoms := by
      by_contra h'; push Not at h'; exact hOut h'
    obtain ⟨x, hx⟩ := final_dart_contained J hA hD hnl (C.collection i) (hPat ▸ hi)
    exact hrem _ (Or.inl ⟨i, rfl⟩) x hx
  by_cases hin : ∃ i, P.atoms ⊆ (E i).atoms
  · obtain ⟨i, hi⟩ := hin
    obtain ⟨x, hx⟩ := final_dart_contained J hA hD hnl (E i) (hPat ▸ hi)
    exact hremE i x hx
  have hin' : ∀ i, ¬ P.atoms ⊆ (E i).atoms := fun i hi => hin ⟨i, hi⟩
  by_cases hB : Disjoint P.atoms (survJointsM E)
  swap
  · rcases obl.meetB P hSG hB with ⟨i, hi⟩ | ⟨i, x, hPx, hEx⟩ | hcr
    · exact hin' i hi
    · obtain ⟨x', -, rfl⟩ := hPb x hPx
      exact hremE i x' hEx
    · exact hHc hcr
  by_cases hdis : Disjoint P.atoms C.hinges
  · have hdisB : Disjoint P.atoms (C.hinges ∪ survJointsM E) := Finset.disjoint_union_right.2 ⟨hdis, hB⟩
    obtain ⟨hHF, hforbP⟩ := hostF_of_hostE hforb (obl.contained P hSG hOut hin' hdisB)
    have hInP : C.InPF L γ η w κ P := ⟨hSG, hOut, Finset.disjoint_union_right.2 ⟨hdis, hforbP⟩, hHF⟩
    rcases coverCanF_MK C Unsel hInP with hmem | ⟨U, hUC, hsub⟩
    · rcases (hU.dv P hmem).2 with ⟨U, hU2, hsub⟩ | ⟨A, a, b, hVA, hVB, hAB, U, hU2, hUA, hvc⟩
      · obtain ⟨x, hx⟩ := final_dart_contained J hA hD hnl U (hPat ▸ hsub)
        exact hrem U (Or.inr hU2) x hx
      · exact residual_unselL hS J hA hD hnl P.atoms hPat A a b hVA hVB hAB U hUA hvc (hrem U (Or.inr hU2))
    · obtain ⟨x, hx⟩ := final_dart_contained J hA hD hnl U (hPat ▸ hsub)
      exact hrem U (Or.inr hUC) x hx
  · exact hHc (obl.crossing P hSG hOut hin' hB hdis)

/-- **The gap at a joint of a final vine component is LG, with survivors** (main's `joint_LGL`, GV13). -/
theorem joint_LGLE (hS : SubHypL R₀ M₀) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hC : Prop95ConclAtL L γ η w κ R hf Tm) (hT : TameFree hf Tm a₀) (hrec : HInv L γ η w κ hf) (hdp : DPInv hf)
    {m : ℕ} {C : CollDataMK M₀} {E : Fin m → Object M₀} {Unsel : Set (Object M₀)}
    (obl : SubproOblGMK C.toCollData E L γ η w κ) (hU : C.UnselOKF L γ η w κ Unsel) (hforb : C.forb = survAtomsM E)
    (hrem : ∀ U, CollectedF C Unsel L γ η w κ U → ∀ x : hf.s.D, ¬ U.ContainsDart (hf.s.down x))
    (hremE : ∀ i, ∀ x : hf.s.D, ¬ (E i).ContainsDart (hf.s.down x))
    (hdes : DesRecN C.toCollData hf) (J : FinalJoints hf a₀ j₁ j₂) {X : VineType}
    (hv : (compMol hf.s.M a₀).IsVine X (compMol hf.s.M a₀).atoms j₁ j₂) (x y : hf.s.D)
    (hx : hf.s.M.atom x = j₁) (hy : hf.s.M.atom y = j₁) (hox : hf.s.M.out x = false) (hoy : hf.s.M.out y = true) :
    L ^ (-γ + η) < ‖Molecule.kvec L w (κ ∘ hf.s.down) x - Molecule.kvec L w (κ ∘ hf.s.down) y‖ := by
  obtain ⟨P, hPat, hPup, hPlo, hgap, hPa, hPb⟩ := final_vine_object'L J hA hD hS hv
  obtain ⟨r, hr, hre⟩ := hgap L w κ x y hx hy hox hoy
  have hno := no_SGLE hS hA hD hC hT hrec hdp obl hU hforb hrem hremE hdes J P hPat hPup hPlo hPa hPb
  have hnSG : Molecule.gapKind L γ η r ≠ .SG := fun h => hno ⟨r, hr, h⟩
  have hne : hf.s.cls j₁ ≠ .eps := J.n1
  obtain ⟨g, hg, hgg⟩ := hC.dartGap j₁ J.m1 hne x y hx hy hox hoy
  have hg0 := nonEps_gap_ne_zeroL hrec hC J.m1 J.n1 hg
  have hxy0 : Molecule.gapAt L w (κ ∘ hf.s.down) x y ≠ 0 := by
    rcases hgg with h | h
    · rw [h]; exact hg0
    · rw [h]; exact neg_ne_zero.2 hg0
  have hr0 : r ≠ 0 := by
    rw [hre]
    have : Molecule.gapAt L w (κ ∘ hf.s.down) y x = -Molecule.gapAt L w (κ ∘ hf.s.down) x y := by
      unfold Molecule.gapAt; abel
    rw [this]; exact neg_ne_zero.2 hxy0
  have hlt := lt_norm_of_LGL (kind_LG_of hr0 hnSG)
  rw [hre] at hlt
  unfold Molecule.gapAt at hlt
  rwa [norm_sub_rev] at hlt

/-- Main's `joint_LG2L` (GV13) with survivors. -/
theorem joint_LG2LE (hS : SubHypL R₀ M₀) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hC : Prop95ConclAtL L γ η w κ R hf Tm) (hT : TameFree hf Tm a₀) (hrec : HInv L γ η w κ hf) (hdp : DPInv hf)
    {m : ℕ} {C : CollDataMK M₀} {E : Fin m → Object M₀} {Unsel : Set (Object M₀)}
    (obl : SubproOblGMK C.toCollData E L γ η w κ) (hU : C.UnselOKF L γ η w κ Unsel) (hforb : C.forb = survAtomsM E)
    (hrem : ∀ U, CollectedF C Unsel L γ η w κ U → ∀ x : hf.s.D, ¬ U.ContainsDart (hf.s.down x))
    (hremE : ∀ i, ∀ x : hf.s.D, ¬ (E i).ContainsDart (hf.s.down x))
    (hdes : DesRecN C.toCollData hf) (J : FinalJoints hf a₀ j₁ j₂) {X : VineType}
    (hv : (compMol hf.s.M a₀).IsVine X (compMol hf.s.M a₀).atoms j₁ j₂) (x y : hf.s.D)
    (hx : hf.s.M.atom x = j₁) (hy : hf.s.M.atom y = j₁) (hxy : hf.s.M.out x ≠ hf.s.M.out y) :
    L ^ (-γ + η) < ‖Molecule.kvec L w (κ ∘ hf.s.down) x - Molecule.kvec L w (κ ∘ hf.s.down) y‖ := by
  cases hox : hf.s.M.out x
  · have hoy : hf.s.M.out y = true := by
      cases h : hf.s.M.out y
      · exact absurd (hox.trans h.symm) hxy
      · rfl
    exact joint_LGLE hS hA hD hC hT hrec hdp obl hU hforb hrem hremE hdes J hv x y hx hy hox hoy
  · have hoy : hf.s.M.out y = false := by
      cases h : hf.s.M.out y
      · rfl
      · exact absurd (hox.trans h.symm) hxy
    rw [norm_sub_rev]
    exact joint_LGLE hS hA hD hC hT hrec hdp obl hU hforb hrem hremE hdes J hv y x hy hx hoy hox

end nosgl

end WaveTurbulence.Flower.FinalMKChain
