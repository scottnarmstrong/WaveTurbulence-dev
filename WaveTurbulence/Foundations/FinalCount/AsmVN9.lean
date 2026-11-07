/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN8
/-! **FINALCOUNT-ASSEMBLY (VineNodeExists, part 9): `VineNodeExists` from the garden-dependent facts `VHard`.**
`vineNodeExists_of_hard`: given the `SG`-gap of every collected object, its hinge data (`hdesU`: the designated pair of a hinge joint is
the oriented pair of the object) and the garden-dependent fields `VHard` of every vine cut along an intact collected object, a
non-dartless intact collected object that respects the first-stage order gives a vine node of `h` whose class contains `κ`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount


variable {V : Type*} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The hinge data of an object: at a hinge joint the designated pair is a pair of `ContainsDart` darts of opposite directions at it. -/
def HingeData {M₀ : Molecule V D₀} (C : CollData M₀) (U : Object M₀) : Prop :=
  ∀ v ∈ C.hinges, (v = U.upper ∨ v = U.lower) → ∃ f s, C.first v = some f ∧ C.second v = some s ∧ U.ContainsDart f ∧
    U.ContainsDart s ∧ M₀.atom f = v ∧ M₀.atom s = v ∧ M₀.out f ≠ M₀.out s

theorem vineNodeExists_of_hard {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {crit : V → Prop} {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))} (hM₀ : M₀.IsMolecule) (hS : SubHyp Rn M₀) (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ)
    (hη : 0 < η) (h2 : 2 / L ≤ L ^ (-γ + η))
    (hmate : ∀ κ ∈ A0, ∀ x, κ (M₀.mate x) = κ x)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hsgC : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → U.HasGapKind L γ η w κ .SG)
    (hdesC : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → HingeData C U)
    (hard : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1 M₀ Rn C Un Fst L γ η w A0 A h → ∀ κ ∈ A,
      ∀ U : Object M₀, Collected C (Un κ) L γ η w κ U → UIntact U h → ¬ Dartless U h → ∀ K : VineCut h.s.M, K.C.atoms = U.atoms → K.C.upper = U.upper → K.C.lower = U.lower →
        K.fa = fresh3 h 0 → K.fb = fresh3 h 1 → VHard crit h K) :
    VineNodeExists M₀ Rn C Un Fst crit L γ η w A0 := by
  intro A h hinv κ hκ U hU hUint hnd hord
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hL1 : 1 < L := lt_of_lt_of_le (by have := Real.add_one_lt_exp (show (1:ℝ) ≠ 0 by norm_num); linarith) hLe
  have hAe : A ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨κ, hκ⟩
  obtain ⟨hA0, hctx⟩ := hinv
  obtain ⟨hc, -, -⟩ := hctx.resolve_left hAe
  have hκ0 : κ ∈ A0 := hA0 hκ
  have hA := hc.anc
  have hD := hc.rel
  have hdeg : ∀ b ∈ h.s.M.atoms, h.s.M.deg b ≤ 4 := fun b hb => by
    have h1 := hc.good.1.bounds b hb
    have h3 := Mole.outdeg_add_indeg h.s.M b
    omega
  obtain ⟨K, hKat, hKup, hKlo, hKfa, hKfb, hKcd, hKJ, PU, PL, hsgX, htwin⟩ :=
    vineData_of_intact hM₀ hS (hmate κ hκ0) (h0 κ hκ0) h hA hD hdeg U hUint (hsgC κ hκ0 U hU)
  have hHard := hard A h ⟨hA0, hctx⟩ κ hκ U hU hUint hnd K hKat hKup hKlo hKfa hKfb
  have hUup : U.upper ∈ U.atoms := object_mem_of_joint U (Or.inl rfl)
  have hUlo : U.lower ∈ U.atoms := object_mem_of_joint U (Or.inr rfl)
  have hHD := hdesC κ hκ0 U hU
  -- VFacts
  have hdeg3 : ∀ b ∈ U.atoms, 3 ≤ h.s.M.deg b := fun b hb => by
    rw [deg_eq_of_eps hA (hUint b hb).1 (hUint b hb).2]
    exact hS.deg3 b (objectAtoms_sub U hb)
  have hanc : ∀ b ∈ U.atoms, h.anc b = b := fun b hb => hA.eps b (hUint b hb).1 (hUint b hb).2
  have hnl : ∀ x : h.s.D, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x) := fun x e => by
    apply hS.noloop (h.s.down x)
    have e1 := hA.atom x
    have e2 := hA.atom (h.s.M.mate x)
    rw [← hD.mate] at e2
    rw [e1, e2, e]
  have hF : VFacts C crit h K := by
    refine ⟨hKup ▸ (hUint _ hUup).2, hKlo ▸ (hUint _ hUlo).2, hKup ▸ hdeg3 _ hUup, hKlo ▸ hdeg3 _ hUlo, ?_, ?_,
      hHard.hcls, hHard.hconn, hnl, hHard.hrho, hHard.hint⟩
    · intro hmem
      rw [hKup, hanc _ hUup] at hmem ⊢
      obtain ⟨f, s, hf1, hs1, hfc, hsc, haf, has, hout⟩ := hHD _ hmem (Or.inl rfl)
      exact ⟨f, s, hf1, hs1, Or.inl (pair_set_eq U PU (Or.inl rfl) hfc hsc haf has hout)⟩
    · intro hmem
      rw [hKlo, hanc _ hUlo] at hmem ⊢
      obtain ⟨f, s, hf1, hs1, hfc, hsc, haf, has, hout⟩ := hHD _ hmem (Or.inr rfl)
      exact ⟨f, s, hf1, hs1, Or.inl (pair_set_eq U PL (Or.inr rfl) hfc hsc haf has hout)⟩
  -- label
  obtain ⟨R', hR, hsim⟩ := exists_label_of_SG w (κ ∘ h.s.down) K.x₁ K.x₂ hL h2 hsgX
  obtain ⟨z, hRz, hz1, hz2⟩ := label_zrange hLe hηγ hR
  subst hRz
  have hsimy : GapSim L w (κ ∘ h.s.down) K.y₁ K.y₂ ((2 : ℝ) ^ z) := by
    have e : ‖Molecule.gapAt L w (κ ∘ h.s.down) K.y₁ K.y₂‖ = ‖Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂‖ := by
      have := congrArg norm htwin
      simpa [norm_neg, pgap, St.pr, gapAt_comp_down] using this
    unfold GapSim at hsim ⊢
    rw [e]; exact hsim
  have hdet : ∀ K' : VineCut h.s.M, K'.x₁ = K.x₁ → K'.x₂ = K.x₂ → K'.y₁ = K.y₁ → K'.y₂ = K.y₂ → K'.fa = fresh3 h 0 →
      K'.fb = fresh3 h 1 → U.atoms = K'.C.atoms := fun K' e1 e2 e3 e4 e5 e6 =>
    hKat.symm.trans (vineCut_atoms_determined K K' e1.symm e2.symm e3.symm e4.symm (hKfa.trans e5.symm) (hKfb.trans e6.symm))
  have hAv : ∀ (x₁ x₂ y₁ y₂ : h.s.D), x₁ = K.x₁ → x₂ = K.x₂ → y₁ = K.y₁ → y₂ = K.y₂ →
      κ ∈ Avine C Un Fst L γ η w h A x₁ x₂ y₁ y₂ := by
    rintro x₁ x₂ y₁ y₂ rfl rfl rfl rfl
    refine ⟨hκ, U, hU, fun K' e1 e2 e3 e4 e5 e6 => hdet K' e1 e2 e3 e4 e5 e6, hKcd, ?_, hord⟩
    exact Or.inl hKJ
  by_cases hI : IotaHit L η w κ h.alive (h.s.pr K.x₁ K.x₂) ((2 : ℝ) ^ z)
  · obtain ⟨q, hq, ⟨a, ha, vis, hcr⟩, sg, hsgn, h1, h2'⟩ := iotaAlive_of_hit hI
    refine ⟨(K.x₁, K.x₂, K.y₁, K.y₂, z, true, a, decide (sg = 1)), ?_, ?_⟩
    · unfold nodes1
      refine Finset.mem_filter.2 ⟨?_, K, rfl, rfl, rfl, rfl, hKfa, hKfb, hF, hR, ha, fun _ => ⟨q, vis, hcr, hq⟩⟩
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc]
      exact ⟨⟨hz1, hz2⟩, ha, trivial⟩
    · have hq' : qOf h a (h.s.pr K.x₁ K.x₂) = q := by simp [qOf, hcr]
      have hsg' : (if decide (sg = 1) then (1 : ℝ) else -1) = sg := by
        rcases hsgn with rfl | rfl <;> norm_num
      refine ⟨hAv _ _ _ _ rfl rfl rfl rfl, hsgX, hsim, hsimy, Or.inr htwin, fun _ => ?_, fun hb => by simp at hb⟩
      rw [hq', hsg']; exact ⟨h1, h2'⟩
  · have hnot2 : ¬ IotaHit L η w κ (h.s.pr K.x₁ K.x₂ :: h.alive) (h.s.pr K.y₁ K.y₂) ((2 : ℝ) ^ z) := fun hh =>
      hI (iotaHit_first_of_second hL1 hη (zpow_pos (by norm_num) z) (Or.inr htwin)
        (by have := hsim.1; simpa [pgap, St.pr, gapAt_comp_down] using this) hh)
    refine ⟨(K.x₁, K.x₂, K.y₁, K.y₂, z, false, K.C.upper, true), ?_, ?_⟩
    · unfold nodes1
      have hupm : K.C.upper ∈ h.s.M.atoms := hKup ▸ (hUint _ hUup).1
      refine Finset.mem_filter.2 ⟨?_, K, rfl, rfl, rfl, rfl, hKfa, hKfb, hF, hR, hupm, fun hb => by simp at hb⟩
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc]
      exact ⟨⟨hz1, hz2⟩, hupm, trivial⟩
    · exact ⟨hAv _ _ _ _ rfl rfl rfl rfl, hsgX, hsim, hsimy, Or.inr htwin, fun hb => by simp at hb, fun _ => ⟨hI, hnot2⟩⟩

/-- **`HmemAt` from the garden-dependent facts.**  Assembles `hmemAt_of_vineNodes` (triple case + coverage by exhaustion) with
`vineNodeExists_of_hard` (vine case).  The inputs are class-level: `hdisj` (collected objects have the same designation or disjoint
atoms: `desDisj_of_parts`), `hFst`, `hsgC`, `hdesC` and `hard` (`VHard` of the vine cuts along intact collected objects). -/
theorem hmemAt_of_hard {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {crit : V → Prop} {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))} (hM₀ : M₀.IsMolecule) (hS : SubHyp Rn M₀) (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ)
    (hη : 0 < η) (h2 : 2 / L ≤ L ^ (-γ + η))
    (hmate : ∀ κ ∈ A0, ∀ x, κ (M₀.mate x) = κ x)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Object M₀, Collected C (Un κ) L γ η w κ U → Collected C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hFst : ∀ κ ∈ A0, ∀ U ∈ Fst, Collected C (Un κ) L γ η w κ U)
    (hsgC : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → U.HasGapKind L γ η w κ .SG)
    (hdesC : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → HingeData C U)
    (hard : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1 M₀ Rn C Un Fst L γ η w A0 A h → ∀ κ ∈ A,
      ∀ U : Object M₀, Collected C (Un κ) L γ η w κ U → UIntact U h → ¬ Dartless U h → ∀ K : VineCut h.s.M, K.C.atoms = U.atoms → K.C.upper = U.upper → K.C.lower = U.lower →
        K.fa = fresh3 h 0 → K.fb = fresh3 h 1 → VHard crit h K) :
    HmemAt M₀ Rn C L γ η w A0 Un Fst crit :=
  hmemAt_of_vineNodes hS hLe hηγ h2 (fun κ hκ => h0 κ hκ) hdisj hFst
    (vineNodeExists_of_hard hM₀ hS hLe hηγ hη h2 hmate h0 hsgC hdesC hard)

end WaveTurbulence.FinalCountAsm
