/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain22
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmHmem
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain21
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain22`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, session 4 (4): `HmemAtL`** (coverage of the LOW Step 1 by the vine, triple and D1 node families).
The D1 node of an intact collected object with a joint of state degree `2` has `VFactsD1.hconn` from `HostConn` (`hconn0_of_hostConnL`):
the pendant double-shape case is excluded (R71). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

variable {V : Type*} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem vinePostG_atoms_eq {h : HSt V D₀} {K K' : Step1.VineCut Src.γL h.s.M} (he : h.vinePostGL K = h.vinePostGL K') : K'.C.atoms = K.C.atoms := by
  have h1 := congrArg (fun x : HSt V D₀ => x.s.M.atoms) he
  simp only [HSt.vinePostGL, FinalCountG3.HSt.vinePostGL, vineStG_atoms] at h1
  have hsub := (object_oh K.C).basic.1
  have hsub' := (object_oh K'.C).basic.1
  ext v
  by_cases hv : v ∈ h.s.M.atoms
  · have hfa : v ≠ K.fa := fun e => K.cut_a.2.1 (e ▸ hv)
    have hfb : v ≠ K.fb := fun e => K.cut_b.2.1 (by simp [e] at hv ⊢; exact Finset.mem_insert_of_mem (e ▸ hv))
    have hfa' : v ≠ K'.fa := fun e => K'.cut_a.2.1 (e ▸ hv)
    have hfb' : v ≠ K'.fb := fun e => K'.cut_b.2.1 (by simp [e] at hv ⊢; exact Finset.mem_insert_of_mem (e ▸ hv))
    have := Finset.ext_iff.mp h1 v
    simp only [Finset.mem_filter, Finset.mem_insert, hfa, hfb, hfa', hfb', false_or, hv, true_and, VineKeep,
      false_and, not_false_eq_true, and_true] at this
    exact (not_iff_not.mp this).symm
  · exact ⟨fun h' => absurd (hsub' h') hv, fun h' => absurd (hsub h') hv⟩

/-- **Cut data of an intact object.** -/
theorem vineDataL_of_intact [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} (hM₀ : M₀.IsMolecule) (hS : SubHypL Rn M₀) {L γ η : ℝ} {w : Mom d}
    {κ : D₀ → (Fin d → ℤ)} (hmate : ∀ x, κ (M₀.mate x) = κ x)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h : HSt V D₀) (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s) (hdeg : ∀ b ∈ h.s.M.atoms, h.s.M.deg b ≤ 4)
    (U : Src.Object Src.γL M₀) (hint : UIntact U h) (hsg : U.HasGapKind L γ η w κ .SG) :
    ∃ K : Step1.VineCut Src.γL h.s.M, K.C.atoms = U.atoms ∧ K.C.upper = U.upper ∧ K.C.lower = U.lower ∧ K.fa = fresh3 h 0 ∧
      K.fb = fresh3 h 1 ∧
      (U.ContainsDart (h.s.down K.x₁) ∧ U.ContainsDart (h.s.down K.x₂) ∧ U.ContainsDart (h.s.down K.y₁) ∧
        U.ContainsDart (h.s.down K.y₂)) ∧
      (M₀.atom (h.s.down K.x₁) = U.upper ∧ M₀.atom (h.s.down K.y₁) = U.lower) ∧
      SourceObjectJointPair U U.upper (h.s.down K.x₂) (h.s.down K.x₁) ∧
      SourceObjectJointPair U U.lower (h.s.down K.y₂) (h.s.down K.y₁) ∧
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂) = .SG ∧
      pgap L w κ (h.s.pr K.y₁ K.y₂) = -pgap L w κ (h.s.pr K.x₁ K.x₂) := by
  have hnl : ∀ x : h.s.D, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x) := by
    intro x e
    apply hS.noloop (h.s.down x)
    have e1 := hA.atom x
    have e2 := hA.atom (h.s.M.mate x)
    rw [← hD.mate] at e2
    rw [e1, e2, e]
  obtain ⟨hf0, hf1⟩ := fresh3_spec h
  have hfab : fresh3 h 0 ≠ fresh3 h 1 := fun e => by have := hf0 e; simp at this
  obtain ⟨Ũ, hatoms, hup, hlo, hcd, -⟩ := stateObj_spec hA hD U hint
  obtain ⟨K, hKC, hKfa, hKfb⟩ := exists_vineCut_of_object Ũ hdeg hnl (fresh3 h 0) (fresh3 h 1) (hf1 0) (hf1 1) hfab
  have hUup : U.upper ∈ U.atoms := object_mem_of_joint U (Or.inl rfl)
  have hUlo : U.lower ∈ U.atoms := object_mem_of_joint U (Or.inr rfl)
  have hKup : K.C.upper = U.upper := by rw [hKC]; exact hup
  have hKlo : K.C.lower = U.lower := by rw [hKC]; exact hlo
  have hCD : ∀ z, K.C.ContainsDart z ↔ U.ContainsDart (h.s.down z) := fun z => by rw [hKC]; exact hcd z
  have hMx₁ : M₀.atom (h.s.down K.x₁) = U.upper := by
    rw [hA.atom, K.Mx₁, hKup]; exact hA.eps _ (hint _ hUup).1 (hint _ hUup).2
  have hMx₂ : M₀.atom (h.s.down K.x₂) = U.upper := by
    rw [hA.atom, K.Mx₂, hKup]; exact hA.eps _ (hint _ hUup).1 (hint _ hUup).2
  have hMy₁ : M₀.atom (h.s.down K.y₁) = U.lower := by
    rw [hA.atom, K.My₁, hKlo]; exact hA.eps _ (hint _ hUlo).1 (hint _ hUlo).2
  have hMy₂ : M₀.atom (h.s.down K.y₂) = U.lower := by
    rw [hA.atom, K.My₂, hKlo]; exact hA.eps _ (hint _ hUlo).1 (hint _ hUlo).2
  have PU : SourceObjectJointPair U U.upper (h.s.down K.x₂) (h.s.down K.x₁) :=
    ⟨hMx₂, hMx₁, (hCD _).mp K.in_a.2, (hCD _).mp K.in_a.1, by rw [hD.out]; exact K.Mout₂, by rw [hD.out]; exact K.Mout₁⟩
  have PL : SourceObjectJointPair U U.lower (h.s.down K.y₂) (h.s.down K.y₁) :=
    ⟨hMy₂, hMy₁, (hCD _).mp K.in_b.2, (hCD _).mp K.in_b.1, by rw [hD.out]; exact K.Mouty₂, by rw [hD.out]; exact K.Mouty₁⟩
  refine ⟨K, by rw [hKC, hatoms], hKup, hKlo, hKfa, hKfb, ⟨(hCD _).mp K.in_a.1, (hCD _).mp K.in_a.2, (hCD _).mp K.in_b.1,
    (hCD _).mp K.in_b.2⟩, ⟨hMx₁, hMy₁⟩, PU, PL, ?_, ?_⟩
  · have := object_gapKind_pair U L γ η w κ .SG hsg PU
    rw [gapAt_comp_down]
    have e : Molecule.gapAt L w κ (h.s.down K.x₁) (h.s.down K.x₂) = -Molecule.gapAt L w κ (h.s.down K.x₂) (h.s.down K.x₁) := by
      simp [Molecule.gapAt]
    rw [e, gapKind_neg]; exact this
  · have htw := object_gap_twin U (fun b hb => Mole.deg_le_four M₀ hM₀ hb) (Molecule.kvec L w κ)
      (fun x => by simp [Molecule.kvec, hmate]) h0 PU PL
    unfold pgap
    simp only [St.pr, Molecule.gapAt]
    rw [eq_neg_iff_add_eq_zero]
    calc _ = -((Molecule.kvec L w κ (h.s.down K.x₂) - Molecule.kvec L w κ (h.s.down K.x₁)) +
          (Molecule.kvec L w κ (h.s.down K.y₂) - Molecule.kvec L w κ (h.s.down K.y₁))) := by abel
      _ = 0 := by rw [htw, neg_zero]


def VineNodeExistsL (M₀ : Molecule V D₀) (Rn : ℕ) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀))
    (Fst : Set (Src.Object Src.γL M₀)) (crit : V → Prop) (L γ η : ℝ) (w : Mom d) (A0 : Set (D₀ → (Fin d → ℤ))) : Prop :=
  ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1L M₀ Rn C Un Fst L γ η w A0 A h → ∀ κ ∈ A,
    ∀ U : Src.Object Src.γL M₀, Collected C (Un κ) L γ η w κ U → UIntact U h → ¬ Dartless U h →
    (U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' h) →
    (∃ t ∈ nodes1 C crit L γ η h, κ ∈ cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
      t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) ∨
    (∃ t ∈ nodes1D C crit h, κ ∈ cls1D L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2)
      t.1 t.2.1 t.2.2.1 t.2.2.2)

theorem vineNodeExistsL_of_class {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {crit : V → Prop} {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))} (hM₀ : M₀.IsMolecule) (hS : SubHypL Rn M₀) (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ)
    (hη : 0 < η) (h2 : 2 / L ≤ L ^ (-γ + η))
    (hmate : ∀ κ ∈ A0, ∀ x, κ (M₀.mate x) = κ x)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hsgC : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → U.HasGapKind L γ η w κ .SG)
    (hdesC : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → HingeData C U)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Src.Object Src.γL M₀, Collected C (Un κ) L γ η w κ U → Collected C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hsh : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → U.atoms.card = 3 ∨ ObjVine M₀ U)
    (hHC : HostConn M₀ C Un L γ η w A0)
    (hcrit : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → ∀ a ∈ U.atoms, a ≠ U.upper → a ≠ U.lower → ¬ crit a) :
    VineNodeExistsL M₀ Rn C Un Fst crit L γ η w A0 := by
  intro A h hinv κ hκ U hU hUint hnd hord
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hL1 : 1 < L := lt_of_lt_of_le (by have := Real.add_one_lt_exp (show (1:ℝ) ≠ 0 by norm_num); linarith) hLe
  have hAe : A ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨κ, hκ⟩
  obtain ⟨hA0, hctx⟩ := hinv
  obtain ⟨⟨R₁, hR₁, hc⟩, -, hr⟩ := hctx.resolve_left hAe
  have hκ0 : κ ∈ A0 := hA0 hκ
  have hA := hc.anc
  have hD := hc.rel
  have hdeg : ∀ b ∈ h.s.M.atoms, h.s.M.deg b ≤ 4 := fun b hb => by
    have h1 := hc.good.1.bounds b hb
    have h3 := Mole.outdeg_add_indeg h.s.M b
    omega
  obtain ⟨K, hKat, hKup, hKlo, hKfa, hKfb, hKcd, hKJ, PU, PL, hsgX, htwin⟩ :=
    vineDataL_of_intact hM₀ hS (hmate κ hκ0) (h0 κ hκ0) h hA hD hdeg U hUint (hsgC κ hκ0 U hU)
  have hUup : U.upper ∈ U.atoms := object_mem_of_joint U (Or.inl rfl)
  have hUlo : U.lower ∈ U.atoms := object_mem_of_joint U (Or.inr rfl)
  have hHD := hdesC κ hκ0 U hU
  have hanc : ∀ b ∈ U.atoms, h.anc b = b := fun b hb => hA.eps b (hUint b hb).1 (hUint b hb).2
  have hnl : ∀ x : h.s.D, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x) := fun x e => by
    apply hS.noloop (h.s.down x)
    have e1 := hA.atom x
    have e2 := hA.atom (h.s.M.mate x)
    rw [← hD.mate] at e2
    rw [e1, e2, e]
  have hdesu : Desig C (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂) := by
    intro hmem
    rw [hKup, hanc _ hUup] at hmem ⊢
    obtain ⟨f, s, hf1, hs1, hfc, hsc, haf, has, hout⟩ := hHD _ hmem (Or.inl rfl)
    exact ⟨f, s, hf1, hs1, Or.inl (pair_set_eq U PU (Or.inl rfl) hfc hsc haf has hout)⟩
  have hdesl : Desig C (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂) := by
    intro hmem
    rw [hKlo, hanc _ hUlo] at hmem ⊢
    obtain ⟨f, s, hf1, hs1, hfc, hsc, haf, has, hout⟩ := hHD _ hmem (Or.inr rfl)
    exact ⟨f, s, hf1, hs1, Or.inl (pair_set_eq U PL (Or.inr rfl) hfc hsc haf has hout)⟩
  have hCB : CompBeta h.s := (invL_reach1 hS (h0 κ hκ0) (hr κ hκ)).choose_spec.2.comp
  have hMol : h.s.M.IsMolecule := isMolecule_of_compBeta hc.good hCB
  have hKcrit : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a :=
    fun a ha h1 h2 => hcrit κ hκ0 U hU a (hKat ▸ ha) (hKup ▸ h1) (hKlo ▸ h2)
  have hconn0 : ∀ K' : Step1.VineCut Src.γL h.s.M, K'.C.atoms = K.C.atoms → Nonempty (Step1.DoubleShape K') →
      ∃ G : Finset h.s.D, (∀ z ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K' G := by
    rcases reach1L_connInv hS (h0 κ hκ0) (hdisj κ hκ0) (hr κ hκ) with hd | hI
    · exact absurd (hd U hU) hnd
    · exact hconn0_of_hostConnL hHC hκ0 hA hD hI hU hUint hKat
  have hcl0 : ∀ K' : Step1.VineCut Src.γL h.s.M, K'.C.atoms = K.C.atoms → Step1.SingleVineVCGamma K' ∨ Nonempty (Step1.DoubleShape K') :=
    fun K' he => hcls_state hA hD hnl hdeg U hUint (hsh κ hκ0 U hU) K' (he.trans hKat)
  have hF : VFacts C crit h K ∨ VFactsD1 C crit h K := by
    have hu' : h.s.cls K.C.upper = .eps := hKup ▸ (hUint _ hUup).2
    have hl' : h.s.cls K.C.lower = .eps := hKlo ▸ (hUint _ hUlo).2
    by_cases hd2 : h.s.M.deg K.C.upper = 2 ∨ h.s.M.deg K.C.lower = 2
    · right
      exact ⟨hu', hl', hd2, hdesu, hdesl, fun K' he => hcl0 K' (vinePostG_atoms_eq he),
        fun K' he hd => hconn0 K' (vinePostG_atoms_eq he) hd, hnl, ladderLoss_le_86 hMol K (hcl0 K rfl), hKcrit⟩
    · left
      push Not at hd2
      have hne1 : K.x₁ ≠ K.x₂ := by
        intro e; have h1 := K.cut_a.2.2.2.2.2.1; have h2 := K.cut_a.2.2.2.2.2.2; rw [e] at h1; simp_all
      have hne2 : K.y₁ ≠ K.y₂ := by
        intro e; have h1 := K.cut_b.2.2.2.2.2.1; have h2 := K.cut_b.2.2.2.2.2.2; rw [e] at h1; simp_all
      have d1 := two_le_deg K.Mx₁ K.Mx₂ hne1
      have d2 := two_le_deg K.My₁ K.My₂ hne2
      have VH := vhard_of_shape hA hD hnl hdeg hMol hUint hKat (hsh κ hκ0 U hU) hconn0 hKcrit
      exact ⟨hu', hl', by omega, by omega, hdesu, hdesl, VH.hcls, VH.hconn, hnl, VH.hrho, VH.hint⟩
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
  have hdet : ∀ K' : Step1.VineCut Src.γL h.s.M, K'.x₁ = K.x₁ → K'.x₂ = K.x₂ → K'.y₁ = K.y₁ → K'.y₂ = K.y₂ → K'.fa = fresh3 h 0 →
      K'.fb = fresh3 h 1 → U.atoms = K'.C.atoms := fun K' e1 e2 e3 e4 e5 e6 =>
    hKat.symm.trans (vineCut_atoms_determined K K' e1.symm e2.symm e3.symm e4.symm (hKfa.trans e5.symm) (hKfb.trans e6.symm))
  have hAv : ∀ (x₁ x₂ y₁ y₂ : h.s.D), x₁ = K.x₁ → x₂ = K.x₂ → y₁ = K.y₁ → y₂ = K.y₂ →
      κ ∈ Avine C Un Fst L γ η w h A x₁ x₂ y₁ y₂ := by
    rintro x₁ x₂ y₁ y₂ rfl rfl rfl rfl
    refine ⟨hκ, U, hU, fun K' e1 e2 e3 e4 e5 e6 => hdet K' e1 e2 e3 e4 e5 e6, hKcd, ?_, hord⟩
    exact Or.inl hKJ
  rcases hF with hF | hF
  swap
  · exact Or.inr ⟨(K.x₁, K.x₂, K.y₁, K.y₂), Finset.mem_filter.2 ⟨Finset.mem_univ _, K, rfl, rfl, rfl, rfl, hKfa, hKfb, hF⟩,
      hAv _ _ _ _ rfl rfl rfl rfl, hsgX, Or.inr htwin⟩
  left
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


/-- The coverage hypothesis `hmem` of `chain_coverL`. -/
def HmemAtL (M₀ : Molecule V D₀) (Rn : ℕ) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀))
    (Fst : Set (Src.Object Src.γL M₀)) (crit : V → Prop) (L γ η : ℝ) (w : Mom d) (A0 : Set (D₀ → (Fin d → ℤ))) : Prop :=
  ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1L M₀ Rn C Un Fst L γ η w A0 A h → ∀ κ ∈ A,
      ¬ Stuck1 C L γ η w Un κ h →
      (∃ t ∈ nodes1 C crit L γ η h, κ ∈ cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1
          t.2.2.2.2.2.2.2) ∨
      (∃ t ∈ nodesT C L γ η h, κ ∈ cls3 L γ η w h (Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2) ∨
      (∃ t ∈ nodes1D C crit h, κ ∈ cls1D L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2)
          t.1 t.2.1 t.2.2.1 t.2.2.2)

theorem hmemAtL_of_shape {M₀ : Molecule V D₀} {Rn : ℕ} {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {crit : V → Prop} {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))} (hM₀ : M₀.IsMolecule) (hS : SubHypL Rn M₀) (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ)
    (hη : 0 < η) (h2 : 2 / L ≤ L ^ (-γ + η))
    (hmate : ∀ κ ∈ A0, ∀ x, κ (M₀.mate x) = κ x)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Src.Object Src.γL M₀, Collected C (Un κ) L γ η w κ U → Collected C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hFst : ∀ κ ∈ A0, ∀ U ∈ Fst, Collected C (Un κ) L γ η w κ U)
    (hsgC : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → U.HasGapKind L γ η w κ .SG)
    (hdesC : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → HingeData C U)
    (hsh : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → U.atoms.card = 3 ∨ ObjVine M₀ U)
    (hHC : HostConn M₀ C Un L γ η w A0)
    (hcrit : ∀ κ ∈ A0, ∀ U, Collected C (Un κ) L γ η w κ U → ∀ a ∈ U.atoms, a ≠ U.upper → a ≠ U.lower → ¬ crit a) :
    HmemAtL M₀ Rn C Un Fst crit L γ η w A0 := by
  have hv := vineNodeExistsL_of_class (crit := crit) (Fst := Fst) hM₀ hS hLe hηγ hη h2 hmate h0 hsgC hdesC hdisj hsh hHC hcrit
  intro A h hA κ hκ hns
  have hAe : A ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨κ, hκ⟩
  have hr : Reach1L C Un Fst L γ η w κ h := (hA.2.resolve_left hAe).2.2 κ hκ
  have hκ0 : κ ∈ A0 := hA.1 hκ
  have hinv := collInv_of_reach1L hS (h0 κ hκ0) (hdisj κ hκ0) hr
  unfold Stuck1 at hns
  by_cases hex : ∃ U, Collected C (Un κ) L γ η w κ U ∧ ¬ Dartless U h
  · obtain ⟨U₀, hU₀, hnd₀⟩ := hex
    have key : (∃ t ∈ nodes1 C crit L γ η h, κ ∈ cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) ∨
        (∃ t ∈ nodes1D C crit h, κ ∈ cls1D L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2)
          t.1 t.2.1 t.2.2.1 t.2.2.2) := by
      by_cases hF : ∃ U ∈ Fst, ¬ Dartless U h
      · obtain ⟨U, hUF, hnd⟩ := hF
        exact hv A h hA κ hκ U (hFst κ hκ0 U hUF) ((hinv U (hFst κ hκ0 U hUF)).resolve_left hnd) hnd (Or.inl hUF)
      · push Not at hF
        exact hv A h hA κ hκ U₀ hU₀ ((hinv U₀ hU₀).resolve_left hnd₀) hnd₀ (Or.inr hF)
    rcases key with k | k
    · exact Or.inl k
    · exact Or.inr (Or.inr k)
  · right; left
    push Not at hex
    have hall : ∀ U, Collected C (Un κ) L γ η w κ U → Dartless U h := fun U hU => hex U hU
    have hnt : ¬ NoTripleCut C L γ η w κ h := fun hn => hns ⟨hn, hall⟩
    exact hmem_triple hLe hηγ h2 hκ hall hnt

end WaveTurbulence.GammaLow.FinalCount.H
