/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Cov4

/-! # C1b1 MK-PHASE1 (16): the collected and triple nodes exist (coverage, part 5)

Copy-thread of main's LOW coverage (LowChain22 `vineNodeExistsL_of_class`, LowChain20 `hconn0_of_hostConnL`, AsmHmem
`hmem_triple`; sha256 in COPIED-SHA256SUMS) to the survivor Step 1:

* `hconn0_of_hostConnMK`: the outside connectivity of a three-atom collected object from `HostConnMK` (the S4-shape
  input with the earlier survivor pieces `qs` in the kill set) and the bookkeeping `BookE`;
* `collNodeExists`: an intact collected (`CollectedF`) object not yet removed, in the first-stage order, gives a vine or
  D1 node whose class (`AvineE`, through `AvineF`) contains the decoration;
* `hmem_tripleG`: main's `hmem_triple` with an arbitrary class (`AtripE` here). -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem hconn0_of_hostConnMK {M₀ : Molecule V D₀} {m : ℕ} {C : CollDataMK M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))} {κ : D₀ → (Fin d → ℤ)} (hHC : HostConnMK M₀ C Un E L γ η w A0) (hκ : κ ∈ A0)
    {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s) {ps qs : List (Object M₀ × Quad D₀)}
    (hI : BookE M₀ C Un Fst E L γ η w κ h ps qs)
    {U : Object M₀} (hUc : CollectedF C (Un κ) L γ η w κ U) (hint : UIntact U h) {K : VineCut h.s.M}
    (hKat : K.C.atoms = U.atoms) :
    ∀ K' : VineCut h.s.M, K'.C.atoms = K.C.atoms → Nonempty (DoubleShape K') →
      ∃ G : Finset h.s.D, (∀ z ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K' G := by
  intro K' hK'at ⟨S⟩
  refine ⟨{K'.x₁, K'.x₂, K'.y₁, K'.y₂}, fun z hz => hz, ?_⟩
  obtain ⟨⟨hinj, hrem, hpres, -, -, -, -⟩, hps, hpw, hqs, -, -⟩ := hI
  set a := K'.C.upper with ha
  set b := K'.C.lower with hb
  set x := S.x with hx
  have hUat : U.atoms = {a, x, b} := by rw [← hKat, ← hK'at]; exact S.atoms_eq
  have hax : a ≠ x := S.x_ne_a.symm
  have hxb : x ≠ b := S.x_ne_b
  have hab : a ≠ b := K'.ab_ne
  have hmem : ∀ v ∈ ({a, x, b} : Finset V), v ∈ h.s.M.atoms ∧ h.s.cls v = .eps := fun v hv => hint v (hUat ▸ hv)
  have hancε : ∀ v ∈ ({a, x, b} : Finset V), h.anc v = v := fun v hv => hA.eps v (hmem v hv).1 (hmem v hv).2
  have haM : a ∈ ({a, x, b} : Finset V) := by simp
  have hxM : x ∈ ({a, x, b} : Finset V) := by simp
  have hbM : b ∈ ({a, x, b} : Finset V) := by simp
  -- closure of the darts at x
  have hclos : ∀ z, M₀.atom z = x → M₀.atom (M₀.mate z) = a ∨ M₀.atom (M₀.mate z) = b := by
    intro z hz
    obtain ⟨x', hx'⟩ := hA.surj x (hmem x hxM).1 (hmem x hxM).2 z hz
    have h1 : h.anc (h.s.M.atom x') = x := by rw [← hA.atom x', hx', hz]
    have h2 : h.s.M.atom x' = x := hA.uniq _ (h.s.M.atom_mem x') x (hmem x hxM).1 (hmem x hxM).2 h1
    have h3 : x' ∈ h.s.M.dartsAt x := (Mole.mem_dartsAt _ _ _).2 h2
    rw [S.darts_x] at h3
    have hm : M₀.atom (M₀.mate z) = h.anc (h.s.M.atom (h.s.M.mate x')) := by
      rw [← hx', hD.mate, hA.atom]
    simp only [Finset.mem_insert, Finset.mem_singleton] at h3
    rcases h3 with e | e | e | e <;> rw [e, h.s.M.mate_mate] at hm
    · left; rw [hm, K'.Mx₁, hancε a haM]
    · left; rw [hm, K'.Mx₂, hancε a haM]
    · right; rw [hm, K'.My₁, hancε b hbM]
    · right; rw [hm, K'.My₂, hancε b hbM]
  have hdis : ∀ p ∈ ps, Disjoint p.1.atoms U.atoms := fun p hp =>
    Finset.disjoint_left.2 fun v hv hvU => hrem p (List.mem_append_right _ hp) v hv (hint v hvU)
  have hconn := hHC κ hκ qs ps U a x b hqs hps hpw hdis hUc hUat hax hxb hab hclos
  -- the lift
  let σ : V → V := fun s => if hs : ∃ c ∈ h.s.M.atoms, h.anc c = s then Classical.choose hs else s
  have hσ : ∀ c ∈ h.s.M.atoms, σ (h.anc c) = c := by
    intro c hc
    have hs : ∃ c' ∈ h.s.M.atoms, h.anc c' = h.anc c := ⟨c, hc, rfl⟩
    simp only [σ, dite_eq_left hs]
    exact hinj _ (Classical.choose_spec hs).1 _ hc (Classical.choose_spec hs).2
  have hint' : ∀ c ∈ vineInterior K', c = x := by
    intro c hc
    simp only [vineInterior, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    rw [S.atoms_eq] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with ⟨hc | hc | hc, h1, h2⟩
    · exact absurd hc h1
    · exact hc
    · exact absurd hc h2
  have hxint : x ∈ vineInterior K' := by
    unfold vineInterior
    rw [S.atoms_eq]
    refine Finset.mem_sdiff.2 ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hax.symm, hxb⟩
  -- mate darts at x
  have hxd : ∀ y : h.s.D, y ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D) → h.s.M.atom (h.s.M.mate y) = x := by
    intro y hy
    have : h.s.M.mate y ∈ h.s.M.dartsAt x := by
      rw [S.darts_x]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
      rcases hy with e | e | e | e <;> simp [e]
    exact (Mole.mem_dartsAt _ _ _).1 this
  have hxd' : ∀ y : h.s.D, h.s.M.mate y ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D) → h.s.M.atom y = x := by
    intro y hy
    have := hxd _ hy
    rwa [h.s.M.mate_mate] at this
  have hstep : ∀ s t, Relation.EqvGen (fun s t : V => ∃ z, M₀.atom z = s ∧ M₀.atom (M₀.mate z) = t ∧
      z ∉ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ KillS qs ∪ {z | M₀.atom z = x}) ∧
      M₀.mate z ∉ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ KillS qs ∪ {z | M₀.atom z = x})) s t →
      Relation.EqvGen (fun s t : V => s ∉ vineInterior K' ∧ t ∉ vineInterior K' ∧
        ∃ z, h.s.M.atom z = s ∧ h.s.M.atom (h.s.M.mate z) = t ∧ z ∉ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D) ∧
          h.s.M.mate z ∉ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D)) (σ s) (σ t) := by
    intro s t hst
    induction hst with
    | rel s t hr =>
      obtain ⟨z, hs, ht, hz, hmz⟩ := hr
      have hpr : ∀ z' : D₀, z' ∉ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ KillS qs ∪ {z | M₀.atom z = x}) → ∃ x₀ : h.s.D, h.s.down x₀ = z' := by
        intro z' hz'
        by_contra hno
        push Not at hno
        obtain ⟨p, hp, hk⟩ := hpres z' hno
        rcases List.mem_append.1 hp with hp | hp
        · exact hz' (Or.inl (Or.inr ⟨p, hp, hk⟩))
        · exact hz' (Or.inl (Or.inl (Set.mem_iUnion₂.2 ⟨p, hp, hk⟩)))
      obtain ⟨x₀, hx₀⟩ := hpr z hz
      have hz1 : M₀.atom z ≠ x := fun e => hz (Or.inr e)
      have hz2 : M₀.atom (M₀.mate z) ≠ x := fun e => hmz (Or.inr e)
      have hc1 : h.anc (h.s.M.atom x₀) = s := by rw [← hs, ← hx₀, hA.atom]
      have hc2 : h.anc (h.s.M.atom (h.s.M.mate x₀)) = t := by rw [← ht, ← hx₀, hD.mate, hA.atom]
      have hs1 : σ s = h.s.M.atom x₀ := by rw [← hc1]; exact hσ _ (h.s.M.atom_mem x₀)
      have ht1 : σ t = h.s.M.atom (h.s.M.mate x₀) := by rw [← hc2]; exact hσ _ (h.s.M.atom_mem _)
      rw [hs1, ht1]
      have hne : ∀ c ∈ h.s.M.atoms, h.anc c ≠ x → c ∈ h.s.M.atoms → c ∈ vineInterior K' → False := by
        intro c _ hcx _ hci
        have := hint' c hci
        subst this
        exact hcx (hancε _ hxM)
      refine Relation.EqvGen.rel _ _ ⟨fun hci => hne _ (h.s.M.atom_mem _) (by rw [hc1]; exact fun e => hz1 (hs.trans e)) (h.s.M.atom_mem _) hci,
        fun hci => hne _ (h.s.M.atom_mem _) (by rw [hc2]; exact fun e => hz2 (ht.trans e)) (h.s.M.atom_mem _) hci, x₀, rfl, rfl, ?_, ?_⟩
      · intro hG
        apply hne _ (h.s.M.atom_mem (h.s.M.mate x₀)) (by rw [hc2]; exact fun e => hz2 (ht.trans e)) (h.s.M.atom_mem _)
        rw [hxd x₀ hG]; exact hxint
      · intro hG
        apply hne _ (h.s.M.atom_mem x₀) (by rw [hc1]; exact fun e => hz1 (hs.trans e)) (h.s.M.atom_mem _)
        rw [hxd' x₀ hG]; exact hxint
    | refl s => exact Relation.EqvGen.refl _
    | symm s t _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans s t u _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have := hstep a b hconn
  have e1 : σ a = a := by have := hσ a (hmem a haM).1; rwa [hancε a haM] at this
  have e2 : σ b = b := by have := hσ b (hmem b hbM).1; rwa [hancε b hbM] at this
  rw [e1, e2] at this
  exact this



theorem collNodeExists [Infinite V] {M₀ : Molecule V D₀} {m : ℕ} {Rn : ℕ} {C : CollDataMK M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {crit : V → Prop}
    {L γ η : ℝ} {w : Mom d}
    {A0 : Set (D₀ → (Fin d → ℤ))} (hM₀ : M₀.IsMolecule) (hS : SubHypL Rn M₀) (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ)
    (hη : 0 < η) (h2 : 2 / L ≤ L ^ (-γ + η))
    (hmate : ∀ κ ∈ A0, ∀ x, κ (M₀.mate x) = κ x)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hsgC : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → U.HasGapKind L γ η w κ .SG)
    (hdesC : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → HingeData C.toCollData U)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Object M₀, CollectedF C (Un κ) L γ η w κ U → CollectedF C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hsh : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → U.atoms.card = 3 ∨ ObjVine M₀ U)
    (hsd : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hHC : HostConnMK M₀ C Un E L γ η w A0)
    (hcrit : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ a ∈ U.atoms, a ≠ U.upper → a ≠ U.lower → ¬ crit a) :
    ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h → ∀ κ ∈ A,
      ∀ U : Object M₀, CollectedF C (Un κ) L γ η w κ U → UIntact U h → ¬ Dartless U h →
      (U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' h) →
      (∃ t ∈ nodes1 C.toCollData crit L γ η h, κ ∈ cls1 L γ η w h
          (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) ∨
      (∃ t ∈ nodes1D C.toCollData crit h, κ ∈ cls1D L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2)
          t.1 t.2.1 t.2.2.1 t.2.2.2) := by
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
  have hdesu : Desig C.toCollData (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂) := by
    intro hmem
    rw [hKup, hanc _ hUup] at hmem ⊢
    obtain ⟨f, s, hf1, hs1, hfc, hsc, haf, has, hout⟩ := hHD _ hmem (Or.inl rfl)
    exact ⟨f, s, hf1, hs1, Or.inl (pair_set_eq U PU (Or.inl rfl) hfc hsc haf has hout)⟩
  have hdesl : Desig C.toCollData (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂) := by
    intro hmem
    rw [hKlo, hanc _ hUlo] at hmem ⊢
    obtain ⟨f, s, hf1, hs1, hfc, hsc, haf, has, hout⟩ := hHD _ hmem (Or.inr rfl)
    exact ⟨f, s, hf1, hs1, Or.inl (pair_set_eq U PL (Or.inr rfl) hfc hsc haf has hout)⟩
  have hCB : CompBeta h.s := (invL_reach1E hS (h0 κ hκ0) (hr κ hκ)).choose_spec.2.comp
  have hMol : h.s.M.IsMolecule := isMolecule_of_compBeta hc.good hCB
  have hKcrit : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a :=
    fun a ha h1 h2 => hcrit κ hκ0 U hU a (hKat ▸ ha) (hKup ▸ h1) (hKlo ▸ h2)
  have hconn0 : ∀ K' : VineCut h.s.M, K'.C.atoms = K.C.atoms → Nonempty (DoubleShape K') →
      ∃ G : Finset h.s.D, (∀ z ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K' G := by
    rcases (reach1LE_book hS (h0 κ hκ0) (hdisj κ hκ0) (hsd κ hκ0) (hr κ hκ)).2 with ⟨ps, qs, hI⟩ | ⟨hd, -⟩
    · exact hconn0_of_hostConnMK hHC hκ0 hA hD hI hU hUint hKat
    · exact absurd (hd U hU) hnd
  have hcl0 : ∀ K' : VineCut h.s.M, K'.C.atoms = K.C.atoms → SingleVineVC K' ∨ Nonempty (DoubleShape K') :=
    fun K' he => hcls_state hA hD hnl hdeg U hUint (hsh κ hκ0 U hU) K' (he.trans hKat)
  have hF : VFacts C.toCollData crit h K ∨ VFactsD1 C.toCollData crit h K := by
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
  have hdet : ∀ K' : VineCut h.s.M, K'.x₁ = K.x₁ → K'.x₂ = K.x₂ → K'.y₁ = K.y₁ → K'.y₂ = K.y₂ → K'.fa = fresh3 h 0 →
      K'.fb = fresh3 h 1 → U.atoms = K'.C.atoms := fun K' e1 e2 e3 e4 e5 e6 =>
    hKat.symm.trans (vineCut_atoms_determined K K' e1.symm e2.symm e3.symm e4.symm (hKfa.trans e5.symm) (hKfb.trans e6.symm))
  have hAv : ∀ (x₁ x₂ y₁ y₂ : h.s.D), x₁ = K.x₁ → x₂ = K.x₂ → y₁ = K.y₁ → y₂ = K.y₂ →
      κ ∈ AvineE C Un Fst E L γ η w h A x₁ x₂ y₁ y₂ := by
    rintro x₁ x₂ y₁ y₂ rfl rfl rfl rfl
    refine Or.inl ⟨hκ, U, hU, fun K' e1 e2 e3 e4 e5 e6 => hdet K' e1 e2 e3 e4 e5 e6, hKcd, ?_, hord⟩
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



theorem hmem_tripleG [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ}
    {w : Mom d} (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ) (h2 : 2 / L ≤ L ^ (-γ + η)) {B : Set (D₀ → (Fin d → ℤ))}
    {κ : D₀ → (Fin d → ℤ)} {h : HSt V D₀} (hκ : κ ∈ B) (hnt : ¬ NoTripleCut C L γ η w κ h) :
    ∃ t ∈ nodesT C L γ η h, κ ∈ cls3 L γ η w h B t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1
      t.2.2.2.2.2.2 := by
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hκA : κ ∈ B := hκ
  unfold NoTripleCut at hnt
  push Not at hnt
  obtain ⟨v, v₂, x₁, x₂, hcd0, hε', h3, hhinge, hdes, hu, hsg⟩ := hnt
  have hcd : h.s.M.IsCutData v (fresh h) x₁ x₂ :=
    ⟨hcd0.1, fresh_notMem h, hcd0.2.2.1, hcd0.2.2.2.1, hcd0.2.2.2.2.1, hcd0.2.2.2.2.2.1, hcd0.2.2.2.2.2.2⟩
  obtain ⟨R', hR, hsim⟩ := exists_label_of_SG w (κ ∘ h.s.down) x₁ x₂ hL h2 hsg
  obtain ⟨z, hRz, hz1, hz2⟩ := label_zrange hLe hηγ hR
  subst hRz
  have hT : TripleCond C h v x₁ x₂ := ⟨hhinge, hdes, hu⟩
  by_cases hI : IotaHit L η w κ h.alive (h.s.pr x₁ x₂) ((2 : ℝ) ^ z)
  · obtain ⟨q, hq, ⟨a, ha, vis, hcr⟩, sg, hsgn, h1, h2'⟩ := iotaAlive_of_hit hI
    refine ⟨(v, x₁, x₂, z, true, a, decide (sg = 1)), ?_, ?_⟩
    · refine mem_nodesT.2 ⟨Finset.mem_filter.2 ⟨?_, hcd, hε', h3, hR, ha, fun _ => ⟨q, vis, hcr, hq⟩⟩, hT⟩
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc]
      exact ⟨hcd0.1, ⟨hz1, hz2⟩, ha, trivial⟩
    · have hq' : qOf h a (h.s.pr x₁ x₂) = q := by simp [qOf, hcr]
      have hsg' : (if decide (sg = 1) then (1 : ℝ) else -1) = sg := by
        rcases hsgn with rfl | rfl <;> norm_num
      refine ⟨hκA, hsg, hsim, fun _ => ?_, fun hb => by simp at hb⟩
      rw [hq', hsg']; exact ⟨h1, h2'⟩
  · refine ⟨(v, x₁, x₂, z, false, v, true), ?_, ?_⟩
    · refine mem_nodesT.2 ⟨Finset.mem_filter.2 ⟨?_, hcd, hε', h3, hR, hcd0.1, fun hb => by simp at hb⟩, hT⟩
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc]
      exact ⟨hcd0.1, ⟨hz1, hz2⟩, hcd0.1, trivial⟩
    · exact ⟨hκA, hsg, hsim, fun hb => by simp at hb, fun _ => hI⟩

end WaveTurbulence.Flower.FinalMKPhase1
