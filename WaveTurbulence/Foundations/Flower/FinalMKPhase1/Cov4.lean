/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Cov3
public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Classes

/-! # C1b1 MK-PHASE1 (15): the survivor and re-cut nodes exist (coverage, part 4)

`survNodeExists`: for a decoration of a class at a state of the survivor Step 1, the survivor `E i` next in the removal
order (`SurvOrder`, not dartless) gives a node whose class contains the decoration:

* both joints `ε`: main's vine node (`VFacts`, joints of degree `≥ 3`) or D1 node (`VFactsD1`), class `AvineE`
  through `AvineS` (main's `vineNodeExistsL_of_class`, LowChain22, with the matched survivor);
* a non-`ε` joint (a pending re-cut joint): the **re-cut node** (`VFactsRC`) with `hone` (`recut_hone`, obligation 1)
  and `hpend` (`recut_pend`), class `cls1D` on `AvineS`.

Survivors are single vines (`survShape`), so no cut along them is a double shape (`objVine_card_ne_three`) and the
outside-connectivity clause is vacuous. -/

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

section nodes
variable {M₀ : Molecule V D₀} {m : ℕ} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
  {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

/-- An interior atom of a survivor still present is itself a present atom (it is not the shared joint). -/
theorem BookE.surv_interior {Rn : ℕ} (hS : SubHypL Rn M₀) {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc)
    {ps qs : List (Object M₀ × Quad D₀)} (B : BookE M₀ C Un Fst E L γ η w κ h ps qs)
    (hsd : ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hchain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1)
    {i : Fin m} (hi : ¬ Dartless (E i) h) {b : V} (hb : b ∈ (E i).atoms) (h1 : b ≠ (E i).upper)
    (h2 : b ≠ (E i).lower) : ancInv h b = b := by
  have hM₀ : M₀.IsMolecule := hS.isMolecule
  have hm := B.surv_match hS hsd hchain hi
  have hc := hm.mem b hb
  have hcb := hm.anc b hb
  by_cases he : h.s.cls (ancInv h b) = .eps
  · rw [← hA.eps _ hc he]; exact hcb
  · exfalso
    obtain ⟨p, hp, hpa⟩ := B.geom.neps _ hc he
    rw [hcb] at hpa
    obtain ⟨j, -, hpj, -, hcard⟩ := B.piece_meet hsd hchain hi hb hp hpa
    rw [hpj] at hpa
    obtain ⟨z, hza, hzg⟩ := exists_group_dart (E j) hpa
    have hcd : (E i).ContainsDart z :=
      containsDart_of_interior (E i) (fun c hc => Mole.deg_le_four M₀ hM₀ hc) (object_oh (E i)).basic.2.2.2.2.2.2
        (hza ▸ hb) (hza ▸ h1) (hza ▸ h2)
    exact not_two_groups hS hcard hzg (containsDart_inGroup _ hcd)

/-- **The survivor nodes and the re-cut nodes exist.** -/
theorem survNodeExists [Infinite V] {Rn : ℕ} {crit : V → Prop} {A0 : Set (D₀ → (Fin d → ℤ))}
    (hM₀ : M₀.IsMolecule) (hS : SubHypL Rn M₀) (hLe : Real.exp 1 ≤ L) (hηγ : η ≤ γ) (hη : 0 < η)
    (h2 : 2 / L ≤ L ^ (-γ + η)) (hmate : ∀ κ ∈ A0, ∀ x, κ (M₀.mate x) = κ x)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Object M₀, CollectedF C (Un κ) L γ η w κ U → CollectedF C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hsd : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hobl : ∀ κ ∈ A0, SubproOblGMK C.toCollData E L γ η w κ)
    (hchain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1)
    (hshape : ∀ i, ObjVine M₀ (E i))
    (hcrit : ∀ i, ∀ a ∈ (E i).atoms, a ≠ (E i).upper → a ≠ (E i).lower → ¬ crit a)
    (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (hinv : Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h)
    (κ : D₀ → (Fin d → ℤ)) (hκ : κ ∈ A) (i : Fin m) (hi : ¬ Dartless (E i) h) (ho : SurvOrder Fst E i h) :
    (∃ t ∈ nodes1 C.toCollData crit L γ η h, κ ∈ cls1 L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
        t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) ∨
    (∃ t ∈ nodes1D C.toCollData crit h, κ ∈ cls1D L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2)
        t.1 t.2.1 t.2.2.1 t.2.2.2) ∨
    (∃ t ∈ nodesRC C.toCollData crit E L γ η h, κ ∈ cls1D L γ η w h (AvineS E Fst h A t.1 t.2.1 t.2.2.1 t.2.2.2)
        t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hL1 : 1 < L := lt_of_lt_of_le (by have := Real.add_one_lt_exp (show (1:ℝ) ≠ 0 by norm_num); linarith) hLe
  have hAe : A ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨κ, hκ⟩
  obtain ⟨hA0, hctx⟩ := hinv
  obtain ⟨⟨R₁, -, hc⟩, -, hr⟩ := hctx.resolve_left hAe
  have hκ0 : κ ∈ A0 := hA0 hκ
  have hA := hc.anc
  have hD := hc.rel
  have hdeg : ∀ b ∈ h.s.M.atoms, h.s.M.deg b ≤ 4 := fun b hb => by
    have h1 := hc.good.1.bounds b hb
    have h3 := Mole.outdeg_add_indeg h.s.M b
    omega
  have hIL := (invL_reach1E hS (h0 κ hκ0) (hr κ hκ)).choose_spec.2
  obtain ⟨-, hbook⟩ := reach1LE_book hS (h0 κ hκ0) (hdisj κ hκ0) (hsd κ hκ0) (hr κ hκ)
  obtain ⟨ps, qs, B⟩ := hbook.resolve_right (fun hd => hi (hd.2 i))
  have hinj := B.geom.inj
  have hm := B.surv_match hS (hsd κ hκ0) hchain hi
  obtain ⟨K, hKat, hKup, hKlo, hKfa, hKfb, hKcd, hKJ, PU, PL, hsgX, htwin, hsv⟩ :=
    vineDataA hM₀ hS (hmate κ hκ0) (h0 κ hκ0) h hA hD hinj hdeg (E i) hm ((hobl κ hκ0).survSG i)
  have hUup : (E i).upper ∈ (E i).atoms := object_mem_of_joint (E i) (Or.inl rfl)
  have hUlo : (E i).lower ∈ (E i).atoms := object_mem_of_joint (E i) (Or.inr rfl)
  -- the survivor cut, for every cut with the node data
  have hancK : K.C.atoms.image h.anc = (E i).atoms := by
    rw [hKat, Finset.image_image]
    ext a
    simp only [Finset.mem_image, Function.comp]
    constructor
    · rintro ⟨b, hb, rfl⟩; rw [hm.anc b hb]; exact hb
    · intro ha; exact ⟨a, ha, hm.anc a ha⟩
  have hsurv : ∀ K' : VineCut h.s.M, K'.x₁ = K.x₁ → K'.x₂ = K.x₂ → K'.y₁ = K.y₁ → K'.y₂ = K.y₂ →
      K'.fa = fresh3 h 0 → K'.fb = fresh3 h 1 → SurvCut E i h K' := by
    intro K' e1 e2 e3 e4 e5 e6
    have hat := vineCut_atoms_determined K K' e1.symm e2.symm e3.symm e4.symm (hKfa.trans e5.symm)
      (hKfb.trans e6.symm)
    refine ⟨by rw [← hat, hancK], ?_, ?_⟩
    · rw [e1, e2, e3, e4]; exact hKcd
    · rw [e1, e3]; exact Or.inl hKJ
  have hsK : SurvCut E i h K := hsurv K rfl rfl rfl rfl hKfa hKfb
  have hAS : ∀ x₁ x₂ y₁ y₂ : h.s.D, x₁ = K.x₁ → x₂ = K.x₂ → y₁ = K.y₁ → y₂ = K.y₂ →
      κ ∈ AvineS E Fst h A x₁ x₂ y₁ y₂ := by
    rintro x₁ x₂ y₁ y₂ rfl rfl rfl rfl
    exact ⟨hκ, i, hsurv, ho⟩
  -- the common node facts
  have hnl : ∀ x : h.s.D, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x) := fun x e => by
    apply hS.noloop (h.s.down x)
    have e1 := hA.atom x
    have e2 := hA.atom (h.s.M.mate x)
    rw [← hD.mate] at e2
    rw [e1, e2, e]
  have hju : h.anc K.C.upper = (E i).upper := by rw [hKup]; exact hm.anc _ hUup
  have hjl : h.anc K.C.lower = (E i).lower := by rw [hKlo]; exact hm.anc _ hUlo
  have hdesu : Desig C.toCollData (h.anc K.C.upper) (h.s.pr K.x₁ K.x₂) := by
    rw [hju]; exact survDesig hS C.toCollData E (hobl κ hκ0) hchain i (Or.inl rfl) PU
  have hdesl : Desig C.toCollData (h.anc K.C.lower) (h.s.pr K.y₁ K.y₂) := by
    rw [hjl]; exact survDesig hS C.toCollData E (hobl κ hκ0) hchain i (Or.inr rfl) PL
  have hMol : h.s.M.IsMolecule := isMolecule_of_compBeta hc.good hIL.comp
  have hKcrit : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a := by
    intro a ha h1 h2
    rw [hKat] at ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
    have hb1 : b ≠ (E i).upper := fun e => h1 (by rw [hKup, e])
    have hb2 : b ≠ (E i).lower := fun e => h2 (by rw [hKlo, e])
    have hbb : ancInv h b = b := B.surv_interior hS hA (hsd κ hκ0) hchain hi hb hb1 hb2
    rw [hbb]
    exact hcrit i b hb hb1 hb2
  have hcl0 : ∀ K' : VineCut h.s.M, K'.C.atoms = K.C.atoms → SingleVineVC K' ∨ Nonempty (DoubleShape K') :=
    fun K' he => Or.inl (hsv (hshape i) K' he)
  have hcardK : K.C.atoms.card ≠ 3 := by
    rw [hKat, Finset.card_image_of_injOn hm.inj]
    exact Subpro.objVine_card_ne_three (hshape i)
  have hconn0 : ∀ K' : VineCut h.s.M, K'.C.atoms = K.C.atoms → Nonempty (DoubleShape K') →
      ∃ G : Finset h.s.D, (∀ z ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K' G := by
    rintro K' he ⟨S⟩
    exfalso
    apply hcardK
    rw [← he, S.atoms_eq, Finset.card_insert_of_notMem (by simp [S.x_ne_a.symm, K'.ab_ne]),
      Finset.card_insert_of_notMem (by simp [S.x_ne_b]), Finset.card_singleton]
  by_cases hε : h.s.cls K.C.upper = .eps ∧ h.s.cls K.C.lower = .eps
  · obtain ⟨hu', hl'⟩ := hε
    by_cases hd2 : h.s.M.deg K.C.upper = 2 ∨ h.s.M.deg K.C.lower = 2
    · right; left
      have hF : VFactsD1 C.toCollData crit h K := ⟨hu', hl', hd2, hdesu, hdesl,
        fun K' he => hcl0 K' (vinePostG_atoms_eq he), fun K' he hd => hconn0 K' (vinePostG_atoms_eq he) hd, hnl,
        ladderLoss_le_86 hMol K (hcl0 K rfl), hKcrit⟩
      exact ⟨(K.x₁, K.x₂, K.y₁, K.y₂), Finset.mem_filter.2 ⟨Finset.mem_univ _, K, rfl, rfl, rfl, rfl, hKfa, hKfb, hF⟩,
        Or.inr (hAS _ _ _ _ rfl rfl rfl rfl), hsgX, Or.inr htwin⟩
    · left
      push Not at hd2
      have d1 := two_le_deg_upper K
      have d2 := two_le_deg_lower K
      have VH := vhard_of_atoms hcl0 hconn0 (hrho_of_cls hMol K (hcl0 K rfl)) hKcrit
      have hF : VFacts C.toCollData crit h K :=
        ⟨hu', hl', by omega, by omega, hdesu, hdesl, VH.hcls, VH.hconn, hnl, VH.hrho, VH.hint⟩
      obtain ⟨R', hR, hsim⟩ := exists_label_of_SG w (κ ∘ h.s.down) K.x₁ K.x₂ hL h2 hsgX
      obtain ⟨z, hRz, hz1, hz2⟩ := label_zrange hLe hηγ hR
      subst hRz
      have hsimy : GapSim L w (κ ∘ h.s.down) K.y₁ K.y₂ ((2 : ℝ) ^ z) := by
        have e : ‖Molecule.gapAt L w (κ ∘ h.s.down) K.y₁ K.y₂‖ =
            ‖Molecule.gapAt L w (κ ∘ h.s.down) K.x₁ K.x₂‖ := by
          have := congrArg norm htwin
          simpa [norm_neg, pgap, St.pr, gapAt_comp_down] using this
        unfold GapSim at hsim ⊢
        rw [e]; exact hsim
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
          refine ⟨Or.inr (hAS _ _ _ _ rfl rfl rfl rfl), hsgX, hsim, hsimy, Or.inr htwin, fun _ => ?_,
            fun hb => by simp at hb⟩
          rw [hq', hsg']; exact ⟨h1, h2'⟩
      · have hnot2 : ¬ IotaHit L η w κ (h.s.pr K.x₁ K.x₂ :: h.alive) (h.s.pr K.y₁ K.y₂) ((2 : ℝ) ^ z) := fun hh =>
          hI (iotaHit_first_of_second hL1 hη (zpow_pos (by norm_num) z) (Or.inr htwin)
            (by have := hsim.1; simpa [pgap, St.pr, gapAt_comp_down] using this) hh)
        refine ⟨(K.x₁, K.x₂, K.y₁, K.y₂, z, false, K.C.upper, true), ?_, ?_⟩
        · unfold nodes1
          have hupm : K.C.upper ∈ h.s.M.atoms := objectAtoms_sub K.C K.a_mem
          refine Finset.mem_filter.2 ⟨?_, K, rfl, rfl, rfl, rfl, hKfa, hKfb, hF, hR, hupm, fun hb => by simp at hb⟩
          simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc]
          exact ⟨⟨hz1, hz2⟩, hupm, trivial⟩
        · exact ⟨Or.inr (hAS _ _ _ _ rfl rfl rfl rfl), hsgX, hsim, hsimy, Or.inr htwin, fun hb => by simp at hb,
            fun _ => ⟨hI, hnot2⟩⟩
  · right; right
    have hrc : h.s.cls K.C.upper ≠ .eps ∨ h.s.cls K.C.lower ≠ .eps := by
      by_contra hcon
      push Not at hcon
      exact hε hcon
    have hRC : ∀ c, c ∈ h.s.M.atoms → 2 ≤ h.s.M.deg c → RCJoint h.s c := by
      intro c hcm hd
      by_cases hce : h.s.cls c = .eps
      · exact Or.inl hce
      · right
        have hab := hc.good.1.ab c hcm hce
        have hng : h.s.cls c ≠ .ghost := hc.good.2 c hcm
        refine ⟨?_, by omega⟩
        rcases hcls : h.s.cls c with _ | _ | _ | _
        · exact absurd hcls hce
        · trivial
        · trivial
        · exact absurd hcls hng
    have hF : VFactsRC C.toCollData crit E L γ η h K :=
      { hu := hRC _ (objectAtoms_sub K.C K.a_mem) (two_le_deg_upper K)
        hl := hRC _ (objectAtoms_sub K.C K.b_mem) (two_le_deg_lower K)
        hrc := hrc
        hone := recut_hone hA B (hsd κ hκ0) hchain K i hsK
        hdu := hdesu
        hdl := hdesl
        hcls := fun K' he => hcl0 K' (vinePostG_atoms_eq he)
        hconn := fun K' he hd => hconn0 K' (vinePostG_atoms_eq he) hd
        hnl := hnl
        hloss := ladderLoss_le_86 hMol K (hcl0 K rfl)
        hint := hKcrit
        hlab := labels_of_hinv hIL.hrec
        hpend := recut_pend hA hD B (hsd κ hκ0) hchain K i hsK hrc }
    exact ⟨(K.x₁, K.x₂, K.y₁, K.y₂), Finset.mem_filter.2 ⟨Finset.mem_univ _, K, rfl, rfl, rfl, rfl, hKfa, hKfb, hF⟩,
      hAS _ _ _ _ rfl rfl rfl rfl, hsgX, Or.inr htwin⟩

end nodes

end WaveTurbulence.Flower.FinalMKPhase1
