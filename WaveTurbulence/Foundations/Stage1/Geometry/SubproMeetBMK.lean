/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCrossMK
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: o75 Theorem 7.5′(6′) (`SubproSupportMK.meetB`) for the marked splice

* `spine_bonds_block` (generic): in a block cut into a spine of vines, every bond of the block is a bond of one member
  (the members meet only at consecutive joints, whose four bonds are the members' bonds, and the ends of the block
  carry only the end members' bonds).
* `ingredient_bonds`: every bond of a VC/HVC group of `G` is a bond of one of its ingredients, except the added bond
  of an HVC (at most one of its two darts at each atom).
* `meetB_atomsMk` (o75 (6′)): an object of `G_sb` meeting a survivor joint lies in a survivor, shares a bond with a
  survivor, or has a hinge in configuration (6).  If not, every hinge of `P` is aligned, the substitution of
  SubproCrossMK makes `P` an object of `G`, inside the marked group `W` of the met survivor; a bond of `P` at its
  upper joint avoiding the added bond of `W` is a bond of an ingredient of `W`, which is a run (impossible: runs are
  collapsed) or a survivor.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1 WaveTurbulence.Mole

section generic
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D}

theorem inGroup_mate_iff {S : Finset V} {y : D} : N.InGroup S (N.mate y) ↔ N.InGroup S y :=
  ⟨fun h => ⟨by have := h.2; rwa [N.mate_mate] at this, h.1⟩,
    fun h => ⟨h.2, by rw [N.mate_mate]; exact h.1⟩⟩

/-- **No loop at a joint of a block** (the block is connected and has one out- and one in-dart at the joint). -/
theorem block_joint_no_loop {S : Finset V} {j1 j2 : V} (hB : N.IsBlock S j1 j2) {x : D}
    (hx : N.atom x = j1) (hxS : N.InGroup S x) : N.atom (N.mate x) ≠ j1 := by
  classical
  intro hloop
  obtain ⟨o, -, -, -, ho⟩ := block_unique_dart hB true
  obtain ⟨i, -, -, -, hi⟩ := block_unique_dart hB false
  have hxm : N.InGroup S (N.mate x) := inGroup_mate_iff.mpr hxS
  have hall : ∀ y, N.atom y = j1 → N.InGroup S y → y = x ∨ y = N.mate x := by
    intro y hy hyS
    have hmo : N.out (N.mate x) = !N.out x := N.out_mate x
    cases hyo : N.out y
    · have h1 := hi y hy hyS hyo
      cases hxo : N.out x
      · exact Or.inl (h1.trans (hi x hx hxS hxo).symm)
      · rw [hxo] at hmo
        exact Or.inr (h1.trans (hi _ hloop hxm hmo).symm)
    · have h1 := ho y hy hyS hyo
      cases hxo : N.out x
      · rw [hxo] at hmo
        exact Or.inr (h1.trans (ho _ hloop hxm hmo).symm)
      · exact Or.inl (h1.trans (ho x hx hxS hxo).symm)
  have key : ∀ a b, Relation.EqvGen (fun a b => ∃ y, N.InGroup S y ∧ N.atom y = a ∧ N.atom (N.mate y) = b) a b →
      (a = j1 ↔ b = j1) := by
    intro a b h
    induction h with
    | rel a b hr =>
      obtain ⟨y, hyS, h1, h2⟩ := hr
      constructor
      · intro ha
        rcases hall y (h1.trans ha) hyS with rfl | rfl
        · rw [← h2]; exact hloop
        · rw [← h2, N.mate_mate]; exact hx
      · intro hb
        rcases hall (N.mate y) (h2.trans hb) (inGroup_mate_iff.mpr hyS) with h | h
        · rw [← h1, ← N.mate_mate y, h]; exact hloop
        · rw [← h1, ← N.mate_mate y, h, N.mate_mate]; exact hx
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  have hc := hB.2.2.2.2.2.2.2.2.2 j1 hB.2.1 j2 hB.2.2.1
  exact hB.2.2.2.1 ((key _ _ hc).mp rfl).symm

/-- Three darts at one atom with one direction: two of them are equal. -/
theorem eq_of_three_darts (hN : N.IsMolecule) {v : V} (hv : v ∈ N.atoms) {bo : Bool} {x y z : D}
    (hx : N.atom x = v) (hy : N.atom y = v) (hz : N.atom z = v) (hxo : N.out x = bo) (hyo : N.out y = bo)
    (hzo : N.out z = bo) (hxy : x ≠ y) : z = x ∨ z = y := by
  classical
  by_contra h
  push Not at h
  have hle : ((N.dartsAt v).filter fun x => N.out x = bo).card ≤ 2 := by
    cases bo
    · exact (hN.1 v hv).2
    · exact (hN.1 v hv).1
  have hsub : ({x, y, z} : Finset D) ⊆ (N.dartsAt v).filter fun x => N.out x = bo := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> simp [Molecule.dartsAt, *]
  have hcard : ({x, y, z} : Finset D).card = 3 :=
    Finset.card_eq_three.mpr ⟨x, y, z, hxy, fun e => h.1 e.symm, fun e => h.2 e.symm, rfl⟩
  have := Finset.card_le_card hsub
  omega

/-- **At a joint shared by two blocks meeting only there, every dart is a dart of one of them.** -/
theorem shared_joint_darts (hN : N.IsMolecule) {A B : Finset V} {a b c : V} (hA : N.IsBlock A a b)
    (hBl : N.IsBlock B b c) (hAB : A ∩ B = {b}) {y : D} (hy : N.atom y = b) :
    N.InGroup A y ∨ N.InGroup B y := by
  have hA' := block_swap_joints N hA
  have hbmem : b ∈ N.atoms := hBl.1 hBl.2.1
  obtain ⟨oA, hoA, hoAg, hoAo, -⟩ := block_unique_dart hA' (N.out y)
  obtain ⟨oB, hoB, hoBg, hoBo, -⟩ := block_unique_dart hBl (N.out y)
  have hne : oA ≠ oB := by
    rintro rfl
    have hm : N.atom (N.mate oA) ∈ A ∩ B := Finset.mem_inter.mpr ⟨hoAg.2, hoBg.2⟩
    rw [hAB, Finset.mem_singleton] at hm
    exact block_joint_no_loop hBl hoB hoBg hm
  rcases eq_of_three_darts hN hbmem hoA hoB hy hoAo hoBo rfl hne with h | h
  · exact Or.inl (h ▸ hoAg)
  · exact Or.inr (h ▸ hoBg)

/-- **Bonds of a spine** (induction along the spine): a bond of the union is a bond of a member or joins the two
ends, and every atom other than the ends has all its bonds in the union. -/
theorem spine_bonds (hN : N.IsMolecule) {L : List (Finset V × V × V)} {U : Finset V} {a b : V}
    (hs : Spine N L U a b) :
    (∀ y, N.InGroup U y → (∃ m ∈ L, N.InGroup m.1 y) ∨ s(N.atom y, N.atom (N.mate y)) = s(a, b)) ∧
      (∀ x ∈ U, x ≠ a → x ≠ b → ∀ y, N.atom y = x → N.atom (N.mate y) ∈ U) := by
  classical
  induction hs with
  | @one T a b hv =>
    obtain ⟨X, hX⟩ := hv
    refine ⟨fun y hy => Or.inl ⟨(T, a, b), List.mem_singleton_self _, hy⟩, ?_⟩
    intro x hx hxa hxb y hy
    exact (inGroup_of_degIn_four hN (hX.1.1 hx) (hX.1.2.2.2.2.2.2.2.2.1 x hx hxa hxb) hy).2
  | @snoc L U T a b c hs hT hi hne ih =>
    obtain ⟨ihP, ihI⟩ := ih
    obtain ⟨X, hX⟩ := hT
    have hBT : N.IsBlock T b c := hX.1
    have hends := hs.ends
    have hab : a ≠ b := hends.2.2
    have hbU : b ∈ U := hends.2.1
    have haU : a ∈ U := hends.1
    -- the last member of `L`
    obtain ⟨L0, t, hL⟩ : ∃ L0 t, L = L0 ++ [t] := by
      rcases List.eq_nil_or_concat L with h | ⟨L0, t, h⟩
      · exact absurd h hs.ne_nilMK
      · exact ⟨L0, t, by rw [h, List.concat_eq_append]⟩
    subst hL
    obtain ⟨T', p, q⟩ := t
    have hqb : q = b := hs.last_sndMK
    subst hqb
    obtain ⟨⟨Xt, hXt⟩, htU⟩ := hs.mem_vine (List.mem_append_right _ (List.mem_singleton_self _))
    have hBt : N.IsBlock T' p q := hXt.1
    have htT : T' ∩ T = {q} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨Finset.mem_inter.mpr ⟨hBt.2.2.1, hBT.2.1⟩, fun v hv => ?_⟩
      have : v ∈ U ∩ T := Finset.mem_inter.mpr ⟨htU (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
      rw [hi] at this
      exact Finset.mem_singleton.mp this
    have hb : ∀ y, N.atom y = q → N.InGroup T' y ∨ N.InGroup T y :=
      fun y hy => shared_joint_darts hN hBt hBT htT hy
    have hmemT : (T, q, c) ∈ L0 ++ [(T', p, q)] ++ [(T, q, c)] := by simp
    have hmemt : (T', p, q) ∈ L0 ++ [(T', p, q)] ++ [(T, q, c)] := by simp
    have haT : a ∉ T := by
      intro haT
      have : a ∈ U ∩ T := Finset.mem_inter.mpr ⟨haU, haT⟩
      rw [hi, Finset.mem_singleton] at this
      exact hab this
    refine ⟨?_, ?_⟩
    · have key : ∀ y, N.InGroup (U ∪ T) y → N.atom y ∈ U →
          (∃ m ∈ L0 ++ [(T', p, q)] ++ [(T, q, c)], N.InGroup m.1 y) ∨
            s(N.atom y, N.atom (N.mate y)) = s(a, c) := by
        intro y hy hyU
        by_cases hwU : N.atom (N.mate y) ∈ U
        · rcases ihP y ⟨hyU, hwU⟩ with ⟨m, hm, hmy⟩ | hab'
          · exact Or.inl ⟨m, List.mem_append_left _ hm, hmy⟩
          · rcases Sym2.eq_iff.mp hab' with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rcases hb (N.mate y) h2 with h | h
              · exact Or.inl ⟨_, hmemt, inGroup_mate_iff.mp h⟩
              · exfalso; apply haT; have := h.2; rwa [N.mate_mate, h1] at this
            · rcases hb y h1 with h | h
              · exact Or.inl ⟨_, hmemt, h⟩
              · exfalso; apply haT; have := h.2; rwa [h2] at this
        · have hwT : N.atom (N.mate y) ∈ T := (Finset.mem_union.mp hy.2).resolve_left hwU
          have hwb : N.atom (N.mate y) ≠ q := fun h => hwU (h ▸ hbU)
          by_cases hwc : N.atom (N.mate y) = c
          · by_cases hva : N.atom y = a
            · exact Or.inr (by rw [hva, hwc])
            · by_cases hvb : N.atom y = q
              · rcases hb y hvb with h | h
                · exact absurd (htU h.2) hwU
                · exact Or.inl ⟨_, hmemT, h⟩
              · exact absurd (ihI _ hyU hva hvb y rfl) hwU
          · have h4 := inGroup_of_degIn_four hN (hBT.1 hwT) (hBT.2.2.2.2.2.2.2.2.1 _ hwT hwb hwc)
              (rfl : N.atom (N.mate y) = _)
            have hvT : N.atom y ∈ T := by have := h4.2; rwa [N.mate_mate] at this
            have hvb : N.atom y = q := by
              have : N.atom y ∈ U ∩ T := Finset.mem_inter.mpr ⟨hyU, hvT⟩
              rw [hi] at this
              exact Finset.mem_singleton.mp this
            rcases hb y hvb with h | h
            · exact absurd (htU h.2) hwU
            · exact Or.inl ⟨_, hmemT, h⟩
      intro y hy
      by_cases hyU : N.atom y ∈ U
      · exact key y hy hyU
      · by_cases hwU : N.atom (N.mate y) ∈ U
        · rcases key (N.mate y) (inGroup_mate_iff.mpr hy) hwU with ⟨m, hm, hmy⟩ | h
          · exact Or.inl ⟨m, hm, inGroup_mate_iff.mp hmy⟩
          · right
            rw [N.mate_mate] at h
            rw [Sym2.eq_swap]
            exact h
        · exact Or.inl ⟨_, hmemT, (Finset.mem_union.mp hy.1).resolve_left hyU,
            (Finset.mem_union.mp hy.2).resolve_left hwU⟩
    · intro x hx hxa hxc y hy
      by_cases hxb : x = q
      · rw [hxb] at hy
        rcases hb y hy with h | h
        · exact Finset.mem_union_left _ (htU h.2)
        · exact Finset.mem_union_right _ h.2
      rcases Finset.mem_union.mp hx with hxU | hxT
      · exact Finset.mem_union_left _ (ihI x hxU hxa hxb y hy)
      · exact Finset.mem_union_right _
          (inGroup_of_degIn_four hN (hBT.1 hxT) (hBT.2.2.2.2.2.2.2.2.1 x hxT hxb hxc) hy).2

/-- **Every bond of a block cut into a spine is a bond of one member.** -/
theorem spine_bonds_block (hN : N.IsMolecule) {L : List (Finset V × V × V)} {S : Finset V} {a b : V}
    (hs : Spine N L S a b) (hB : N.IsBlock S a b) :
    ∀ y, N.InGroup S y → ∃ m ∈ L, N.InGroup m.1 y := by
  classical
  intro y hy
  rcases (spine_bonds hN hs).1 y hy with h | hab
  · exact h
  obtain ⟨⟨T0, p0, q0⟩, L1, hL⟩ := List.exists_cons_of_ne_nil hs.ne_nilMK
  subst hL
  have hp0 : p0 = a := hs.cons_fstMK
  obtain ⟨⟨X0, hX0⟩, hT0S⟩ := hs.mem_vine (List.mem_cons_self ..)
  have hB0 : N.IsBlock T0 a q0 := hp0 ▸ hX0.1
  -- the end of `y` at `a`
  obtain ⟨ya, hya, hyaS, hback⟩ : ∃ ya, N.atom ya = a ∧ N.InGroup S ya ∧ (N.InGroup T0 ya → N.InGroup T0 y) := by
    rcases Sym2.eq_iff.mp hab with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact ⟨y, h1, hy, id⟩
    · exact ⟨N.mate y, h2, inGroup_mate_iff.mpr hy, inGroup_mate_iff.mp⟩
  obtain ⟨o0, ho0, ho0g, ho0o, -⟩ := block_unique_dart hB0 (N.out ya)
  obtain ⟨s0, -, -, -, huniq⟩ := block_unique_dart hB (N.out ya)
  have h1 := huniq ya hya hyaS rfl
  have h2 := huniq o0 ho0 ⟨hT0S ho0g.1, hT0S ho0g.2⟩ ho0o
  exact ⟨_, List.mem_cons_self .., hback (h1.trans h2.symm ▸ ho0g)⟩

end generic

variable {R : ℕ} {G : Garden (2 * R)}

/-- **The bonds of a group with an ingredient** (VC or HVC): every bond of the group is a bond of one of its
ingredients, except the added bond `E` of an HVC (at most one dart of `E` at each atom). -/
theorem ingredient_bonds (hM : G.molecule.IsMolecule) {W A : Finset (GBranch G.tree)}
    (hI : IsIngredient G.molecule W A) :
    ∃ E : Finset (GardenDart G), (∀ y ∈ E, ∀ y' ∈ E, G.molecule.atom y = G.molecule.atom y' → y = y') ∧
      ∀ y, G.molecule.InGroup W y → y ∉ E → ∃ I, IsIngredient G.molecule W I ∧ G.molecule.InGroup I y := by
  classical
  rcases hI with ⟨a, b, n, x, y, hB, hCI⟩ | ⟨a, b, e, n, x, y, hends, hn2, hBe, hCI⟩
  · obtain ⟨L, hs⟩ := Spine.of_chain (Vine.chainIngredient_spec hCI).1
    refine ⟨∅, by simp, fun z hz _ => ?_⟩
    obtain ⟨⟨T, p, q⟩, hm, hmz⟩ := spine_bonds_block hM hs hB z hz
    exact ⟨T, Or.inl ⟨a, b, L.length, p, q, hB, hs.ingredient_of_mem hm⟩, hmz⟩
  · have hab : a ≠ b := hBe.2.2.2.1
    have hne : G.molecule.atom e ≠ G.molecule.atom (G.molecule.mate e) := by
      intro h
      unfold Molecule.ends at hends
      rw [h] at hends
      rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hab (h1.symm.trans h2)
      · exact hab (h2.symm.trans h1)
    have hN := Vine.eraseBond_isMolecule G.molecule hM e hne
    obtain ⟨L, hs, hlen⟩ := Spine.of_chain_len (Vine.chainIngredient_spec hCI).1
    have hlen2 : 2 ≤ L.length := hlen ▸ hn2
    refine ⟨{e, G.molecule.mate e}, ?_, ?_⟩
    · intro y1 hy1 y2 hy2 h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy1 hy2
      rcases hy1 with rfl | rfl <;> rcases hy2 with rfl | rfl
      · rfl
      · exact absurd h hne
      · exact absurd h.symm hne
      · rfl
    · intro z hz hzE
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzE
      obtain ⟨⟨T, p, q⟩, hm, hmz⟩ := spine_bonds_block hN hs hBe ⟨z, hzE.1, hzE.2⟩ hz
      exact ⟨T, Or.inr ⟨a, b, e, L.length, p, q, hends, hlen2, hBe, hs.ingredient_of_mem hm⟩, hmz⟩

/-- A lifted bond of `G_sb` is not a bond inside a unit (units are collapsed). -/
theorem od_not_internal (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)} {u : CLBlock G}
    (hu : u ∈ unitBlocks G σ Mk) (x : GardenDart (stSt G σ Mk).G) :
    ¬ G.molecule.InGroup u.atoms ((stSt G σ Mk).M.od x) := by
  intro hin
  have := ((stSt G σ Mk).M.od_range ((stSt G σ Mk).M.od x)).mp ⟨x, rfl⟩
  exact this ⟨u.upper, stSt_cls_memMk (Mk := Mk) hM σ hu hin.1, stSt_cls_memMk (Mk := Mk) hM σ hu hin.2⟩

/-- `ContainsDart` is closed under `mate`. -/
theorem containsDart_mateMk {w : ℕ} {G' : Garden w} (O : Object G'.molecule) {z : GardenDart G'}
    (h : O.ContainsDart z) : O.ContainsDart (G'.molecule.mate z) := by
  unfold Object.ContainsDart at h ⊢
  rcases hs : O.shape with c | R
  · rw [hs] at h
    exact ⟨by simpa [G'.molecule.mate_mate] using h.2, by simpa [G'.molecule.mate_mate] using h.1⟩
  · rw [hs] at h
    obtain ⟨a1, a2, a3⟩ := h
    refine ⟨fun e => a2 (by rw [← G'.molecule.mate_mate z, e]), fun e => a1 (by
      have := congrArg G'.molecule.mate e
      rwa [G'.molecule.mate_mate, G'.molecule.mate_mate] at this),
      ⟨by simpa [G'.molecule.mate_mate] using a3.2, by simpa [G'.molecule.mate_mate] using a3.1⟩⟩

/-- **o75 Theorem 7.5′(6′) for the marked splice**: an object of `G_sb` containing a survivor joint lies in a
survivor, shares a bond with a survivor, or has a hinge in configuration (6). -/
theorem meetB_atomsMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
    (P : Object (stSt G σ Mk).G.molecule)
    (hmeet : ∃ t, ∃ ht : t ∈ survivorsMk G σ Mk, (survObj ht).upper ∈ P.atoms ∨ (survObj ht).lower ∈ P.atoms) :
    (∃ t, ∃ ht : t ∈ survivorsMk G σ Mk, P.atoms ⊆ (survObj ht).atoms) ∨
    (∃ t, ∃ ht : t ∈ survivorsMk G σ Mk, ∃ x, P.ContainsDart x ∧ (survObj ht).ContainsDart x) ∨
    ∃ v ∈ (collectionChoices G σ Mk).hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair ((collectionChoices G σ Mk).first v) ((collectionChoices G σ Mk).second v)
            (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y)))) := by
  classical
  by_cases h2 : ∃ t, ∃ ht : t ∈ survivorsMk G σ Mk, ∃ x, P.ContainsDart x ∧ (survObj ht).ContainsDart x
  · exact Or.inr (Or.inl h2)
  by_cases hcon : ∃ v ∈ (collectionChoices G σ Mk).hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair ((collectionChoices G σ Mk).first v) ((collectionChoices G σ Mk).second v)
            (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))
  · exact Or.inr (Or.inr hcon)
  exfalso
  -- every hinge of `P` is aligned: main's substitution applies
  have hjoint : ∀ v ∈ (stSt G σ Mk).hinges, v ∈ P.atoms → v = P.upper ∨ v = P.lower := by
    intro v hv hvP
    by_contra h
    push Not at h
    exact hcon ⟨v, hv, hvP, Or.inl h⟩
  have hnx : ∀ v ∈ (stSt G σ Mk).hinges, v ∈ P.atoms → ∀ x y, hingePair G σ v = some (x, y) →
      (P.ContainsDart x ↔ P.ContainsDart y) := by
    intro v hv hvP x y hp
    by_contra hne
    apply hcon
    refine ⟨v, hv, hvP, Or.inr ⟨hjoint v hv hvP, x, y, by simp [collectionChoices, hp],
      by simp [collectionChoices, hp], ?_⟩⟩
    by_cases hx : P.ContainsDart x
    · exact Or.inl ⟨hx, fun hy => hne ⟨fun _ => hy, fun _ => hx⟩⟩
    · have hy : P.ContainsDart y := by
        by_contra hy
        exact hne ⟨fun h => absurd h hx, fun h => absurd h hy⟩
      exact Or.inr ⟨hy, hx⟩
  have hK : ∀ v, v ∈ P.atoms → v ∈ (stSt G σ Mk).hinges → ∃ j, (v = P.upper ∨ v = P.lower) ∧
      ∃ u ∈ unitBlocks G σ Mk, (stSt G σ Mk).M.ob v = u.upper ∧ (j = u.upper ∨ j = u.lower) ∧
        ∀ x, (stSt G σ Mk).G.molecule.atom x = v → P.ContainsDart x →
          G.molecule.atom ((stSt G σ Mk).M.od x) = j := by
    intro v hvP hvh
    obtain ⟨u, hu, hob, j, hj, hx⟩ := hinge_common_jointMk hM σ P hvh (hjoint v hvh hvP) (hnx v hvh hvP)
    exact ⟨j, hjoint v hvh hvP, u, hu, hob, hj, hx⟩
  let jf : GBranch (stSt G σ Mk).G.tree → GBranch G.tree := fun c =>
    if h : c ∈ P.atoms ∧ c ∈ (stSt G σ Mk).hinges then Classical.choose (hK c h.1 h.2) else (stSt G σ Mk).M.ob c
  have hjnon : ∀ c ∈ P.atoms, c ∉ (stSt G σ Mk).hinges → jf c = (stSt G σ Mk).M.ob c := by
    intro c hc hch
    simp only [jf]
    rw [dif_neg (fun h => hch h.2)]
  have hjsp : ∀ w ∈ P.atoms, w ∈ (stSt G σ Mk).hinges → (w = P.upper ∨ w = P.lower) ∧
      ∃ u ∈ unitBlocks G σ Mk, (stSt G σ Mk).M.ob w = u.upper ∧ (jf w = u.upper ∨ jf w = u.lower) ∧
        ∀ x, (stSt G σ Mk).G.molecule.atom x = w → P.ContainsDart x →
          G.molecule.atom ((stSt G σ Mk).M.od x) = jf w := by
    intro w hw hwh
    have := Classical.choose_spec (hK w hw hwh)
    simp only [jf]
    rw [dif_pos ⟨hw, hwh⟩]
    exact this
  have hKd : KDataMk σ P jf := hjsp
  -- the substituted object is vine-like in `G`
  have hTv : IsVineLikeSet G.molecule (P.atoms.image jf) := by
    by_cases hend : ∃ w, (w = P.upper ∨ w = P.lower) ∧ w ∈ (stSt G σ Mk).hinges
    · exact ⟨_, _, Or.inr (Or.inl (cross_isvcMk hM σ P jf hjnon hKd hend))⟩
    · have hdis : Disjoint P.atoms (stSt G σ Mk).hinges :=
        Finset.disjoint_left.mpr fun v hv hvh => hend ⟨v, hjoint v hvh hv, hvh⟩
      have hB := nohinge_unmergedMk σ hdis
      obtain ⟨I, hIπ, -⟩ := exists_iso_down (stSt G σ Mk).M (stSt G σ Mk).hcls P.atoms hB
      have := isVineLikeSet_of_object (I.mapObj P (subset_refl _))
      rw [InducedIso.mapObj_atoms, hIπ] at this
      have himg : P.atoms.image jf = P.atoms.image (stSt G σ Mk).M.ob :=
        Finset.image_congr (fun c hc => hjnon c hc (Finset.disjoint_left.mp hdis hc))
      rw [himg]
      exact this
  obtain ⟨g, hg, hBg⟩ := cover_group hM hTv
  have hjg : ∀ c ∈ P.atoms, jf c ∈ g := fun c hc => hBg (Finset.mem_image_of_mem _ hc)
  have hpij : ∀ c ∈ P.atoms, (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (jf c) = c := by
    intro c hc
    by_cases hch : c ∈ (stSt G σ Mk).hinges
    · obtain ⟨-, u, hu, hob, hj, -⟩ := hjsp c hc hch
      have hjm : jf c ∈ u.atoms := by rcases hj with h | h <;> rw [h]; exacts [u.isBlock.2.1, u.isBlock.2.2.1]
      exact pi_of_crown hM σ hu hob hjm
    · rw [hjnon c hc hch]
      exact pi_obMk σ (by by_contra hne; exact hch (((stSt G σ Mk).mem_hinges c).mpr hne))
  have hod : ∀ x, P.ContainsDart x →
      G.molecule.atom ((stSt G σ Mk).M.od x) = jf ((stSt G σ Mk).G.molecule.atom x) := by
    intro x hx
    have hxP : (stSt G σ Mk).G.molecule.atom x ∈ P.atoms := (inGroup_of_containsDart P hx).1
    by_cases hch : (stSt G σ Mk).G.molecule.atom x ∈ (stSt G σ Mk).hinges
    · obtain ⟨-, u, -, -, -, hKw⟩ := hjsp _ hxP hch
      exact hKw x rfl hx
    · rw [hjnon _ hxP hch]
      have hcn : (stSt G σ Mk).cls ((stSt G σ Mk).M.ob ((stSt G σ Mk).G.molecule.atom x)) = none := by
        by_contra hne
        exact hch (((stSt G σ Mk).mem_hinges _).mpr hne)
      apply eq_of_pi_eq_unmerged hM σ hcn
      rw [pi_obMk σ hcn]
      exact (atom_lift hM σ).symm
  -- the group of the met survivor joint
  obtain ⟨t, ht, hJ⟩ := hmeet
  obtain ⟨-, hup, hlo, -⟩ := survObj_spec ht
  obtain ⟨W, hW, hσW, hmkW, htm, htW⟩ := survivorsMk_group ht
  obtain ⟨⟨Xt, hXt⟩, -, -⟩ := (markedUnitsOfMK hmkW).surv_spec t htm
  have hgW : g = W := by
    obtain ⟨J, hJP, z, hzt, hJz⟩ : ∃ J ∈ P.atoms, ∃ z ∈ t.1, (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z = J := by
      rcases hJ with h | h
      · exact ⟨_, h, t.2.1, hXt.1.2.1, hup.symm⟩
      · exact ⟨_, h, t.2.2, hXt.1.2.2.1, hlo.symm⟩
    have hzW := htW hzt
    have hjW : jf J ∈ W := by
      by_cases he : jf J = z
      · rw [he]; exact hzW
      · obtain ⟨u, hu, -, hu2⟩ := run_of_pi_eq hM σ hW hmkW hzW (Ne.symm he) (hJz.trans (hpij J hJP).symm)
        exact (markedUnitsOfMK hmkW).sub u hu hu2
    by_contra hne
    exact Finset.disjoint_left.mp (groups_disjoint hM hg hW hne) (hjg J hJP) hjW
  subst hgW
  -- the bonds of the marked group
  obtain ⟨c0, -, -, hc0I⟩ := id hmkW
  obtain ⟨E, hE1, hE2⟩ := ingredient_bonds hM hc0I
  -- a bond of `P` at its upper joint that is not the added bond
  obtain ⟨ao, hao, hao_c, hao_o, -⟩ := contained_unique (stSt G σ Mk).G P (Or.inl rfl) true
  obtain ⟨ai, hai, hai_c, hai_o, -⟩ := contained_unique (stSt G σ Mk).G P (Or.inl rfl) false
  obtain ⟨x, hxP, hxE⟩ : ∃ x, P.ContainsDart x ∧ (stSt G σ Mk).M.od x ∉ E := by
    by_cases h1 : (stSt G σ Mk).M.od ao ∈ E
    · refine ⟨ai, hai_c, fun h2 => ?_⟩
      have e1 := hE1 _ h1 _ h2 (by rw [hod ao hao_c, hod ai hai_c, hao, hai])
      have := congrArg G.molecule.out e1
      rw [(stSt G σ Mk).M.od_out, (stSt G σ Mk).M.od_out, hao_o, hai_o] at this
      cases this
    · exact ⟨ao, hao_c, h1⟩
  have hxW : G.molecule.InGroup g ((stSt G σ Mk).M.od x) := by
    have hmP := containsDart_mateMk P hxP
    refine ⟨?_, ?_⟩
    · rw [hod x hxP]; exact hjg _ (inGroup_of_containsDart P hxP).1
    · rw [← (stSt G σ Mk).M.od_mate, hod _ hmP]
      exact hjg _ (inGroup_of_containsDart P hmP).1
  obtain ⟨I, hIW, hxI⟩ := hE2 _ hxW hxE
  -- the ingredient is a survivor (a run is collapsed)
  obtain ⟨t', ht', hIt⟩ : ∃ t' ∈ (markedUnitsOfMK hmkW).surv, t'.1 = I := by
    by_cases hV : ∃ c ∈ vinesV G, c.atoms = I
    · obtain ⟨c, hcV, hcI⟩ := hV
      by_cases hcMk : c ∈ Mk
      · obtain ⟨t', ht', h'⟩ := (markedUnitsOfMK hmkW).surv_cover c hcMk hcV (hcI ▸ hIW)
        exact ⟨t', ht', h'.trans hcI⟩
      · exfalso
        obtain ⟨u, hu, hcu⟩ := (markedUnitsOfMK hmkW).cover c hcV hcMk (hcI ▸ hIW)
        have huB : u ∈ unitBlocks G σ Mk :=
          mem_unitBlocksMk.mpr ⟨g, hW, hσW, (groupUnitsMk_of_markedMK hmkW).symm ▸ hu⟩
        exact od_not_internal hM σ huB x ⟨hcu (hcI ▸ hxI.1), hcu (hcI ▸ hxI.2)⟩
    · exact (markedUnitsOfMK hmkW).surv_skip I hIW (fun c hc hcI => hV ⟨c, hc, hcI⟩)
  have ht'm : t' ∈ survivorsMk G σ Mk := mem_survivorsMk_iffMK.mpr ⟨g, hW, hσW, hmkW, ht'⟩
  exact h2 ⟨t', ht'm, x, hxP, survObj_containsDart hM σ ht'm (hIt ▸ hxI)⟩

end WaveTurbulence.VineA.NormalizedSplice.Subpro
