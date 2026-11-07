/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C5VineG
import Mathlib.Tactic

/-! # Prop 9.6, case (5): assembling `IsVine .II` for `M₀` -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem post_loopfree {N : Molecule V D} (T : TwoExit N) (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) :
    ∀ z, T.post.atom z ≠ T.post.atom (T.post.mate z) := by
  intro z
  rcases z with z | b
  · exact hloop z.val
  · cases b
    · exact fun h => T.far (show T.c = T.d from h)
    · exact fun h => T.far (show T.c = T.d from h.symm)

/-- The atoms of the post molecule of the second chain. -/
theorem post_atoms_iff {M : Molecule V D} {a₀ b₀ : V} (Tb : TwoExit (Degen.eraseAtoms M {a₀}))
    (hTbY : Tb.Y = {b₀}) (v : V) :
    v ∈ Tb.post.atoms ↔ (v ∈ M.atoms ∧ v ≠ a₀ ∧ v ≠ b₀) := by
  rw [Tb.post_atoms, hTbY]
  change v ∈ (M.atoms \ {a₀}) \ {b₀} ↔ _
  simp [and_assoc]

/-- The degree of an atom of the post molecule. -/
theorem post_deg_formula {M : Molecule V D} {a₀ b₀ : V} (Ta : TwoExit M) (hTaY : Ta.Y = {a₀})
    (Tb : TwoExit (Degen.eraseAtoms M {a₀})) (hTbY : Tb.Y = {b₀}) (hne : Ta.c ≠ Ta.d) {v : V}
    (hv : v ∈ Tb.post.atoms) (h4 : M.deg v = 4) :
    Tb.post.deg v = 4 - (if v = Ta.c then 1 else 0) - (if v = Ta.d then 1 else 0) := by
  have hvb : v ∉ Tb.Y := by rw [Tb.post_atoms] at hv; exact (mem_sdiff.mp hv).2
  rw [Tb.post_deg hvb]
  have hva : v ∉ Ta.Y := by
    rw [hTaY]; have := (post_atoms_iff Tb hTbY v).mp hv; simpa using this.2.1
  have h1 := deg_eraseAtoms_add (N := M) Ta.Y hva
  rw [Ta.removedDartsAt_eq hva] at h1
  have hN : (Degen.eraseAtoms M Ta.Y).deg v = (Degen.eraseAtoms M {a₀}).deg v := by rw [hTaY]
  rw [← hN]
  by_cases hc : v = Ta.c <;> by_cases hd : v = Ta.d
  · exact absurd (hc.symm.trans hd) hne
  · simp [hc, hd, hne, hne.symm] at h1 h4 ⊢; omega
  · simp [hc, hd, hne, hne.symm] at h1 h4 ⊢; omega
  · simp [hc, hd, hne, hne.symm] at h1 h4 ⊢; omega


theorem bb_erase_le_two' (M : Molecule V D) (K : Finset V) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (h2 : ∀ p q, M.bondsBetween p q ≤ 2) (p q : V) : (Degen.eraseAtoms M K).bondsBetween p q ≤ 2 := by
  by_cases hpq : p = q
  · subst hpq
    rw [bondsBetween_self_eq_zero (fun z => hloop z.val)]; omega
  · exact (bondsBetween_eraseAtoms_le M K hpq).trans (h2 p q)

theorem expand_n (k : ℕ) : (VineType.II.expand [k]).n = 4 + 2 * k := by
  by_cases hk : k = 0
  · subst hk; simp [VineType.expand, VineType.template, insertRungs]
  · simp [VineType.expand, VineType.template, insertRungs, hk]

/-- The degree of a vertex in the image multiset. -/
theorem card_filter_map_mem {G : Multiset (Sym2 V)} {A : Finset V} {f : V → ℕ} (hinj : Set.InjOn f ↑A)
    (hG : ∀ e ∈ G, ∃ a ∈ A, ∃ b ∈ A, e = s(a, b)) {g : V} (hg : g ∈ A) :
    Multiset.card ((G.map (Sym2.map f)).filter (fun e => f g ∈ e)) = Multiset.card (G.filter (fun e => g ∈ e)) := by
  classical
  rw [Multiset.filter_map, Multiset.card_map]
  congr 1
  refine Multiset.filter_congr fun e he => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := hG e he
  simp only [Function.comp, Sym2.map_mk, Sym2.mem_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (hinj hg ha h).symm.symm
    · exact Or.inr (hinj hg hb h)
  · rintro (h | h) <;> simp [h]

theorem endsA_ne_endsB (k : ℕ) : labA k k ≠ labB k k := by
  simp only [labA, labB]; split_ifs <;> omega

theorem endsA_range (k : ℕ) : labA k k ∈ Finset.range (4 + 2 * k) \ {0, 1} := by
  rw [mem_sdiff]; simp only [labA, mem_range, mem_insert, mem_singleton]; by_cases h : k = 0 <;> simp [h] <;> omega

theorem endsB_range (k : ℕ) : labB k k ∈ Finset.range (4 + 2 * k) \ {0, 1} := by
  rw [mem_sdiff]; simp only [labB, mem_range, mem_insert, mem_singleton]; by_cases h : k = 0 <;> simp [h] <;> omega


theorem isVine_of_halfClosure {M : Molecule V D} (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) (hle2 : ∀ p q, M.bondsBetween p q ≤ 2)
    {a₀ b₀ : V} (ha₀ : a₀ ∈ M.atoms) (hb₀ : b₀ ∈ M.atoms) (hab : a₀ ≠ b₀)
    (hdir_a : M.outdeg a₀ = 1 ∧ M.indeg a₀ = 1) (hdir_b : M.outdeg b₀ = 1 ∧ M.indeg b₀ = 1)
    (hdeg4 : ∀ v ∈ M.atoms, v ≠ a₀ → v ≠ b₀ → M.deg v = 4)
    (Ta : TwoExit M) (hTaY : Ta.Y = {a₀}) (ha_all : ∀ x, M.atom x = a₀ → x = Ta.x ∨ x = Ta.y)
    (Tb : TwoExit (Degen.eraseAtoms M {a₀})) (hTbY : Tb.Y = {b₀})
    (hb_all : ∀ x : D, M.atom x = b₀ → x = Tb.x.val ∨ x = Tb.y.val)
    (hnadj : Ta.c ≠ b₀ ∧ Ta.d ≠ b₀) (H : IsVineIIHalfClosure Tb.post) :
    M.IsVine VineType.II M.atoms b₀ a₀ := by
  classical
  obtain ⟨k, f, hinj, himg, hbonds⟩ := H
  have hPat := post_atoms_iff Tb hTbY
  have hcP : Tb.c ∈ Tb.post.atoms := by rw [Tb.post_atoms]; exact Tb.c_mem
  have hdP : Tb.d ∈ Tb.post.atoms := by rw [Tb.post_atoms]; exact Tb.d_mem
  have hcP' := (hPat _).mp hcP
  have hdP' := (hPat _).mp hdP
  have hu1M : Ta.c ∈ M.atoms ∧ Ta.c ≠ a₀ := by
    have := Ta.c_mem; rw [hTaY] at this; simpa using this
  have hu2M : Ta.d ∈ M.atoms ∧ Ta.d ≠ a₀ := by
    have := Ta.d_mem; rw [hTaY] at this; simpa using this
  have hu1P : Ta.c ∈ Tb.post.atoms := (hPat _).mpr ⟨hu1M.1, hu1M.2, hnadj.1⟩
  have hu2P : Ta.d ∈ Tb.post.atoms := (hPat _).mpr ⟨hu2M.1, hu2M.2, hnadj.2⟩
  have hax : M.atom Ta.x = a₀ := by have := Ta.atom_x; rw [hTaY] at this; simpa using this
  have hay : M.atom Ta.y = a₀ := by have := Ta.atom_y; rw [hTaY] at this; simpa using this
  have hbx : M.atom Tb.x.val = b₀ := by have := Tb.atom_x; rw [hTbY] at this; exact mem_singleton.mp this
  have hby : M.atom Tb.y.val = b₀ := by have := Tb.atom_y; rw [hTbY] at this; exact mem_singleton.mp this
  have h3 : ∀ q, M.bondsBetween a₀ q = (if q = Ta.c then 1 else 0) + (if q = Ta.d then 1 else 0) := by
    intro q
    rw [bb_two_darts M hloop hax hay Ta.ne ha_all q]
    simp only [TwoExit.c, TwoExit.d, eq_comm (a := q)]
  have h4 : ∀ q, M.bondsBetween b₀ q = (if q = Tb.c then 1 else 0) + (if q = Tb.d then 1 else 0) := by
    intro q
    rw [bb_two_darts M hloop hbx hby (fun h => Tb.ne (Subtype.ext h)) hb_all q]
    simp only [TwoExit.c, TwoExit.d, eq_comm (a := q)]
    rfl
  have h1 : ∀ p q, (p ∈ M.atoms ∧ p ≠ a₀ ∧ p ≠ b₀) → (q ∈ M.atoms ∧ q ≠ a₀ ∧ q ≠ b₀) →
      Tb.post.bondsBetween p q = M.bondsBetween p q + (if s(Tb.d, Tb.c) = s(p, q) then 1 else 0) := by
    intro p q hp hq
    have hpY : p ∉ Tb.Y := by rw [hTbY]; simpa using hp.2.2
    have hqY : q ∉ Tb.Y := by rw [hTbY]; simpa using hq.2.2
    have hpa : p ∉ ({a₀} : Finset V) := by simpa using hp.2.1
    have hqa : q ∉ ({a₀} : Finset V) := by simpa using hq.2.1
    change (Mole.addBond (Degen.eraseAtoms (Degen.eraseAtoms M {a₀}) Tb.Y) Tb.d Tb.c).bondsBetween p q = _
    rw [addBond_bondsBetween, Degen.bondsBetween_erase_eq _ Tb.Y hpY hqY, Degen.bondsBetween_erase_eq M {a₀} hpa hqa]
  have h2 : ∀ p q, ¬ ((p ∈ M.atoms ∧ p ≠ a₀ ∧ p ≠ b₀) ∧ (q ∈ M.atoms ∧ q ≠ a₀ ∧ q ≠ b₀)) →
      Tb.post.bondsBetween p q = 0 := by
    intro p q hn
    by_cases hp : p ∈ Tb.post.atoms
    · have hq : q ∉ Tb.post.atoms := fun hq => hn ⟨(hPat _).mp hp, (hPat _).mp hq⟩
      rw [Degen.bondsBetween_comm]; exact bb_zero_of_not_mem _ hq p
    · exact bb_zero_of_not_mem _ hp q
  have hid := bb_identity M.atoms M.bondsBetween Tb.post.bondsBetween a₀ b₀ Tb.c Tb.d Ta.c Ta.d
    (Degen.bondsBetween_comm M) (Degen.bondsBetween_comm _) hab ha₀ hb₀ hcP' hdP'
    ⟨hu1M.1, hu1M.2, hnadj.1⟩ ⟨hu2M.1, hu2M.2, hnadj.2⟩ h1 h2 h3 h4
    (fun p q hp => bb_zero_of_not_mem M hp q)
  have hmulti := multiset_identity M Tb.post a₀ b₀ Tb.c Tb.d Ta.c Ta.d hid
  -- loop-freeness and bond bounds
  have hloopN : ∀ z, (Degen.eraseAtoms M {a₀}).atom z ≠ (Degen.eraseAtoms M {a₀}).atom ((Degen.eraseAtoms M {a₀}).mate z) :=
    fun z => hloop z.val
  have hloopP := post_loopfree Tb hloopN
  have hleN := bb_erase_le_two' M {a₀} hloop hle2
  have hleE := bb_erase_le_two' (Degen.eraseAtoms M {a₀}) Tb.Y hloopN hleN
  have hf_img : ∀ v ∈ Tb.post.atoms, 2 ≤ f v ∧ f v < 4 + 2 * k := by
    intro v hv
    have : f v ∈ Tb.post.atoms.image f := mem_image_of_mem f hv
    rw [himg] at this
    rw [mem_sdiff] at this
    simp only [mem_range, mem_insert, mem_singleton] at this
    omega
  -- the triple bond is the new bond
  obtain ⟨p, hp, q, hq, hfp, hfq, h3⟩ := triple_of_data hinj himg hbonds
  have hbbP : ∀ p q, Tb.post.bondsBetween p q =
      (Degen.eraseAtoms (Degen.eraseAtoms M {a₀}) Tb.Y).bondsBetween p q + (if s(Tb.d, Tb.c) = s(p, q) then 1 else 0) :=
    fun p q => addBond_bondsBetween _ _ _ _ _
  have hdc : s(Tb.d, Tb.c) = s(p, q) := by
    by_contra hn
    rw [hbbP, if_neg hn] at h3
    have := hleE p q; omega
  have hf23 : s(f Tb.d, f Tb.c) = s(2, 3) := by
    rcases Sym2.eq_iff.mp hdc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hfp, hfq]
    · rw [h1, h2, hfp, hfq, Sym2.eq_swap]
  -- the degree-three atoms
  have hne_u : Ta.c ≠ Ta.d := Ta.far
  have hmapDeg : ∀ g ∈ Tb.post.atoms, Tb.post.deg g = ladderDeg k (f g) := by
    intro g hg
    rw [deg_eq_card_bonds Tb.post hloopP g]
    have := card_filter_map_mem (G := Tb.post.groupBonds Tb.post.atoms) (A := Tb.post.atoms) hinj
      (fun e he => mem_groupBonds_atoms he) hg
    rw [hbonds, halfClosureIIBonds_eq] at this
    exact this.symm
  have hends : ∀ j ∈ Finset.range (4 + 2 * k) \ {0, 1}, ∃ g ∈ Tb.post.atoms, f g = j := by
    intro j hj
    rw [← himg] at hj
    obtain ⟨g, hg, rfl⟩ := mem_image.mp hj
    exact ⟨g, hg, rfl⟩
  obtain ⟨g, hg, hfg⟩ := hends _ (endsA_range k)
  obtain ⟨h, hh, hfh⟩ := hends _ (endsB_range k)
  have hdegP : ∀ v ∈ Tb.post.atoms, Tb.post.deg v =
      4 - (if v = Ta.c then 1 else 0) - (if v = Ta.d then 1 else 0) := fun v hv =>
    post_deg_formula Ta hTaY Tb hTbY hne_u hv (hdeg4 v ((hPat v).mp hv).1 ((hPat v).mp hv).2.1 ((hPat v).mp hv).2.2)
  have hg3 : g = Ta.c ∨ g = Ta.d := by
    have h1 := hdegP g hg
    rw [hmapDeg g hg, hfg, ladderDeg_end_a] at h1
    by_contra hn; push Not at hn
    simp [hn.1, hn.2] at h1
  have hh3 : h = Ta.c ∨ h = Ta.d := by
    have h1 := hdegP h hh
    rw [hmapDeg h hh, hfh, ladderDeg_end_b] at h1
    by_contra hn; push Not at hn
    simp [hn.1, hn.2] at h1
  have hgh : g ≠ h := fun e => endsA_ne_endsB k (by rw [← hfg, ← hfh, e])
  have hu : (f Ta.c = labA k k ∧ f Ta.d = labB k k) ∨ (f Ta.c = labB k k ∧ f Ta.d = labA k k) := by
    rcases hg3 with e1 | e1 <;> rcases hh3 with e2 | e2
    · exact absurd (e1.trans e2.symm) hgh
    · left; rw [← e1, ← e2]; exact ⟨hfg, hfh⟩
    · right; rw [← e1, ← e2]; exact ⟨hfh, hfg⟩
    · exact absurd (e1.trans e2.symm) hgh
  -- the labelling of `M₀`
  let f' : V → ℕ := fun v => if v = b₀ then 0 else if v = a₀ then 1 else f v
  have hf'P : ∀ v ∈ Tb.post.atoms, f' v = f v := by
    intro v hv
    have := (hPat v).mp hv
    simp [f', this.2.2, this.2.1]
  have hf'b : f' b₀ = 0 := by simp [f']
  have hf'a : f' a₀ = 1 := by simp [f', hab]
  have key : ∀ v ∈ M.atoms, (v = b₀ ∧ f' v = 0) ∨ (v = a₀ ∧ f' v = 1) ∨ (v ∈ Tb.post.atoms ∧ f' v = f v ∧ 2 ≤ f v) := by
    intro v hv
    by_cases hvb : v = b₀
    · exact Or.inl ⟨hvb, by rw [hvb]; exact hf'b⟩
    by_cases hva : v = a₀
    · exact Or.inr (Or.inl ⟨hva, by rw [hva]; exact hf'a⟩)
    have hvP : v ∈ Tb.post.atoms := (hPat v).mpr ⟨hv, hva, hvb⟩
    exact Or.inr (Or.inr ⟨hvP, hf'P v hvP, (hf_img v hvP).1⟩)
  have hinj' : Set.InjOn f' ↑M.atoms := by
    intro v hv w hw hvw
    simp only [Finset.mem_coe] at hv hw
    rcases key v hv with ⟨e1, f1⟩ | ⟨e1, f1⟩ | ⟨hvP, f1, g1⟩ <;> rcases key w hw with ⟨e2, f2⟩ | ⟨e2, f2⟩ | ⟨hwP, f2, g2⟩
    · rw [e1, e2]
    · omega
    · omega
    · omega
    · rw [e1, e2]
    · omega
    · omega
    · omega
    · exact hinj hvP hwP (by rw [← f1, ← f2]; exact hvw)
  have himg' : M.atoms.image f' = Finset.range (VineType.II.expand [k]).n := by
    rw [expand_n]
    ext j
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rcases key v hv with ⟨_, f1⟩ | ⟨_, f1⟩ | ⟨hvP, f1, _⟩
      · omega
      · omega
      · rw [f1]; exact (hf_img v hvP).2
    · intro hj
      by_cases j0 : j = 0
      · exact ⟨b₀, hb₀, by rw [hf'b, j0]⟩
      by_cases j1 : j = 1
      · exact ⟨a₀, ha₀, by rw [hf'a, j1]⟩
      obtain ⟨g', hg', hfg'⟩ := hends j (by simp only [mem_sdiff, mem_range, mem_insert, mem_singleton]; omega)
      exact ⟨g', ((hPat g').mp hg').1, by rw [hf'P g' hg', hfg']⟩
  -- the bond multiset
  have hmap := congrArg (Multiset.map (Sym2.map f')) hmulti
  simp only [Multiset.map_add, Multiset.map_singleton, Sym2.map_mk] at hmap
  have hGP : (Tb.post.groupBonds Tb.post.atoms).map (Sym2.map f') = halfClosureIIBonds k := by
    rw [← hbonds]
    refine Multiset.map_congr rfl fun e he => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_groupBonds_atoms he
    simp only [Sym2.map_mk, hf'P a ha, hf'P b hb]
  have hdc' : f' Tb.d = f Tb.d := hf'P _ hdP
  have hcc' : f' Tb.c = f Tb.c := hf'P _ hcP
  have hu1' : f' Ta.c = f Ta.c := hf'P _ hu1P
  have hu2' : f' Ta.d = f Ta.d := hf'P _ hu2P
  rw [hGP, hf'b, hf'a, hdc', hcc', hu1', hu2', hf23] at hmap
  have hQ := Q_eq_J k (f Tb.c) (f Tb.d) (f Ta.c) (f Ta.d) hf23 hu
  have hHJ := halfClosure_add_joint k
  have hfin : (M.groupBonds M.atoms).map (Sym2.map f') = Esym k := by
    have e1 : (M.groupBonds M.atoms).map (Sym2.map f') + {s(2, 3)} = Esym k + {s(2, 3)} := by
      rw [hmap, ← hHJ, ← hQ]
    exact add_right_cancel e1
  refine ⟨isBlock_all M hconn hb₀ ha₀ hab.symm hdir_b hdir_a (fun v hv h1 h2 => hdeg4 v hv h2 h1), [k], rfl, f',
    hinj', himg', ?_, hfin⟩
  rw [hf'b, hf'a]

end
end WaveTurbulence.FinalCountG8
