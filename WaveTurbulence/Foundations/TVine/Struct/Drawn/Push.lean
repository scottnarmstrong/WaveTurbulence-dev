/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Basic

/-!
# Multigraphs from bond multisets, and transport of T-vines along explicit bijections (packet L3D)

* `ofMS vs B`: the multigraph on `vs` whose bonds are the elements of `B` lying in `vs.sym2`;
* `pushG H g f`: the image of `H` under `g`, where `f` is a left inverse of `g` on `H.verts`;
* `isTVineU_pushG`: the (Y2)-reduction of the closure to `T` and the bound `mult ≤ 2` transfer along `pushG`
  (the block part is supplied by the caller);
* `isTVineU_of_iso`: a block `G` whose bond multiset is carried by an injective `f` onto the bonds of a T-vine `H`
  is a T-vine.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct.Drawn

open TVine WaveTurbulence.TVine.Core

/-! ## Multigraphs from multisets -/

section ofMS

variable {V : Type*} [DecidableEq V]

/-- The multigraph on `vs` with bond multiset `B` (bonds of `B` with an end outside `vs` are dropped). -/
def ofMS (vs : Finset V) (B : Multiset (Sym2 V)) : UMultigraph V where
  verts := vs
  mult e := if e ∈ vs.sym2 then B.count e else 0
  supp e he x hx := by
    by_cases h : e ∈ vs.sym2
    · exact Finset.mem_sym2_iff.mp h x hx
    · simp [h] at he

theorem ofMS_verts (vs : Finset V) (B : Multiset (Sym2 V)) : (ofMS vs B).verts = vs := rfl

theorem ofMS_mult (vs : Finset V) (B : Multiset (Sym2 V)) (e : Sym2 V) :
    (ofMS vs B).mult e = if e ∈ vs.sym2 then B.count e else 0 := rfl

/-- Every bond of `B` has both ends in `vs`. -/
def WF (vs : Finset V) (B : Multiset (Sym2 V)) : Prop := ∀ e ∈ B, e ∈ vs.sym2

instance (vs : Finset V) (B : Multiset (Sym2 V)) : Decidable (WF vs B) := by
  unfold WF; infer_instance

theorem ofMS_mult_of_wf {vs : Finset V} {B : Multiset (Sym2 V)} (h : WF vs B) (e : Sym2 V) :
    (ofMS vs B).mult e = B.count e := by
  rw [ofMS_mult]
  split_ifs with he
  · rfl
  · exact (Multiset.count_eq_zero.mpr fun hm => he (h e hm)).symm

theorem WF.mono {vs vs' : Finset V} {B : Multiset (Sym2 V)} (h : WF vs B) (hv : vs ⊆ vs') : WF vs' B :=
  fun e he => Finset.mem_sym2_iff.mpr fun x hx => hv (Finset.mem_sym2_iff.mp (h e he) x hx)

theorem WF.add {vs : Finset V} {A B : Multiset (Sym2 V)} (hA : WF vs A) (hB : WF vs B) : WF vs (A + B) := by
  intro e he
  rcases Multiset.mem_add.mp he with h | h
  · exact hA e h
  · exact hB e h

end ofMS

/-! ## Pushforward along a map with a left inverse -/

section push

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- The image of `H` under `g`; `f` is meant to be a left inverse of `g` on `H.verts`. -/
def pushG (H : UMultigraph W) (g : W → V) (f : V → W) : UMultigraph V where
  verts := H.verts.image g
  mult e := if e ∈ (H.verts.image g).sym2 then H.mult (Sym2.map f e) else 0
  supp e he x hx := by
    by_cases h : e ∈ (H.verts.image g).sym2
    · exact Finset.mem_sym2_iff.mp h x hx
    · simp [h] at he

/-- `f` is a left inverse of `g` on `S`. -/
def LInv (S : Finset W) (g : W → V) (f : V → W) : Prop := ∀ w ∈ S, f (g w) = w

theorem LInv.mono {S S' : Finset W} {g : W → V} {f : V → W} (h : LInv S' g f) (hS : S ⊆ S') : LInv S g f :=
  fun w hw => h w (hS hw)

theorem LInv.injOn {S : Finset W} {g : W → V} {f : V → W} (h : LInv S g f) : Set.InjOn g S := by
  intro a ha b hb hab
  rw [← h a ha, ← h b hb]
  exact congrArg f hab

theorem LInv.eq_iff {S : Finset W} {g : W → V} {f : V → W} (h : LInv S g f) {a b : W} (ha : a ∈ S)
    (hb : b ∈ S) : g a = g b ↔ a = b :=
  ⟨fun hh => h.injOn ha hb hh, fun hh => hh ▸ rfl⟩

theorem LInv.mem_image_iff {S T : Finset W} {g : W → V} {f : V → W} (h : LInv S g f) (hT : T ⊆ S) {a : W}
    (ha : a ∈ S) : g a ∈ T.image g ↔ a ∈ T := by
  constructor
  · intro hm
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hm
    rw [← h.injOn (hT hb) ha hba]; exact hb
  · intro hm; exact Finset.mem_image_of_mem g hm

theorem LInv.image_erase {S T : Finset W} {g : W → V} {f : V → W} (h : LInv S g f) (hT : T ⊆ S) {a : W}
    (ha : a ∈ S) : (T.erase a).image g = (T.image g).erase (g a) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨b, ⟨hba, hb⟩, rfl⟩
    exact ⟨fun hh => hba (h.injOn (hT hb) ha hh), b, hb, rfl⟩
  · rintro ⟨hx, b, hb, rfl⟩
    exact ⟨b, ⟨fun hh => hx (hh ▸ rfl), hb⟩, rfl⟩

theorem LInv.sym2_map_eq_iff {S : Finset W} {g : W → V} {f : V → W} (h : LInv S g f) {a b c d : W}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) :
    s(g a, g b) = s(g c, g d) ↔ s(a, b) = s(c, d) := by
  simp only [Sym2.eq_iff, h.eq_iff ha hc, h.eq_iff hb hd, h.eq_iff ha hd, h.eq_iff hb hc]

theorem pushG_verts (H : UMultigraph W) (g : W → V) (f : V → W) : (pushG H g f).verts = H.verts.image g := rfl

theorem pushG_mult (H : UMultigraph W) (g : W → V) (f : V → W) (e : Sym2 V) :
    (pushG H g f).mult e = if e ∈ (H.verts.image g).sym2 then H.mult (Sym2.map f e) else 0 := rfl

variable {H : UMultigraph W} {g : W → V} {f : V → W}

theorem pushG_mult_img (hfg : LInv H.verts g f) {a b : W} (ha : a ∈ H.verts) (hb : b ∈ H.verts) :
    (pushG H g f).mult s(g a, g b) = H.mult s(a, b) := by
  rw [pushG_mult, ite_eq_left, Sym2.map_mk, hfg a ha, hfg b hb]
  rw [Finset.mem_sym2_iff]
  intro x hx
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  · exact Finset.mem_image_of_mem g ha
  · exact Finset.mem_image_of_mem g hb

/-- Every pair of `V` is either the image of a pair of `H.verts`, or carries no bond of `pushG H g f`. -/
theorem pushG_cases (e : Sym2 V) :
    (∃ a ∈ H.verts, ∃ b ∈ H.verts, e = s(g a, g b)) ∨
      ((pushG H g f).mult e = 0 ∧ ∀ T ⊆ H.verts, e ∉ (T.image g).sym2) := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hx : x ∈ H.verts.image g
    · by_cases hy : y ∈ H.verts.image g
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
        exact Or.inl ⟨a, ha, b, hb, rfl⟩
      · refine Or.inr ⟨?_, fun T hT hm => hy ?_⟩
        · rw [pushG_mult, ite_eq_right]
          intro hm; exact hy (Finset.mem_sym2_iff.mp hm y (Sym2.mem_mk_right x y))
        · exact Finset.image_subset_image hT (Finset.mem_sym2_iff.mp hm y (Sym2.mem_mk_right x y))
    · refine Or.inr ⟨?_, fun T hT hm => hx ?_⟩
      · rw [pushG_mult, ite_eq_right]
        intro hm; exact hx (Finset.mem_sym2_iff.mp hm x (Sym2.mem_mk_left x y))
      · exact Finset.image_subset_image hT (Finset.mem_sym2_iff.mp hm x (Sym2.mem_mk_left x y))

/-- `pushG` of a subgraph: the multiplicity of an image pair is the original one. -/
theorem pushG_mult_img' {K : UMultigraph W} (hfg : LInv H.verts g f) (hK : K.verts ⊆ H.verts) {a b : W}
    (ha : a ∈ H.verts) (hb : b ∈ H.verts) : (pushG K g f).mult s(g a, g b) = K.mult s(a, b) := by
  by_cases hab : a ∈ K.verts ∧ b ∈ K.verts
  · exact pushG_mult_img (hfg.mono hK) hab.1 hab.2
  · rw [pushG_mult, ite_eq_right]
    · by_contra hne
      exact hab ⟨K.supp _ (Ne.symm hne) a (Sym2.mem_mk_left a b), K.supp _ (Ne.symm hne) b (Sym2.mem_mk_right a b)⟩
    · intro hm
      apply hab
      have h1 := Finset.mem_sym2_iff.mp hm (g a) (Sym2.mem_mk_left _ _)
      have h2 := Finset.mem_sym2_iff.mp hm (g b) (Sym2.mem_mk_right _ _)
      exact ⟨(hfg.mem_image_iff hK ha).mp h1, (hfg.mem_image_iff hK hb).mp h2⟩

/-! ### Neighbours -/

theorem multiset_map_finset_sum {ι : Type*} (s : Finset ι) (F : ι → Multiset W) :
    (∑ i ∈ s, F i).map g = ∑ i ∈ s, (F i).map g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Multiset.map_add, ih]

theorem nbrs_pushG (hfg : LInv H.verts g f) {j : W} (hj : j ∈ H.verts) :
    nbrs (pushG H g f) (g j) = (nbrs H j).map g := by
  unfold nbrs
  rw [pushG_verts, Finset.sum_image hfg.injOn, Multiset.map_add, multiset_map_finset_sum,
    pushG_mult_img hfg hj hj, Multiset.map_replicate]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [pushG_mult_img hfg hj ha, Multiset.map_replicate]

/-! ### Counting in mapped multisets -/

theorem count_map_of_injOn {S : Finset W} (hfg : LInv S g f) {A : Multiset (Sym2 W)} (hA : ∀ e ∈ A, e ∈ S.sym2)
    {a b : W} (ha : a ∈ S) (hb : b ∈ S) : (A.map (Sym2.map g)).count s(g a, g b) = A.count s(a, b) := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons e A ih =>
    rw [Multiset.map_cons, Multiset.count_cons, Multiset.count_cons,
      ih fun x hx => hA x (Multiset.mem_cons_of_mem hx)]
    congr 1
    have he := hA e (Multiset.mem_cons_self e A)
    induction e using Sym2.ind with
    | _ c d =>
      have hc := Finset.mem_sym2_iff.mp he c (Sym2.mem_mk_left c d)
      have hd := Finset.mem_sym2_iff.mp he d (Sym2.mem_mk_right c d)
      simp only [Sym2.map_mk, hfg.sym2_map_eq_iff ha hb hc hd]

theorem count_map_eq_zero {S : Finset W} {A : Multiset (Sym2 W)} (hA : ∀ e ∈ A, e ∈ S.sym2) {e : Sym2 V}
    (he : e ∉ (S.image g).sym2) : (A.map (Sym2.map g)).count e = 0 := by
  rw [Multiset.count_eq_zero]
  intro hm
  obtain ⟨e', he', rfl⟩ := Multiset.mem_map.mp hm
  apply he
  rw [Finset.mem_sym2_iff]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Sym2.mem_map.mp hx
  exact Finset.mem_image_of_mem g (Finset.mem_sym2_iff.mp (hA e' he') y hy)

/-! ### Closures -/

theorem mem_sym2_of_mult {K : UMultigraph W} {e : Sym2 W} (h : K.mult e ≠ 0) : e ∈ K.verts.sym2 :=
  Finset.mem_sym2_iff.mpr fun x hx => K.supp e h x hx

theorem isClosureU_pushG (hfg : LInv H.verts g f) {j₁ j₂ : W} (h₁ : j₁ ∈ H.verts) (h₂ : j₂ ∈ H.verts)
    {C : UMultigraph W} (hC : IsClosureU H j₁ j₂ C) :
    IsClosureU (pushG H g f) (g j₁) (g j₂) (pushG C g f) := by
  obtain ⟨hσ, hCv, hl, added, hcase, hm⟩ := hC
  have hCH : C.verts ⊆ H.verts := by
    rw [hCv]; exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hadd : ∀ e ∈ added, e ∈ C.verts.sym2 := by
    intro e he
    apply mem_sym2_of_mult
    rw [hm e]
    have := Multiset.count_pos.mpr he
    omega
  have haddH : ∀ e ∈ added, e ∈ H.verts.sym2 := fun e he =>
    Finset.mem_sym2_iff.mpr fun x hx => hCH (Finset.mem_sym2_iff.mp (hadd e he) x hx)
  refine ⟨?_, ?_, ?_, added.map (Sym2.map g), ?_, ?_⟩
  · rw [pushG_mult_img hfg h₁ h₂]; exact hσ
  · rw [pushG_verts, pushG_verts, hCv, hfg.image_erase (Finset.erase_subset _ _) h₂,
      hfg.image_erase le_rfl h₁]
  · intro x
    rcases pushG_cases (H := C) (g := g) (f := f) s(x, x) with ⟨a, ha, b, hb, he⟩ | ⟨h0, -⟩
    · have hab : a = b := by
        have := congrArg (fun z => z) he
        rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact (hfg.mono hCH).injOn ha hb (h1.symm.trans h2)
        · exact (hfg.mono hCH).injOn ha hb (h2.symm.trans h1)
      subst hab
      rw [he, pushG_mult_img (hfg.mono hCH) ha ha]; exact hl a
    · exact h0
  · rcases hcase with ⟨h0, a, b, c, d, ha, hc, rfl⟩ | ⟨h1, x, y, hx, hy, rfl⟩
    · refine Or.inl ⟨by rw [pushG_mult_img hfg h₁ h₂]; exact h0, g a, g b, g c, g d, ?_, ?_, ?_⟩
      · rw [nbrs_pushG hfg h₁, ha]; simp
      · rw [nbrs_pushG hfg h₂, hc]; simp
      · simp
    · refine Or.inr ⟨by rw [pushG_mult_img hfg h₁ h₂]; exact h1, g x, g y, ?_, ?_, ?_⟩
      · rw [nbrs_pushG hfg h₁, hx]; simp
      · rw [nbrs_pushG hfg h₂, hy]; simp
      · simp
  · intro e
    rcases pushG_cases (H := H) (g := g) (f := f) e with ⟨a, ha, b, hb, rfl⟩ | ⟨h0, hnot⟩
    · rw [pushG_mult_img' hfg hCH ha hb, hm, pushG_mult_img hfg ha hb, count_map_of_injOn hfg haddH ha hb]
      congr 1
      have hiff : (g j₁ ∈ s(g a, g b) ∨ g j₂ ∈ s(g a, g b)) ↔ (j₁ ∈ s(a, b) ∨ j₂ ∈ s(a, b)) := by
        simp only [Sym2.mem_iff, hfg.eq_iff h₁ ha, hfg.eq_iff h₁ hb, hfg.eq_iff h₂ ha, hfg.eq_iff h₂ hb]
      exact if_congr hiff.symm rfl rfl
    · rw [count_map_eq_zero haddH (hnot H.verts le_rfl), h0, pushG_mult, ite_eq_right (hnot C.verts hCH)]
      simp

/-! ### (Y2) steps and doubled triangles -/

theorem y2Step_verts {C C' : UMultigraph W} (h : Y2Step C C') : C'.verts ⊆ C.verts := by
  obtain ⟨a, b, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -⟩ := h
  rw [hv]; exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)

theorem rtg_verts {C C' : UMultigraph W} (h : Relation.ReflTransGen Y2Step C C') : C'.verts ⊆ C.verts := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact (y2Step_verts hs).trans ih

theorem y2Step_pushG {C C' : UMultigraph W} (hfg : LInv C.verts g f) (h : Y2Step C C') :
    Y2Step (pushG C g f) (pushG C' g f) := by
  have hC'C := y2Step_verts h
  obtain ⟨a, b, c, d, hab, hcd, hca, hcb, hda, hdb, h3, hac, hbd, ha0, hb0, hv, hm⟩ := h
  have ha : a ∈ C.verts := C.supp _ (by omega) a (Sym2.mem_mk_left a b)
  have hb : b ∈ C.verts := C.supp _ (by omega) b (Sym2.mem_mk_right a b)
  have hc : c ∈ C.verts := C.supp _ (by omega) c (Sym2.mem_mk_right a c)
  have hd : d ∈ C.verts := C.supp _ (by omega) d (Sym2.mem_mk_right b d)
  have hne : ∀ {x y : W}, x ∈ C.verts → y ∈ C.verts → x ≠ y → g x ≠ g y := fun hx hy hxy hh =>
    hxy (hfg.injOn hx hy hh)
  refine ⟨g a, g b, g c, g d, hne ha hb hab, hne hc hd hcd, hne hc ha hca, hne hc hb hcb, hne hd ha hda,
    hne hd hb hdb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pushG_mult_img hfg ha hb]; exact h3
  · rw [pushG_mult_img hfg ha hc]; exact hac
  · rw [pushG_mult_img hfg hb hd]; exact hbd
  · intro x hxb hxc
    rcases pushG_cases (H := C) (g := g) (f := f) s(g a, x) with ⟨p, hp, q, hq, he⟩ | ⟨h0, -⟩
    · rw [he]
      rw [pushG_mult_img hfg hp hq]
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hpa : p = a := hfg.injOn hp ha h1.symm
        subst hpa; subst h2
        exact ha0 q (fun hh => hxb (congrArg g hh)) (fun hh => hxc (congrArg g hh))
      · have hqa : q = a := hfg.injOn hq ha h1.symm
        subst hqa; subst h2
        rw [Sym2.eq_swap]
        exact ha0 p (fun hh => hxb (congrArg g hh)) (fun hh => hxc (congrArg g hh))
    · exact h0
  · intro x hxa hxd
    rcases pushG_cases (H := C) (g := g) (f := f) s(g b, x) with ⟨p, hp, q, hq, he⟩ | ⟨h0, -⟩
    · rw [he]
      rw [pushG_mult_img hfg hp hq]
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hpb : p = b := hfg.injOn hp hb h1.symm
        subst hpb; subst h2
        exact hb0 q (fun hh => hxa (congrArg g hh)) (fun hh => hxd (congrArg g hh))
      · have hqb : q = b := hfg.injOn hq hb h1.symm
        subst hqb; subst h2
        rw [Sym2.eq_swap]
        exact hb0 p (fun hh => hxa (congrArg g hh)) (fun hh => hxd (congrArg g hh))
    · exact h0
  · rw [pushG_verts, pushG_verts, hv, hfg.image_erase (Finset.erase_subset _ _) hb, hfg.image_erase le_rfl ha]
  · intro e
    rcases pushG_cases (H := C) (g := g) (f := f) e with ⟨p, hp, q, hq, rfl⟩ | ⟨h0, hnot⟩
    · rw [pushG_mult_img' hfg hC'C hp hq, hm, pushG_mult_img hfg hp hq]
      have hiff : (g a ∈ s(g p, g q) ∨ g b ∈ s(g p, g q)) ↔ (a ∈ s(p, q) ∨ b ∈ s(p, q)) := by
        simp only [Sym2.mem_iff, hfg.eq_iff ha hp, hfg.eq_iff ha hq, hfg.eq_iff hb hp, hfg.eq_iff hb hq]
      have hiff2 : s(g p, g q) = s(g c, g d) ↔ s(p, q) = s(c, d) := hfg.sym2_map_eq_iff hp hq hc hd
      simp only [hiff, hiff2]
    · rw [pushG_mult, ite_eq_right (hnot C'.verts hC'C), h0]
      split_ifs with h1 h2
      · rfl
      · exfalso
        apply hnot C'.verts hC'C
        rw [h2, Finset.mem_sym2_iff]
        intro x hx
        have hc' : c ∈ C'.verts := by rw [hv]; simp [hc, hca, hcb]
        have hd' : d ∈ C'.verts := by rw [hv]; simp [hd, hda, hdb]
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact Finset.mem_image_of_mem g hc'
        · exact Finset.mem_image_of_mem g hd'
      · rfl

theorem rtg_pushG {C C' : UMultigraph W} (hfg : LInv C.verts g f) (h : Relation.ReflTransGen Y2Step C C') :
    Relation.ReflTransGen Y2Step (pushG C g f) (pushG C' g f) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail B B' hCB hs ih => exact ih.tail (y2Step_pushG (hfg.mono (rtg_verts hCB)) hs)

theorem isDoubledTriangle_pushG {C : UMultigraph W} (hfg : LInv C.verts g f) (h : IsDoubledTriangle C) :
    IsDoubledTriangle (pushG C g f) := by
  obtain ⟨a, b, c, hab, hac, hbc, hv, hm⟩ := h
  have ha : a ∈ C.verts := by rw [hv]; simp
  have hb : b ∈ C.verts := by rw [hv]; simp
  have hc : c ∈ C.verts := by rw [hv]; simp
  have hne : ∀ {x y : W}, x ∈ C.verts → y ∈ C.verts → x ≠ y → g x ≠ g y := fun hx hy hxy hh =>
    hxy (hfg.injOn hx hy hh)
  refine ⟨g a, g b, g c, hne ha hb hab, hne ha hc hac, hne hb hc hbc, ?_, fun e => ?_⟩
  · rw [pushG_verts, hv]; simp [Finset.image_insert]
  · rcases pushG_cases (H := C) (g := g) (f := f) e with ⟨p, hp, q, hq, rfl⟩ | ⟨h0, hnot⟩
    · rw [pushG_mult_img hfg hp hq, hm]
      simp only [hfg.sym2_map_eq_iff hp hq ha hb, hfg.sym2_map_eq_iff hp hq hb hc, hfg.sym2_map_eq_iff hp hq ha hc]
    · rw [h0, ite_eq_right]
      intro hh
      apply hnot C.verts le_rfl
      have hab' : s(g a, g b) ∈ (C.verts.image g).sym2 := Finset.mk_mem_sym2_iff.mpr
        ⟨Finset.mem_image_of_mem g ha, Finset.mem_image_of_mem g hb⟩
      have hbc' : s(g b, g c) ∈ (C.verts.image g).sym2 := Finset.mk_mem_sym2_iff.mpr
        ⟨Finset.mem_image_of_mem g hb, Finset.mem_image_of_mem g hc⟩
      have hac' : s(g a, g c) ∈ (C.verts.image g).sym2 := Finset.mk_mem_sym2_iff.mpr
        ⟨Finset.mem_image_of_mem g ha, Finset.mem_image_of_mem g hc⟩
      rcases hh with rfl | rfl | rfl
      · exact hab'
      · exact hbc'
      · exact hac'

theorem reducesToT_pushG {C : UMultigraph W} (hfg : LInv C.verts g f) (h : ReducesToT C) :
    ReducesToT (pushG C g f) := by
  obtain ⟨C', hrt, hT⟩ := h
  exact ⟨pushG C' g f, rtg_pushG hfg hrt, isDoubledTriangle_pushG (hfg.mono (rtg_verts hrt)) hT⟩

/-- **Transport of T-vines.** If `H` is a T-vine, `f` a left inverse of `g` on `H.verts`, and `pushG H g f` a block,
then `pushG H g f` is a T-vine (with the image joints). -/
theorem isTVineU_pushG (hfg : LInv H.verts g f) {j₁ j₂ : W} (hT : IsTVineU H j₁ j₂)
    (hB : IsBlockU (pushG H g f) (g j₁) (g j₂)) : IsTVineU (pushG H g f) (g j₁) (g j₂) := by
  obtain ⟨hBH, hm2, C, hC, hR⟩ := hT
  have h₁ := hBH.1
  have h₂ := hBH.2.1
  refine ⟨hB, ?_, pushG C g f, isClosureU_pushG hfg h₁ h₂ hC, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    rw [pushG_mult_img hfg ha hb]
    exact hm2 a ha b hb fun hh => hxy (hh ▸ rfl)
  · have hCH : C.verts ⊆ H.verts := by
      rw [hC.2.1]; exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    exact reducesToT_pushG (hfg.mono hCH) hR

end push

/-! ## Graphs isomorphic to a T-vine -/

section iso

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- **T-vines are closed under isomorphism.** Let `G` be a block with joints `j₁, j₂`, and `f` injective on `G.verts`,
carrying `G.verts` onto `H.verts` and the multiplicities of `G` to those of `H`. If `H` is a T-vine with joints
`f j₁, f j₂`, so is `G`. -/
theorem isTVineU_of_iso {G : UMultigraph V} {H : UMultigraph W} {f : V → W} {j₁ j₂ : V}
    (hinj : Set.InjOn f G.verts) (himg : G.verts.image f = H.verts)
    (hmult : ∀ a ∈ G.verts, ∀ b ∈ G.verts, H.mult s(f a, f b) = G.mult s(a, b))
    (hB : IsBlockU G j₁ j₂) (hT : IsTVineU H (f j₁) (f j₂)) : IsTVineU G j₁ j₂ := by
  have : Nonempty V := ⟨j₁⟩
  set g : W → V := Function.invFunOn f (G.verts : Set V) with hg
  have hgf : ∀ v ∈ G.verts, g (f v) = v := fun v hv => hinj.leftInvOn_invFunOn hv
  have hfg : LInv H.verts g f := by
    intro w hw
    rw [← himg] at hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rw [hgf v hv]
  have hGeq : pushG H g f = G := by
    have hv : (pushG H g f).verts = G.verts := by
      rw [pushG_verts, ← himg, Finset.image_image]
      ext x
      simp only [Finset.mem_image, Function.comp_apply]
      constructor
      · rintro ⟨v, hv, rfl⟩; rw [hgf v hv]; exact hv
      · intro hx; exact ⟨x, hx, hgf x hx⟩
    apply Core.ext hv
    intro e
    rcases pushG_cases (H := H) (g := g) (f := f) e with ⟨a, ha, b, hb, rfl⟩ | ⟨h0, hnot⟩
    · rw [pushG_mult_img hfg ha hb]
      rw [← himg] at ha hb
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      rw [hgf x hx, hgf y hy, hmult x hx y hy]
    · rw [h0]
      by_contra hne
      apply hnot H.verts le_rfl
      have := mem_sym2_of_mult (Ne.symm hne)
      rwa [← hv] at this
  have h := isTVineU_pushG hfg hT (by rw [hGeq, hgf j₁ hB.1, hgf j₂ hB.2.1]; exact hB)
  rw [hGeq, hgf j₁ hB.1, hgf j₂ hB.2.1] at h
  exact h

end iso

end WaveTurbulence.TVine.Struct.Drawn
