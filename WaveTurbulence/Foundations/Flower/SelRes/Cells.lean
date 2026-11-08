/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.SelRes.Pin

/-! # D7 SEL-RES / Cells: the endpoints of a selected branch and the face domains

- `cells_identity`: for strict minima/maxima, `𝟙{lo < hi}(g hi − g lo)` is the signed sum over the upper and lower
  cells.
- `volume_eval_eq_null`, `volume_eval_eq_eval_null`: coordinate hyperplanes are Lebesgue-null.
- The endpoints of a free branch `v`: the constant floor `cfl` (layer floor, pinned children), the constant top
  `ctop` (layer ceiling, root time, pinned parent), the free children `Cf` and the free parent `Uf`; `slotA_squeeze`.
- `mem_Iup_dom_iff`, `mem_Ilo_dom_iff`: a parent (child) face cell is the doubly pinned time domain (`v` and the
  recipient pinned at a common time `r`) restricted to the interval `Iup` (`Ilo`) of constant conditions. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FlFace (fixSel fixSel_eq_none extendFix_of_none extendFix_of_some children parents
  mem_children mem_parents IsChildOf.ne)

variable {w : ℕ} {G : Garden w}

/-! ### Cells of a strict minimum / maximum -/

theorem inf'_cells {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (hf : Set.InjOn f s)
    (g : ℝ → ℂ) : g (s.inf' hs f) = ∑ i ∈ s, if (∀ j ∈ s, j ≠ i → f i < f j) then g (f i) else 0 := by
  obtain ⟨i₀, hi₀, he⟩ := Finset.exists_mem_eq_inf' hs f
  rw [Finset.sum_eq_single i₀]
  · have : ∀ j ∈ s, j ≠ i₀ → f i₀ < f j := fun j hj hji => by
      have h1 : f i₀ ≤ f j := he ▸ Finset.inf'_le f hj
      exact lt_of_le_of_ne h1 fun h => hji (hf hj hi₀ h.symm)
    rw [ite_eq_left this, he]
  · intro i hi hii
    rw [ite_eq_right]
    intro h
    have h1 := h i₀ hi₀ (Ne.symm hii)
    have h2 : f i₀ ≤ f i := he ▸ Finset.inf'_le f hi
    linarith
  · intro h; exact absurd hi₀ h

theorem sup'_cells {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (hf : Set.InjOn f s)
    (g : ℝ → ℂ) : g (s.sup' hs f) = ∑ i ∈ s, if (∀ j ∈ s, j ≠ i → f j < f i) then g (f i) else 0 := by
  obtain ⟨i₀, hi₀, he⟩ := Finset.exists_mem_eq_sup' hs f
  rw [Finset.sum_eq_single i₀]
  · have : ∀ j ∈ s, j ≠ i₀ → f j < f i₀ := fun j hj hji => by
      have h1 : f j ≤ f i₀ := he ▸ Finset.le_sup' f hj
      exact lt_of_le_of_ne h1 fun h => hji (hf hj hi₀ h)
    rw [ite_eq_left this, he]
  · intro i hi hii
    rw [ite_eq_right]
    intro h
    have h1 := h i₀ hi₀ (Ne.symm hii)
    have h2 : f i ≤ f i₀ := he ▸ Finset.le_sup' f hi
    linarith
  · intro h; exact absurd hi₀ h

/-- **Cell identity.** For a strict minimum of the upper values and a strict maximum of the lower values (both
injective), `𝟙{lo < hi} (g hi − g lo)` is the signed sum over the upper and lower cells. -/
theorem cells_identity {ι κ : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (hf : Set.InjOn f s)
    (t : Finset κ) (ht : t.Nonempty) (e : κ → ℝ) (he : Set.InjOn e t) (g : ℝ → ℂ) :
    (if t.sup' ht e < s.inf' hs f then g (s.inf' hs f) - g (t.sup' ht e) else 0) =
      (∑ i ∈ s, if (∀ j ∈ t, e j < f i) ∧ (∀ j ∈ s, j ≠ i → f i < f j) then g (f i) else 0) -
        ∑ j ∈ t, if (∀ i ∈ s, e j < f i) ∧ (∀ j' ∈ t, j' ≠ j → e j' < e j) then g (e j) else 0 := by
  obtain ⟨i₀, hi₀, hfi⟩ := Finset.exists_mem_eq_inf' hs f
  obtain ⟨j₀, hj₀, hej⟩ := Finset.exists_mem_eq_sup' ht e
  have hmin : ∀ i ∈ s, (∀ j ∈ s, j ≠ i → f i < f j) → f i = s.inf' hs f := by
    intro i hi h
    by_contra hne
    have h2 : s.inf' hs f ≤ f i := Finset.inf'_le f hi
    have h3 : f i₀ < f i := lt_of_le_of_ne (hfi ▸ h2) (fun h' => hne (h'.symm.trans hfi.symm) |>.elim)
    have h4 := h i₀ hi₀ (fun h' => by subst h'; exact absurd rfl (ne_of_gt h3))
    linarith
  have hmax : ∀ j ∈ t, (∀ j' ∈ t, j' ≠ j → e j' < e j) → e j = t.sup' ht e := by
    intro j hj h
    by_contra hne
    have h2 : e j ≤ t.sup' ht e := Finset.le_sup' e hj
    have h3 : e j < e j₀ := lt_of_le_of_ne (hej ▸ h2) (fun h' => hne (h'.trans hej.symm))
    have h4 := h j₀ hj₀ (fun h' => by subst h'; exact absurd rfl (ne_of_gt h3))
    linarith
  split_ifs with hlt
  · rw [inf'_cells s hs f hf g, sup'_cells t ht e he g]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      by_cases h : ∀ j ∈ s, j ≠ i → f i < f j
      · have hfi' := hmin i hi h
        have : ∀ j ∈ t, e j < f i := fun j hj => lt_of_le_of_lt (Finset.le_sup' e hj) (hfi' ▸ hlt)
        rw [ite_eq_left h, ite_eq_left ⟨this, h⟩]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.2)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      by_cases h : ∀ j' ∈ t, j' ≠ j → e j' < e j
      · have hej' := hmax j hj h
        have : ∀ i ∈ s, e j < f i := fun i hi => lt_of_lt_of_le (hej' ▸ hlt) (Finset.inf'_le f hi)
        rw [ite_eq_left h, ite_eq_left ⟨this, h⟩]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.2)]
  · have h1 : ∀ i ∈ s, ¬ ((∀ j ∈ t, e j < f i) ∧ (∀ j ∈ s, j ≠ i → f i < f j)) := by
      rintro i hi ⟨ha, hb⟩
      have := ha j₀ hj₀
      rw [hmin i hi hb, ← hej] at this
      exact hlt this
    have h2 : ∀ j ∈ t, ¬ ((∀ i ∈ s, e j < f i) ∧ (∀ j' ∈ t, j' ≠ j → e j' < e j)) := by
      rintro j hj ⟨ha, hb⟩
      have := ha i₀ hi₀
      rw [hmax j hj hb, ← hfi] at this
      exact hlt this
    rw [Finset.sum_eq_zero fun i hi => ite_eq_right (h1 i hi), Finset.sum_eq_zero fun j hj => ite_eq_right (h2 j hj),
      sub_zero]

/-! ### Null sets of the Lebesgue measure on `ι → ℝ` -/

theorem volume_eval_eq_null {ι : Type*} [Fintype ι] (i : ι) (c : ℝ) :
    volume {ρ : ι → ℝ | ρ i = c} = 0 := by
  have : {ρ : ι → ℝ | ρ i = c} = Function.eval i ⁻¹' ({c} : Set ℝ) := rfl
  rw [this, volume_pi]
  exact Measure.pi_eval_preimage_null _ Real.volume_singleton

theorem volume_eval_eq_eval_null {ι : Type*} [Fintype ι] {i j : ι} (hij : i ≠ j) :
    volume {ρ : ι → ℝ | ρ i = ρ j} = 0 := by
  set φ : (ι → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j with hφ
  have hs : {ρ : ι → ℝ | ρ i = ρ j} = (LinearMap.ker φ : Set (ι → ℝ)) := by
    ext ρ; simp [hφ, sub_eq_zero]
  rw [hs]
  refine Measure.addHaar_submodule _ _ fun h => ?_
  have hm : (Pi.single i (1 : ℝ) : ι → ℝ) ∈ LinearMap.ker φ := h ▸ Submodule.mem_top
  simp [hφ, hij.symm] at hm

end WaveTurbulence.Flower.SelRes

namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FlFace (fixSel fixSel_eq_none extendFix_of_none extendFix_of_some children parents
  mem_children mem_parents IsChildOf.ne)

variable {w : ℕ} {G : Garden w} (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
  (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree)

/-! ### The endpoints of a selected branch -/

/-- The constant lower endpoint: the layer floor and the pinned children. -/
def cfl : ℝ :=
  (insert (layer v : ℝ) (((children v).filter fun c => fix c ≠ none).image fun c => (fix c).getD 0)).max'
    (insert_nonempty _ _)

/-- The constant upper endpoint: the layer ceiling, the root time and the pinned parent. -/
def ctop : ℝ :=
  (insert ((layer v : ℝ) + 1) (insert (rootTime v.1.1)
    (((parents v).filter fun u => fix u ≠ none).image fun u => (fix u).getD 0))).min' (insert_nonempty _ _)

/-- The free children and the free parent. -/
def Cf : Finset (GBranch G.tree) := (children v).filter fun c => fix c = none
def Uf : Finset (GBranch G.tree) := (parents v).filter fun u => fix u = none

/-- Upper and lower endpoint indices (`none` = the constant endpoint). -/
def upI : Finset (Option (GBranch G.tree)) := insert none ((Uf fix v).image some)
def loI : Finset (Option (GBranch G.tree)) := insert none ((Cf fix v).image some)

def upV (X : GBranch G.tree → ℝ) : Option (GBranch G.tree) → ℝ := fun o => o.elim (ctop layer rootTime fix v) X
def loV (X : GBranch G.tree → ℝ) : Option (GBranch G.tree) → ℝ := fun o => o.elim (cfl layer fix v) X

theorem upI_nonempty : (upI fix v).Nonempty := insert_nonempty _ _
theorem loI_nonempty : (loI fix v).Nonempty := insert_nonempty _ _

def hiX (X : GBranch G.tree → ℝ) : ℝ := (upI fix v).inf' (upI_nonempty fix v) (upV layer rootTime fix v X)
def loX (X : GBranch G.tree → ℝ) : ℝ := (loI fix v).sup' (loI_nonempty fix v) (loV layer fix v X)

variable {layer rootTime fix v}

theorem mem_Cf {c : GBranch G.tree} : c ∈ Cf fix v ↔ c.IsChildOf v ∧ fix c = none := by
  simp [Cf, mem_children]
theorem mem_Uf {u : GBranch G.tree} : u ∈ Uf fix v ↔ v.IsChildOf u ∧ fix u = none := by
  simp [Uf, mem_parents]

theorem layer_le_cfl : (layer v : ℝ) ≤ cfl layer fix v := Finset.le_max' _ _ (mem_insert_self _ _)
theorem pinned_child_le_cfl {c : GBranch G.tree} (hc : c.IsChildOf v) {s : ℝ} (hs : fix c = some s) :
    s ≤ cfl layer fix v :=
  Finset.le_max' _ _ (mem_insert_of_mem (mem_image.2 ⟨c, mem_filter.2 ⟨mem_children.2 hc, by simp [hs]⟩,
    by simp [hs]⟩))
theorem ctop_le_ceil : ctop layer rootTime fix v ≤ (layer v : ℝ) + 1 := Finset.min'_le _ _ (mem_insert_self _ _)
theorem ctop_le_root : ctop layer rootTime fix v ≤ rootTime v.1.1 :=
  Finset.min'_le _ _ (mem_insert_of_mem (mem_insert_self _ _))
theorem ctop_le_pinned_parent {u : GBranch G.tree} (hu : v.IsChildOf u) {s : ℝ} (hs : fix u = some s) :
    ctop layer rootTime fix v ≤ s :=
  Finset.min'_le _ _ (mem_insert_of_mem (mem_insert_of_mem (mem_image.2 ⟨u, mem_filter.2
    ⟨mem_parents.2 hu, by simp [hs]⟩, by simp [hs]⟩)))

theorem cfl_lt_iff {r : ℝ} : cfl layer fix v < r ↔ (layer v : ℝ) < r ∧
    ∀ c, c.IsChildOf v → ∀ s, fix c = some s → s < r := by
  rw [cfl, Finset.max'_lt_iff]
  constructor
  · intro h
    refine ⟨h _ (mem_insert_self _ _), fun c hc s hs => ?_⟩
    exact h s (mem_insert_of_mem (mem_image.2 ⟨c, mem_filter.2 ⟨mem_children.2 hc, by simp [hs]⟩, by simp [hs]⟩))
  · rintro ⟨h1, h2⟩ y hy
    rcases mem_insert.1 hy with rfl | hy
    · exact h1
    · obtain ⟨c, hc, rfl⟩ := mem_image.1 hy
      obtain ⟨hc1, hc2⟩ := mem_filter.1 hc
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hc2
      rw [hs]; exact h2 c (mem_children.1 hc1) s hs

theorem lt_ctop_iff {r : ℝ} : r < ctop layer rootTime fix v ↔ r < (layer v : ℝ) + 1 ∧ r < rootTime v.1.1 ∧
    ∀ u, v.IsChildOf u → ∀ s, fix u = some s → r < s := by
  rw [ctop, Finset.lt_min'_iff]
  constructor
  · intro h
    refine ⟨h _ (mem_insert_self _ _), h _ (mem_insert_of_mem (mem_insert_self _ _)), fun u hu s hs => ?_⟩
    exact h s (mem_insert_of_mem (mem_insert_of_mem (mem_image.2 ⟨u, mem_filter.2 ⟨mem_parents.2 hu,
      by simp [hs]⟩, by simp [hs]⟩)))
  · rintro ⟨h1, h2, h3⟩ y hy
    rcases mem_insert.1 hy with rfl | hy
    · exact h1
    rcases mem_insert.1 hy with rfl | hy
    · exact h2
    · obtain ⟨u, hu, rfl⟩ := mem_image.1 hy
      obtain ⟨hu1, hu2⟩ := mem_filter.1 hu
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hu2
      rw [hs]; exact h3 u (mem_parents.1 hu1) s hs

theorem loX_lt_iff {X : GBranch G.tree → ℝ} {r : ℝ} :
    loX layer fix v X < r ↔ cfl layer fix v < r ∧ ∀ c ∈ Cf fix v, X c < r := by
  rw [loX, Finset.sup'_lt_iff]
  constructor
  · intro h
    exact ⟨h none (mem_insert_self _ _), fun c hc => h (some c) (mem_insert_of_mem (mem_image_of_mem _ hc))⟩
  · rintro ⟨h1, h2⟩ o ho
    rcases mem_insert.1 ho with rfl | ho
    · exact h1
    · obtain ⟨c, hc, rfl⟩ := mem_image.1 ho; exact h2 c hc

theorem lt_hiX_iff {X : GBranch G.tree → ℝ} {r : ℝ} :
    r < hiX layer rootTime fix v X ↔ r < ctop layer rootTime fix v ∧ ∀ u ∈ Uf fix v, r < X u := by
  rw [hiX, Finset.lt_inf'_iff]
  constructor
  · intro h
    exact ⟨h none (mem_insert_self _ _), fun u hu => h (some u) (mem_insert_of_mem (mem_image_of_mem _ hu))⟩
  · rintro ⟨h1, h2⟩ o ho
    rcases mem_insert.1 ho with rfl | ho
    · exact h1
    · obtain ⟨u, hu, rfl⟩ := mem_image.1 ho; exact h2 u hu

/-- The admissible times of `v` are squeezed between the open and the closed endpoint interval. -/
theorem slotA_squeeze (X : GBranch G.tree → ℝ) (hX : ∀ x s, fix x = some s → X x = s) :
    Ioo (loX layer fix v X) (hiX layer rootTime fix v X) ⊆ slotA layer rootTime v X ∧
      slotA layer rootTime v X ⊆ Icc (loX layer fix v X) (hiX layer rootTime fix v X) := by
  constructor
  · rintro r ⟨hl, hh⟩
    obtain ⟨hc1, hc2⟩ := loX_lt_iff.1 hl
    obtain ⟨hu1, hu2⟩ := lt_hiX_iff.1 hh
    obtain ⟨hl1, hl2⟩ := cfl_lt_iff.1 hc1
    obtain ⟨ht1, ht2, ht3⟩ := lt_ctop_iff.1 hu1
    refine ⟨hl1.le, ht1.le, ht2, fun c hc => ?_, fun u hu => ?_⟩
    · rcases hfc : fix c with _ | s
      · exact hc2 c (mem_Cf.2 ⟨hc, hfc⟩)
      · rw [hX c s hfc]; exact hl2 c hc s hfc
    · rcases hfu : fix u with _ | s
      · exact hu2 u (mem_Uf.2 ⟨hu, hfu⟩)
      · rw [hX u s hfu]; exact ht3 u hu s hfu
  · rintro r ⟨hl, hh, hroot, hc, hp⟩
    refine ⟨Finset.sup'_le _ _ fun o ho => ?_, Finset.le_inf' _ _ fun o ho => ?_⟩
    · rcases mem_insert.1 ho with rfl | ho
      · show cfl layer fix v ≤ r
        refine Finset.max'_le _ _ _ fun y hy => ?_
        rcases mem_insert.1 hy with rfl | hy
        · exact hl
        · obtain ⟨c, hc', rfl⟩ := mem_image.1 hy
          obtain ⟨hc1, hc2⟩ := mem_filter.1 hc'
          obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hc2
          rw [hs]; exact (hX c s hs ▸ hc c (mem_children.1 hc1)).le
      · obtain ⟨c, hc', rfl⟩ := mem_image.1 ho
        exact (hc c (mem_Cf.1 hc').1).le
    · rcases mem_insert.1 ho with rfl | ho
      · show r ≤ ctop layer rootTime fix v
        refine Finset.le_min' _ _ _ fun y hy => ?_
        rcases mem_insert.1 hy with rfl | hy
        · exact hh
        rcases mem_insert.1 hy with rfl | hy
        · exact hroot.le
        · obtain ⟨u, hu', rfl⟩ := mem_image.1 hy
          obtain ⟨hu1, hu2⟩ := mem_filter.1 hu'
          obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hu2
          rw [hs]; exact (hX u s hs ▸ hp u (mem_parents.1 hu1)).le
      · obtain ⟨u, hu', rfl⟩ := mem_image.1 ho
        exact (hp u (mem_Uf.1 hu').1).le

end WaveTurbulence.Flower.SelRes

namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FlFace (fixSel fixSel_eq_none extendFix_of_none extendFix_of_some children parents
  mem_children mem_parents IsChildOf.ne)

variable {w : ℕ} {G : Garden w} (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
  (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree)

/-- The parent-face interval of the recipient `u`. -/
def Iup (u : GBranch G.tree) : Set ℝ :=
  {r | cfl layer fix v < r ∧ r < ctop layer rootTime fix v ∧ (layer u : ℝ) ≤ r ∧ r ≤ layer u + 1 ∧
    r < rootTime u.1.1 ∧ (∀ x, x.IsChildOf u → x ≠ v → ∀ s, fix x = some s → s < r) ∧
    ∀ q, u.IsChildOf q → ∀ s, fix q = some s → r < s}

/-- The child-face interval of the recipient `c`. -/
def Ilo (c : GBranch G.tree) : Set ℝ :=
  {r | cfl layer fix v < r ∧ r < ctop layer rootTime fix v ∧ (layer c : ℝ) ≤ r ∧ r ≤ layer c + 1 ∧
    r < rootTime c.1.1 ∧ ∀ x, x.IsChildOf c → ∀ s, fix x = some s → s < r}

variable {layer rootTime fix v}

theorem pin2_apply_self {u : GBranch G.tree} {r : ℝ} : pin (pin fix v r) u r u = some r := Function.update_self _ _ _
theorem pin2_apply_v {u : GBranch G.tree} {r : ℝ} (h : v ≠ u) : pin (pin fix v r) u r v = some r := by
  rw [pin_apply_of_ne h]; exact Function.update_self _ _ _
theorem pin2_apply_ne {u x : GBranch G.tree} {r : ℝ} (h1 : x ≠ u) (h2 : x ≠ v) : pin (pin fix v r) u r x = fix x := by
  rw [pin_apply_of_ne h1, pin_apply_of_ne h2]

/-- **The parent face.** -/
theorem mem_Iup_dom_iff (hv : fix v = none) {u : GBranch G.tree} (hu : v.IsChildOf u) (hfu : fix u = none)
    (Y : GBranch G.tree → ℝ) (hY : ∀ x s, fix x = some s → Y x = s) (r : ℝ) (hYu : Y u = r) :
    (r ∈ Iup layer rootTime fix v u ∧
      Function.update Y v r ∈ splicedTimeDomainFix G layer rootTime (pin (pin fix v r) u r)) ↔
      (restOK layer rootTime fix v Y ∧ loX layer fix v Y < r ∧ r < ctop layer rootTime fix v) := by
  have hvu : v ≠ u := IsChildOf.ne hu
  have hZv : Function.update Y v r v = r := Function.update_self _ _ _
  have hZ : ∀ x, x ≠ v → Function.update Y v r x = Y x := fun x hx => Function.update_of_ne hx _ _
  constructor
  · rintro ⟨⟨hcfl, htop, hl, hh, hroot, hpc, hpp⟩, hD1, hD2⟩
    refine ⟨⟨fun x hx hfx => ?_, fun x y hx hy hxy hfn => ?_⟩, loX_lt_iff.2 ⟨hcfl, fun c hc => ?_⟩, htop⟩
    · by_cases hxu : x = u
      · subst hxu; rw [hYu]; exact ⟨⟨hl, hh⟩, hroot⟩
      · have := hD1 x (by rw [pin2_apply_ne hxu hx]; exact hfx); rwa [hZ x hx] at this
    · by_cases hyu : y = u
      · subst hyu
        have hxu : x ≠ y := IsChildOf.ne hxy
        rcases hfx : fix x with _ | s
        · have := hD2 x y hxy (Or.inl (by rw [pin2_apply_ne hxu hx]; exact hfx))
          rwa [hZ x hx, hZ y hy] at this
        · rw [hY x s hfx, hYu]; exact hpc x hxy hx s hfx
      · by_cases hxu : x = u
        · subst hxu
          rcases hfy : fix y with _ | s
          · have := hD2 x y hxy (Or.inr (by rw [pin2_apply_ne hyu hy]; exact hfy))
            rwa [hZ x hx, hZ y hy] at this
          · rw [hY y s hfy, hYu]; exact hpp y hxy s hfy
        · have := hD2 x y hxy (by rwa [pin2_apply_ne hxu hx, pin2_apply_ne hyu hy])
          rwa [hZ x hx, hZ y hy] at this
    · obtain ⟨hcv, hfc⟩ := mem_Cf.1 hc
      have hcu : c ≠ u := fun h => isChildOf_asymm hu (h ▸ hcv)
      have hcv' : c ≠ v := IsChildOf.ne hcv
      have := hD2 c v hcv (Or.inl (by rw [pin2_apply_ne hcu hcv']; exact hfc))
      rwa [hZ c hcv', hZv] at this
  · rintro ⟨⟨hR1, hR2⟩, hlo, htop⟩
    obtain ⟨hcfl, hCf⟩ := loX_lt_iff.1 hlo
    have hub := hR1 u hvu.symm hfu
    rw [hYu] at hub
    refine ⟨⟨hcfl, htop, hub.1.1, hub.1.2, hub.2, fun x hxu hxv s hfx => ?_, fun q huq s hfq => ?_⟩, ?_, ?_⟩
    · have := hR2 x u hxv hvu.symm hxu (Or.inr hfu); rwa [hY x s hfx, hYu] at this
    · have hqv : q ≠ v := fun h => isChildOf_asymm hu (h ▸ huq)
      have := hR2 u q hvu.symm hqv huq (Or.inl hfu); rwa [hY q s hfq, hYu] at this
    · intro x hfx
      have hxu : x ≠ u := fun h => by rw [h, pin2_apply_self] at hfx; exact absurd hfx (by simp)
      have hxv : x ≠ v := fun h => by rw [h, pin2_apply_v hvu] at hfx; exact absurd hfx (by simp)
      rw [pin2_apply_ne hxu hxv] at hfx
      rw [hZ x hxv]; exact hR1 x hxv hfx
    · intro x y hxy hfn
      by_cases hxv : x = v
      · subst hxv
        have hyu : y = u := isChildOf_parent_unique hxy hu
        subst hyu
        rw [pin2_apply_self, pin2_apply_v hvu] at hfn
        exact absurd hfn (by simp)
      by_cases hyv : y = v
      · subst hyv
        have hxu : x ≠ u := fun h => isChildOf_asymm hu (h ▸ hxy)
        rw [pin2_apply_ne hxu hxv, pin2_apply_v hvu] at hfn
        have hfx : fix x = none := hfn.resolve_right (by simp)
        rw [hZ x hxv, hZv]; exact hCf x (mem_Cf.2 ⟨hxy, hfx⟩)
      rw [hZ x hxv, hZ y hyv]
      by_cases hxu : x = u
      · subst hxu
        have hyu : y ≠ x := (IsChildOf.ne hxy).symm
        rw [pin2_apply_self, pin2_apply_ne hyu hyv] at hfn
        exact hR2 x y hxv hyv hxy (Or.inl hfu)
      by_cases hyu : y = u
      · subst hyu
        rw [pin2_apply_ne hxu hxv, pin2_apply_self] at hfn
        exact hR2 x y hxv hyv hxy (Or.inl (hfn.resolve_right (by simp)))
      · rw [pin2_apply_ne hxu hxv, pin2_apply_ne hyu hyv] at hfn
        exact hR2 x y hxv hyv hxy hfn

/-- **The child face.** -/
theorem mem_Ilo_dom_iff (hv : fix v = none) {c : GBranch G.tree} (hc : c.IsChildOf v) (hfc : fix c = none)
    (Y : GBranch G.tree → ℝ) (hY : ∀ x s, fix x = some s → Y x = s) (r : ℝ) (hYc : Y c = r) :
    (r ∈ Ilo layer rootTime fix v c ∧
      Function.update Y v r ∈ splicedTimeDomainFix G layer rootTime (pin (pin fix v r) c r)) ↔
      (restOK layer rootTime fix v Y ∧ r < hiX layer rootTime fix v Y ∧ cfl layer fix v < r ∧
        ∀ c' ∈ Cf fix v, c' ≠ c → Y c' < r) := by
  have hcv : c ≠ v := IsChildOf.ne hc
  have hvc : v ≠ c := hcv.symm
  have hZv : Function.update Y v r v = r := Function.update_self _ _ _
  have hZ : ∀ x, x ≠ v → Function.update Y v r x = Y x := fun x hx => Function.update_of_ne hx _ _
  constructor
  · rintro ⟨⟨hcfl, htop, hl, hh, hroot, hpc⟩, hD1, hD2⟩
    refine ⟨⟨fun x hx hfx => ?_, fun x y hx hy hxy hfn => ?_⟩, lt_hiX_iff.2 ⟨htop, fun u hu => ?_⟩, hcfl,
      fun c' hc' hcc => ?_⟩
    · by_cases hxc : x = c
      · subst hxc; rw [hYc]; exact ⟨⟨hl, hh⟩, hroot⟩
      · have := hD1 x (by rw [pin2_apply_ne hxc hx]; exact hfx); rwa [hZ x hx] at this
    · by_cases hyc : y = c
      · subst hyc
        have hxc : x ≠ y := IsChildOf.ne hxy
        rcases hfx : fix x with _ | s
        · have := hD2 x y hxy (Or.inl (by rw [pin2_apply_ne hxc hx]; exact hfx))
          rwa [hZ x hx, hZ y hy] at this
        · rw [hY x s hfx, hYc]; exact hpc x hxy s hfx
      · by_cases hxc : x = c
        · subst hxc; exact absurd (isChildOf_parent_unique hxy hc) hy
        · have := hD2 x y hxy (by rwa [pin2_apply_ne hxc hx, pin2_apply_ne hyc hy])
          rwa [hZ x hx, hZ y hy] at this
    · obtain ⟨hvu, hfu⟩ := mem_Uf.1 hu
      have huc : u ≠ c := fun h => isChildOf_asymm hc (h ▸ hvu)
      have huv : u ≠ v := (IsChildOf.ne hvu).symm
      have := hD2 v u hvu (Or.inr (by rw [pin2_apply_ne huc huv]; exact hfu))
      rwa [hZv, hZ u huv] at this
    · obtain ⟨hc'v, hfc'⟩ := mem_Cf.1 hc'
      have hc'v' : c' ≠ v := IsChildOf.ne hc'v
      have := hD2 c' v hc'v (Or.inl (by rw [pin2_apply_ne hcc hc'v']; exact hfc'))
      rwa [hZ c' hc'v', hZv] at this
  · rintro ⟨⟨hR1, hR2⟩, hhi, hcfl, hCf⟩
    obtain ⟨htop, hUf⟩ := lt_hiX_iff.1 hhi
    have hcb := hR1 c hcv hfc
    rw [hYc] at hcb
    refine ⟨⟨hcfl, htop, hcb.1.1, hcb.1.2, hcb.2, fun x hxc s hfx => ?_⟩, ?_, ?_⟩
    · have hxv : x ≠ v := fun h => isChildOf_asymm hc (h ▸ hxc)
      have := hR2 x c hxv hcv hxc (Or.inr hfc); rwa [hY x s hfx, hYc] at this
    · intro x hfx
      have hxc : x ≠ c := fun h => by rw [h, pin2_apply_self] at hfx; exact absurd hfx (by simp)
      have hxv : x ≠ v := fun h => by rw [h, pin2_apply_v hvc] at hfx; exact absurd hfx (by simp)
      rw [pin2_apply_ne hxc hxv] at hfx
      rw [hZ x hxv]; exact hR1 x hxv hfx
    · intro x y hxy hfn
      by_cases hxv : x = v
      · subst hxv
        have hyc : y ≠ c := fun h => isChildOf_asymm hc (h ▸ hxy)
        have hyv : y ≠ x := (IsChildOf.ne hxy).symm
        rw [pin2_apply_v hvc, pin2_apply_ne hyc hyv] at hfn
        rw [hZv, hZ y hyv]; exact hUf y (mem_Uf.2 ⟨hxy, hfn.resolve_left (by simp)⟩)
      by_cases hyv : y = v
      · subst hyv
        by_cases hxc : x = c
        · subst hxc; rw [pin2_apply_self, pin2_apply_v hvc] at hfn; exact absurd hfn (by simp)
        · rw [pin2_apply_ne hxc hxv, pin2_apply_v hvc] at hfn
          rw [hZ x hxv, hZv]; exact hCf x (mem_Cf.2 ⟨hxy, hfn.resolve_right (by simp)⟩) hxc
      rw [hZ x hxv, hZ y hyv]
      by_cases hxc : x = c
      · subst hxc; exact absurd (isChildOf_parent_unique hxy hc) hyv
      by_cases hyc : y = c
      · subst hyc
        rw [pin2_apply_ne hxc hxv, pin2_apply_self] at hfn
        exact hR2 x y hxv hyv hxy (Or.inl (hfn.resolve_right (by simp)))
      · rw [pin2_apply_ne hxc hxv, pin2_apply_ne hyc hyv] at hfn
        exact hR2 x y hxv hyv hxy hfn

end WaveTurbulence.Flower.SelRes
