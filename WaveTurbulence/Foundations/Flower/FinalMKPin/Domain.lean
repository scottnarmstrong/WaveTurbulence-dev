/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Fine
public import WaveTurbulence.Foundations.Spine.Final4c
import Mathlib.Tactic

/-! # C4a PIN-FOURIER: the face time domain as a generic ladder-engine domain

Pins (`fix b = some r`) hold a clock at `r`; an endpoint substitution (`face v = some u`) gives `v` the clock of its
recipient `u`. The integration clocks are `Iv fix face = {b // fix b = none ∧ face b = none}`. Up to a null set, the
domain `splicedTimeDomainFace` read on these clocks is main's generic `Om0 chF lsF capF`:
- `chF` is the parent/child order of the tree with each substituted pair contracted (`repV`);
- a pinned child gives a floor (`floorF`, folded into the box start `lsF`), a pinned parent a strict cap (`capF`);
- the pinned pairs themselves impose nothing.

The phases regroup over the contraction fibres (`fib`), so `‖B_face(α)‖ = ‖Φ(Om0 …)(shiftF α)‖`
(`enorm_splicedFourierBMKFace_eq`). -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKPin
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.Flower.FinalMKDefs
open MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w : ℕ} {G : Garden w}

/-- The admissible substitutions (the face clauses of `LadderFourierAtMKFace`, without the `E` membership). -/
structure FaceOK (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree)) : Prop where
  recip : ∀ v u, face v = some u → fix v = none ∧ fix u = none ∧ face u = none ∧ (v.IsChildOf u ∨ u.IsChildOf v)
  uniq : ∀ v v', (face v).isSome → (face v').isSome → v.1.1 = v'.1.1 → v = v'

/-- The integration clocks. -/
abbrev Iv (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree)) : Type :=
  {b : GBranch G.tree // fix b = none ∧ face b = none}

/-- The clock carrying the time of an unpinned branch: itself, or its recipient. -/
def repV (face : GBranch G.tree → Option (GBranch G.tree)) (b : GBranch G.tree) : GBranch G.tree :=
  (face b).getD b

/-- The integration clocks, extended by `0`. -/
noncomputable def ttv (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (τ : Iv fix face → ℝ) (b : GBranch G.tree) : ℝ :=
  if h : fix b = none ∧ face b = none then τ ⟨b, h⟩ else 0

/-- The value of a pin. -/
noncomputable def pinVal (fix : GBranch G.tree → Option ℝ) (b : GBranch G.tree) : ℝ := (fix b).getD 0

variable {fix : GBranch G.tree → Option ℝ} {face : GBranch G.tree → Option (GBranch G.tree)}

theorem repV_of_none {b : GBranch G.tree} (h : face b = none) : repV face b = b := by
  simp [repV, h]

theorem repV_of_some {b u : GBranch G.tree} (h : face b = some u) : repV face b = u := by
  simp [repV, h]

theorem extendFixFace_eq (τ : Iv fix face → ℝ) (b : GBranch G.tree) :
    extendFixFace G fix face τ b = (fix b).elim (ttv fix face τ (repV face b)) id := by
  unfold extendFixFace
  split
  · simp_all
  · next hf hg => simp [ttv, repV, hf, hg]
  · next u hf hg => simp [ttv, repV, hf, hg]

theorem extendFixFace_pin (τ : Iv fix face → ℝ) {b : GBranch G.tree} (h : fix b ≠ none) :
    extendFixFace G fix face τ b = pinVal fix b := by
  rw [extendFixFace_eq]
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp h
  simp [hr, pinVal]

theorem extendFixFace_unpin (τ : Iv fix face → ℝ) {b : GBranch G.tree} (h : fix b = none) :
    extendFixFace G fix face τ b = ttv fix face τ (repV face b) := by
  rw [extendFixFace_eq, h]; rfl

theorem extendFixFace_free (τ : Iv fix face → ℝ) (a : Iv fix face) :
    extendFixFace G fix face τ a.1 = τ a := by
  rw [extendFixFace_unpin τ a.2.1, repV_of_none a.2.2]
  simp [ttv, a.2.1, a.2.2]

theorem FaceOK.pin_face (hF : FaceOK fix face) {b : GBranch G.tree} (h : fix b ≠ none) : face b = none := by
  rcases hg : face b with _ | u
  · rfl
  · exact absurd (hF.recip b u hg).1 h

theorem FaceOK.repV_free (hF : FaceOK fix face) {b : GBranch G.tree} (h : fix b = none) :
    fix (repV face b) = none ∧ face (repV face b) = none := by
  rcases hg : face b with _ | u
  · rw [repV_of_none hg]; exact ⟨h, hg⟩
  · rw [repV_of_some hg]; exact ⟨(hF.recip b u hg).2.1, (hF.recip b u hg).2.2.1⟩

/-- The clock of an unpinned branch, as an integration clock. -/
def repI (hF : FaceOK fix face) (b : GBranch G.tree) (h : fix b = none) : Iv fix face :=
  ⟨repV face b, hF.repV_free h⟩

theorem ttv_repV (hF : FaceOK fix face) (τ : Iv fix face → ℝ) {b : GBranch G.tree} (h : fix b = none) :
    ttv fix face τ (repV face b) = τ (repI hF b h) := by
  simp [ttv, (hF.repV_free h).1, (hF.repV_free h).2, repI]

theorem isChildOf_ne {v u : GBranch G.tree} (h : v.IsChildOf u) : v ≠ u := by
  intro e; subst e
  have := isChildOf_length h
  omega

/-- A pair of unpinned branches shares a clock exactly when it is a substituted pair. -/
theorem FaceOK.repV_eq_iff (hF : FaceOK fix face) {v u : GBranch G.tree} (hch : v.IsChildOf u)
    (_hv : fix v = none) (_hu : fix u = none) :
    repV face v = repV face u ↔ (face v = some u ∨ face u = some v) := by
  constructor
  · intro h
    rcases hg : face v with _ | x <;> rcases hk : face u with _ | y
    · rw [repV_of_none hg, repV_of_none hk] at h; exact absurd h (isChildOf_ne hch)
    · rw [repV_of_none hg, repV_of_some hk] at h; exact Or.inr (by rw [h])
    · rw [repV_of_some hg, repV_of_none hk] at h; exact Or.inl (by rw [h])
    · exfalso
      have := hF.uniq v u (by simp [hg]) (by simp [hk]) hch.1
      exact isChildOf_ne hch this
  · rintro (h | h)
    · rw [repV_of_some h, repV_of_none (hF.recip v u h).2.2.1]
    · rw [repV_of_some h, repV_of_none (hF.recip u v h).2.2.1]

/-! ### The contracted tree, floors and caps -/

/-- The contracted parent/child relation on the integration clocks. -/
def chF (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (a b : Iv fix face) : Prop :=
  a ≠ b ∧ ∃ v u : GBranch G.tree, v.IsChildOf u ∧ fix v = none ∧ fix u = none ∧
    repV face v = a.1 ∧ repV face u = b.1

/-- Pinned children of the fibre of `a`. -/
noncomputable def floorSrc (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (a : Iv fix face) : Finset (GBranch G.tree) :=
  univ.filter fun v => fix v ≠ none ∧ ∃ u, v.IsChildOf u ∧ fix u = none ∧ repV face u = a.1

/-- Pinned parents of the fibre of `a`. -/
noncomputable def capSrc (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (a : Iv fix face) : Finset (GBranch G.tree) :=
  univ.filter fun u => fix u ≠ none ∧ ∃ v, v.IsChildOf u ∧ fix v = none ∧ repV face v = a.1

/-- The floor: the layer start and the pinned children. -/
noncomputable def floorF (layer : GBranch G.tree → ℕ) (fix : GBranch G.tree → Option ℝ)
    (face : GBranch G.tree → Option (GBranch G.tree)) (a : Iv fix face) : ℝ :=
  (floorSrc fix face a).fold max (layer a.1 : ℝ) (pinVal fix)

/-- The box start (clipped at the layer end). -/
noncomputable def lsF (layer : GBranch G.tree → ℕ) (fix : GBranch G.tree → Option ℝ)
    (face : GBranch G.tree → Option (GBranch G.tree)) (a : Iv fix face) : ℝ :=
  min ((layer a.1 : ℝ) + 1) (floorF layer fix face a)

/-- The strict cap: the root time, the layer end and the pinned parents. -/
noncomputable def capF (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (face : GBranch G.tree → Option (GBranch G.tree)) (a : Iv fix face) : ℝ :=
  (capSrc fix face a).fold min (min (rootTime a.1.1.1) ((layer a.1 : ℝ) + 1)) (pinVal fix)

/-- The boundary coincidences. -/
def nullFF (layer : GBranch G.tree → ℕ) (fix : GBranch G.tree → Option ℝ)
    (face : GBranch G.tree → Option (GBranch G.tree)) : Set (Iv fix face → ℝ) :=
  (⋃ a, {τ | τ a = lsF layer fix face a}) ∪ ⋃ a, {τ | τ a = (layer a.1 : ℝ) + 1}

theorem volume_nullFF (layer : GBranch G.tree → ℕ) : volume (nullFF layer fix face) = 0 :=
  measure_union_null (measure_iUnion_null fun a => volume_eval_eq a _)
    (measure_iUnion_null fun a => volume_eval_eq a _)

theorem layer_le_lsF (layer : GBranch G.tree → ℕ) (a : Iv fix face) : (layer a.1 : ℝ) ≤ lsF layer fix face a :=
  le_min (by linarith) ((Finset.le_fold_max _).mpr (Or.inl le_rfl))

theorem lsF_le (layer : GBranch G.tree → ℕ) (a : Iv fix face) : lsF layer fix face a ≤ (layer a.1 : ℝ) + 1 :=
  min_le_left _ _

theorem capF_le_layer (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (a : Iv fix face) :
    capF layer rootTime fix face a ≤ (layer a.1 : ℝ) + 1 :=
  (Finset.fold_min_le _).mpr (Or.inl (min_le_right _ _))

theorem capF_le_root (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (a : Iv fix face) :
    capF layer rootTime fix face a ≤ rootTime a.1.1.1 :=
  (Finset.fold_min_le _).mpr (Or.inl (min_le_left _ _))

theorem capF_le_pin (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) {a : Iv fix face} {u : GBranch G.tree}
    (hu : u ∈ capSrc fix face a) : capF layer rootTime fix face a ≤ pinVal fix u :=
  (Finset.fold_min_le _).mpr (Or.inr ⟨u, hu, le_rfl⟩)

/-- On the generic domain the floor is not clipped. -/
theorem lsF_eq_floorF {layer : GBranch G.tree → ℕ} {rootTime : Fin w → ℝ} {τ : Iv fix face → ℝ}
    (hτ : τ ∈ Om0 (chF fix face) (lsF layer fix face) (capF layer rootTime fix face)) (a : Iv fix face) :
    lsF layer fix face a = floorF layer fix face a := by
  have h1 := (hτ.1 a).1
  have h2 := hτ.2.1 a
  have h3 := capF_le_layer layer rootTime a
  unfold lsF at h1 ⊢
  rcases le_total ((layer a.1 : ℝ) + 1) (floorF layer fix face a) with h | h
  · rw [min_eq_left h] at h1; linarith
  · exact min_eq_right h

theorem pin_le_lsF {layer : GBranch G.tree → ℕ} {rootTime : Fin w → ℝ} {τ : Iv fix face → ℝ}
    (hτ : τ ∈ Om0 (chF fix face) (lsF layer fix face) (capF layer rootTime fix face)) {a : Iv fix face}
    {v : GBranch G.tree} (hv : v ∈ floorSrc fix face a) : pinVal fix v ≤ lsF layer fix face a := by
  rw [lsF_eq_floorF hτ a]
  exact (Finset.le_fold_max _).mpr (Or.inr ⟨v, hv, le_rfl⟩)

/-! ### The domain identification -/

theorem domFace_iff (hF : FaceOK fix face) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (τ : Iv fix face → ℝ) (hτ : τ ∉ nullFF layer fix face) :
    extendFixFace G fix face τ ∈ splicedTimeDomainFace G layer rootTime fix face ↔
      τ ∈ Om0 (chF fix face) (lsF layer fix face) (capF layer rootTime fix face) := by
  have hn1 : ∀ a, τ a ≠ lsF layer fix face a := fun a h => hτ (Or.inl (Set.mem_iUnion.mpr ⟨a, h⟩))
  have hn2 : ∀ a, τ a ≠ (layer a.1 : ℝ) + 1 := fun a h => hτ (Or.inr (Set.mem_iUnion.mpr ⟨a, h⟩))
  have hrep : ∀ b (h : fix b = none), extendFixFace G fix face τ b = τ (repI hF b h) := fun b h => by
    rw [extendFixFace_unpin τ h, ttv_repV hF τ h]
  constructor
  · rintro ⟨h1, h2⟩
    have hbox : ∀ a : Iv fix face, (layer a.1 : ℝ) ≤ τ a ∧ τ a ≤ (layer a.1 : ℝ) + 1 ∧ τ a < rootTime a.1.1.1 := by
      intro a
      have := h1 a.1 a.2.1 a.2.2
      rw [extendFixFace_free] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    refine ⟨fun a => ⟨?_, ?_⟩, fun a => ?_, fun a b hab => ?_⟩
    · -- the floor
      refine (min_le_right _ _).trans ((Finset.fold_max_le _).mpr ⟨(hbox a).1, fun v hv => ?_⟩)
      obtain ⟨hvp, u, hch, hu, hua⟩ := (Finset.mem_filter.mp hv).2
      have := h2 v u hch (Or.inr hu) (by rw [hF.pin_face hvp]; simp)
        (fun hk => hvp (hF.recip u v hk).2.1)
      rw [extendFixFace_pin τ hvp, hrep u hu] at this
      have e : repI hF u hu = a := Subtype.ext hua
      rw [e] at this
      exact this.le
    · linarith [(hbox a).2.1, layer_le_lsF layer a]
    · refine (Finset.lt_fold_min _).mpr ⟨lt_min (hbox a).2.2 (lt_of_le_of_ne (hbox a).2.1 (hn2 a)), fun u hu => ?_⟩
      obtain ⟨hup, v, hch, hv, hva⟩ := (Finset.mem_filter.mp hu).2
      have := h2 v u hch (Or.inl hv) (fun hk => hup (hF.recip v u hk).2.1) (by rw [hF.pin_face hup]; simp)
      rw [extendFixFace_pin τ hup, hrep v hv] at this
      have e : repI hF v hv = a := Subtype.ext hva
      rw [e] at this
      exact this
    · obtain ⟨hne, v, u, hch, hv, hu, hva, hub⟩ := hab
      have hnf : ¬ (face v = some u ∨ face u = some v) := fun h => hne (Subtype.ext (by
        rw [← hva, ← hub]; exact (hF.repV_eq_iff hch hv hu).mpr h))
      have := h2 v u hch (Or.inl hv) (fun h => hnf (Or.inl h)) (fun h => hnf (Or.inr h))
      rw [hrep v hv, hrep u hu] at this
      have e1 : repI hF v hv = a := Subtype.ext hva
      have e2 : repI hF u hu = b := Subtype.ext hub
      rwa [e1, e2] at this
  · intro hO
    refine ⟨fun v hv hg => ?_, fun v u hch hor hvu huv => ?_⟩
    · have hO1 := (hO.1 ⟨v, hv, hg⟩).1
      have hO2 := hO.2.1 ⟨v, hv, hg⟩
      rw [extendFixFace_free τ ⟨v, hv, hg⟩]
      refine ⟨⟨(layer_le_lsF layer _).trans hO1, (hO2.trans_le (capF_le_layer layer rootTime _)).le⟩,
        hO2.trans_le (capF_le_root layer rootTime _)⟩
    · by_cases hv : fix v = none <;> by_cases hu : fix u = none
      · rw [hrep v hv, hrep u hu]
        refine hO.2.2 _ _ ⟨fun e => ?_, v, u, hch, hv, hu, rfl, rfl⟩
        have : repV face v = repV face u := congrArg Subtype.val e
        rcases (hF.repV_eq_iff hch hv hu).mp this with h | h
        · exact hvu h
        · exact huv h
      · rw [hrep v hv, extendFixFace_pin τ hu]
        have hmem : u ∈ capSrc fix face (repI hF v hv) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, v, hch, hv, rfl⟩
        exact (hO.2.1 _).trans_le (capF_le_pin layer rootTime hmem)
      · rw [extendFixFace_pin τ hv, hrep u hu]
        have hmem : v ∈ floorSrc fix face (repI hF u hu) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, u, hch, hu, rfl⟩
        exact lt_of_le_of_lt (pin_le_lsF hO hmem)
          (lt_of_le_of_ne (hO.1 _).1 (fun h => hn1 _ h.symm))
      · rcases hor with h | h
        · exact absurd h hv
        · exact absurd h hu

/-! ### The phases regroup over the contraction fibres -/

/-- The fibre of an integration clock: the unpinned branches carried by it. -/
noncomputable def fib (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (a : Iv fix face) : Finset (GBranch G.tree) :=
  univ.filter fun b => fix b = none ∧ repV face b = a.1

/-- The frequency of an integration clock: the sum over its fibre. -/
noncomputable def shiftF (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (α : GBranch G.tree → ℝ) (a : Iv fix face) : ℝ :=
  ∑ b ∈ fib fix face a, α b

/-- The pinned phases. -/
noncomputable def pinPhase (fix : GBranch G.tree → Option ℝ) (α : GBranch G.tree → ℝ) : ℂ :=
  ∏ b ∈ univ.filter (fun b => fix b ≠ none), Complex.exp ((Real.pi * α b * pinVal fix b : ℝ) * Complex.I)

theorem norm_pinPhase (α : GBranch G.tree → ℝ) : ‖pinPhase fix α‖ = 1 := by
  unfold pinPhase
  rw [norm_prod]
  exact Finset.prod_eq_one fun _ _ => Complex.norm_exp_ofReal_mul_I _

theorem phase_regroup (hF : FaceOK fix face) (α : GBranch G.tree → ℝ) (τ : Iv fix face → ℝ) :
    ∏ v : GBranch G.tree, Complex.exp ((Real.pi * α v * extendFixFace G fix face τ v : ℝ) * Complex.I) =
      pinPhase fix α * ∏ a : Iv fix face, Complex.exp ((Real.pi * shiftF fix face α a * τ a : ℝ) * Complex.I) := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun b => fix b ≠ none)]
  congr 1
  · refine Finset.prod_congr rfl fun b hb => ?_
    rw [extendFixFace_pin τ (Finset.mem_filter.mp hb).2]
  · set T : Finset (GBranch G.tree) := univ.filter (fun a => fix a = none ∧ face a = none) with hT
    set U : Finset (GBranch G.tree) := univ.filter (fun b => ¬ fix b ≠ none) with hU
    have hmaps : ∀ b ∈ U, repV face b ∈ T := by
      intro b hb
      have hb' : fix b = none := by simpa [hU] using hb
      simpa [hT] using hF.repV_free hb'
    rw [← Finset.prod_fiberwise_of_maps_to hmaps]
    set g : GBranch G.tree → ℂ := fun j => Complex.exp ((Real.pi * (∑ i ∈ U.filter (fun i => repV face i = j), α i) *
      ttv fix face τ j : ℝ) * Complex.I) with hg
    have h1 : ∀ j ∈ T, ∏ i ∈ U with repV face i = j,
        Complex.exp ((Real.pi * α i * extendFixFace G fix face τ i : ℝ) * Complex.I) = g j := by
      intro j _
      have : ∀ i ∈ U.filter (fun i => repV face i = j), extendFixFace G fix face τ i = ttv fix face τ j := by
        intro i hi
        obtain ⟨hiU, hij⟩ := Finset.mem_filter.mp hi
        have hi' : fix i = none := by simpa [hU] using hiU
        rw [extendFixFace_unpin τ hi', hij]
      rw [Finset.prod_congr rfl (fun i hi => by rw [this i hi]), ← Complex.exp_sum, hg]
      congr 1
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    rw [Finset.prod_congr rfl h1, Finset.prod_subtype T (p := fun a => fix a = none ∧ face a = none) (by simp [hT]) g]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hfib : U.filter (fun b => repV face b = a.1) = fib fix face a := by
      ext b; simp [hU, fib]
    rw [hg]
    simp only [hfib]
    have : ttv fix face τ a.1 = τ a := by simp [ttv, a.2.1, a.2.2]
    rw [this]
    rfl

/-- **The face Fourier transform is the generic one on the contracted domain** (norm). -/
theorem enorm_splicedFourierBMKFace_eq (hF : FaceOK fix face) (layer : GBranch G.tree → ℕ)
    (rootTime : Fin w → ℝ) (α : GBranch G.tree → ℝ) :
    ‖splicedFourierBMKFace G layer rootTime fix face α‖ₑ =
      ‖Phi (Om0 (chF fix face) (lsF layer fix face) (capF layer rootTime fix face)) (lsF layer fix face) ∅
        (shiftF fix face α)‖ₑ := by
  unfold splicedFourierBMKFace Phi
  have hpt : ∀ τ : Iv fix face → ℝ, τ ∉ nullFF layer fix face →
      (splicedTimeDomainFace G layer rootTime fix face).indicator
        (fun t => ∏ v : GBranch G.tree, Complex.exp ((Real.pi * α v * t v : ℝ) * Complex.I))
        (extendFixFace G fix face τ) =
      pinPhase fix α * (Om0 (chF fix face) (lsF layer fix face) (capF layer rootTime fix face)).indicator
        (famInt (lsF layer fix face) ∅ (shiftF fix face α)) τ := by
    intro τ hτ
    by_cases hm : extendFixFace G fix face τ ∈ splicedTimeDomainFace G layer rootTime fix face
    · have hm' := (domFace_iff hF layer rootTime τ hτ).mp hm
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm', phase_regroup hF α τ]
      simp [famInt]
    · have hm' : τ ∉ Om0 (chF fix face) (lsF layer fix face) (capF layer rootTime fix face) :=
        fun h => hm ((domFace_iff hF layer rootTime τ hτ).mpr h)
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm', mul_zero]
  have hae : ∀ᵐ τ : Iv fix face → ℝ, τ ∉ nullFF layer fix face :=
    measure_eq_zero_iff_ae_notMem.mp (volume_nullFF layer)
  rw [integral_congr_ae (hae.mono hpt), integral_const_mul, enorm_mul]
  have : ‖pinPhase fix α‖ₑ = 1 := by rw [← ofReal_norm, norm_pinPhase]; simp
  rw [this, one_mul]

end WaveTurbulence.Flower.FinalMKPin
