/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Surj

/-! # BOT-DECOMP: the mixed approximant families for the bottom class (mirror of `P1.Mix`, `P1.Mix2`, `P1.Rem`)

`botQfam = mixFam botTrQ botEx botLq botQ0` etc., over the index type `BT`; `bot_hsub`, `bot_hQ0`, `bot_hT0`, `bot_hreal` (from `RealityAll` via
`bot_carrier_sum_eq`), and the identification of the remainders with the gate remainders (`bot_remQ_eq`, `bot_remT_eq`).
The extension lemmas `P1.couple_eq_ext`, `P1.tree_eq_ext`, `P1.couple_root_vanish`, `P1.tree_root_vanish` are state-free and reused.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.ConjCoh TTree
  WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS5C

set_option linter.unusedSectionVars false

section
variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {d : ℕ} [Fintype ι] [DecidableEq ι] (pstar : ι)

/-- The root layer of the carrier-side couple of the index `b`. -/
noncomputable def botLq (b : BT w ι) : ℕ := cplRootLayer (zpObjC b.1 pstar)

/-- The root layer of the carrier-side tree of the index `b`. -/
noncomputable def botLt (b : BT w ι) : ℕ := treeRootLayer (zpObjT b.1 pstar)

/-- The carrier-side couple of `b` is the trivial couple. -/
def botTrQ (b : BT w ι) : Prop := zpCodeC b.1 pstar = RegCpl.triv

/-- The carrier-side tree of `b` is the trivial tree. -/
def botTrT (b : BT w ι) : Prop := zpCodeT b.1 pstar = RegChain.nil

/-- The root-layer instance of the couple approximant: `SourceApp.couple` at `(Lr, L₂)`. -/
noncomputable def botQ0 (κ : KPar d) (A : FamilyReconstruction w ι) (b : BT w ι) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => LGSpine.SourceApp.couple κ.δ κ.F (zpObjC b.1 pstar) (zpCodeC b.1 pstar) (botLq pstar b) (zpQ2 A pstar) t s k

/-- The root-layer instance of the tree approximant. -/
noncomputable def botT0 (κ : KPar d) (A : FamilyReconstruction w ι) (b : BT w ι) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => LGSpine.SourceApp.tree κ.δ κ.F (zpObjT b.1 pstar) (zpCodeT b.1 pstar) (botLt pstar b) (zpQ2 A pstar) t s k

open Classical in
/-- R35: the exact kernel of a trivial couple, `F · 1_{t > Lq}`. -/
noncomputable def botEx (κ : KPar d) (A : FamilyReconstruction w ι) (b : BT w ι) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => if (botLq pstar b : ℝ) < t then extFam (botLq pstar) (botQ0 pstar κ A) b t s k else 0

open Classical in
/-- R35 for trees. -/
noncomputable def botEt (κ : KPar d) (A : FamilyReconstruction w ι) (b : BT w ι) : ℝ → ℝ → Mom d → ℂ :=
  fun t s k => if (botLt pstar b : ℝ) < t then extFam (botLt pstar) (botT0 pstar κ A) b t s k else 0

/-- **`Qf`**: the approximant family of the couples (`mixFam`). -/
noncomputable def botQfam (κ : KPar d) (A : FamilyReconstruction w ι) : BT w ι → ℝ → ℝ → Mom d → ℂ :=
  mixFam (botTrQ pstar) (botEx pstar κ A) (botLq pstar) (botQ0 pstar κ A)

/-- **`Tf`**: the approximant family of the trees (`mixFam`). -/
noncomputable def botTfam (κ : KPar d) (A : FamilyReconstruction w ι) : BT w ι → ℝ → ℝ → Mom d → ℂ :=
  mixFam (botTrT pstar) (botEt pstar κ A) (botLt pstar) (botT0 pstar κ A)

variable (p kind) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)

open Classical in
/-- `botA ∪ botB` with the classical union instance used by `replSum_decomp_ext`. -/
noncomputable def botBsU : Finset (BT w ι) :=
  @Union.union (Finset (BT w ι)) (@Finset.instUnion _ fun a b => Classical.propDecidable (a = b))
    (botA p kind pstar A c0) (botB p kind pstar A c0)

theorem mem_botBsU {b : BT w ι} : b ∈ botBsU p kind pstar A c0 ↔ b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0 := by
  unfold botBsU; exact @Finset.mem_union _ (fun a b => Classical.propDecidable (a = b)) _ _ _

theorem bot_mem_of_bs {b : BT w ι} (h : b ∈ botBsU p kind pstar A c0) : b ∈ canonFinsetK p kind A c0 := by
  classical
  rcases (mem_botBsU p kind pstar A c0).mp h with h | h
  · exact (Finset.mem_filter.mp h).1
  · exact (Finset.mem_filter.mp h).1

open Classical in
/-- **`hsub`**: `b ∈ botA ∪ botB` with both roots `≤ L₄` lies in `botA ∩ botB`. -/
theorem bot_hsub : ∀ b ∈ botBsU p kind pstar A c0, botLq pstar b ≤ zpQ4 A pstar → botLt pstar b ≤ zpQ4 A pstar →
    b ∈ botA p kind pstar A c0 ∧ b ∈ botB p kind pstar A c0 := by
  classical
  intro b hb h1 h2
  have hroots : ZpRootsLE A b.1 pstar := ⟨h1, h2⟩
  have hz := bot_mem_of_bs p kind pstar A c0 hb
  have hn : nuOf b.1 pstar ≠ 1 := by
    intro hn1
    rcases (mem_botBsU p kind pstar A c0).mp hb with h | h
    · rcases (Finset.mem_filter.mp h).2 with ⟨hn, -⟩ | ⟨-, hr⟩
      · exact hn hn1
      · exact hr hroots
    · exact (Finset.mem_filter.mp h).2 hn1
  refine ⟨Finset.mem_filter.mpr ⟨hz, Or.inl ⟨hn, hroots⟩⟩, Finset.mem_filter.mpr ⟨hz, hn⟩⟩

open Classical in
/-- The leading-sum index set is the set of II-b states with roots `≤ L₄`. -/
theorem bot_filter_eq :
    (botBsU p kind pstar A c0).filter (fun b => botLq pstar b ≤ zpQ4 A pstar ∧ botLt pstar b ≤ zpQ4 A pstar) =
      botMinusFin p kind pstar A c0 := by
  ext b
  simp only [Finset.mem_filter, botMinusFin]
  constructor
  · rintro ⟨hb, h1, h2⟩
    have hz := bot_mem_of_bs p kind pstar A c0 hb
    have hbb := bot_hsub p kind pstar A c0 b hb h1 h2
    have hn : nuOf b.1 pstar ≠ 1 := (Finset.mem_filter.mp hbb.2).2
    exact ⟨hz, (units_ne_one_iff _).mp hn, h1, h2⟩
  · rintro ⟨hz, hn, h1, h2⟩
    have hn' : nuOf b.1 pstar ≠ 1 := (units_ne_one_iff _).mpr hn
    exact ⟨(mem_botBsU p kind pstar A c0).mpr (Or.inr (Finset.mem_filter.mpr ⟨hz, hn'⟩)), h1, h2⟩

/-- **`hQ0`** (R35 repair): endpoint vanishing for a couple whose root layer exceeds `L₄`. -/
theorem bot_hQ0 (hZ : BotSurj p kind pstar A c0) (hL : BotLayers p kind pstar A c0) (κ : KPar d) {b : BT w ι}
    (hb : b ∈ canonFinsetK p kind A c0) (hgt : zpQ4 A pstar < botLq pstar b) (s : ℝ) (k : Mom d) :
    botQ0 pstar κ A b (botLq pstar b : ℝ) s k = 0 := by
  obtain ⟨h2, hle, hp⟩ := hL.pair b hb
  have hc := (hZ.coherent b hb).1
  rw [h2] at hc hle
  exact P1.couple_root_vanish κ.δ κ.F hle hp hc (lt_of_le_of_lt hL.le hgt) s k

/-- **`hT0`** (R35 repair), the tree analogue. -/
theorem bot_hT0 (hZ : BotSurj p kind pstar A c0) (hL : BotLayers p kind pstar A c0) (κ : KPar d) {b : BT w ι}
    (hb : b ∈ canonFinsetK p kind A c0) (hgt : zpQ4 A pstar < botLt pstar b) (s : ℝ) (k : Mom d) :
    botT0 pstar κ A b (botLt pstar b : ℝ) s k = 0 := by
  obtain ⟨h2, hle⟩ := hL.branch b hb
  have hc := (hZ.coherent b hb).2
  rw [h2] at hc hle
  exact P1.tree_root_vanish κ.δ κ.F hle hc (lt_of_le_of_lt hL.le hgt) s k

/-- On the carrier the extension families are the source approximants at `(L₄, L₂)` on the unit window `t ∈ [L₄, L₄+1]`. -/
theorem bot_ext_eq_source (hZ : BotSurj p kind pstar A c0) (hL : BotLayers p kind pstar A c0) (κ : KPar d)
    {b : BT w ι} (hb : b ∈ botMinusFin p kind pstar A c0) {t : ℝ} (h1 : (zpQ4 A pstar : ℝ) ≤ t)
    (h2 : t ≤ zpQ4 A pstar + 1) (s : ℝ) (k : Mom d) :
    extFam (botLq pstar) (botQ0 pstar κ A) b t s k = SourceApp.couple κ.δ κ.F (zpObjC b.1 pstar) (zpCodeC b.1 pstar)
        (zpQ4 A pstar) (zpQ2 A pstar) t s k ∧
      extFam (botLt pstar) (botT0 pstar κ A) b t s k = SourceApp.tree κ.δ κ.F (zpObjT b.1 pstar) (zpCodeT b.1 pstar)
        (zpQ4 A pstar) (zpQ2 A pstar) t s k := by
  have hm : b ∈ botSet p kind pstar A c0 (-1) := by rw [← coe_botMinusFin p kind pstar A c0]; exact hb
  obtain ⟨hcQ, hcT, -⟩ := hZ.carrier.mapsTo hm
  exact ⟨(P1.couple_eq_ext κ.δ κ.F hL.le hL.le_p hcQ s k h1 h2).symm, (P1.tree_eq_ext κ.δ κ.F hL.le hcT s k h1 h2).symm⟩

open Classical in
/-- **`hreal`** for the mixed families: from `RealityAll` (PL234 `reality_all`), `bot_carrier_sum_eq` and the extension lemma. -/
theorem bot_hreal (hR : P1.RealityAll) (hZ : BotSurj p kind pstar A c0) (hL : BotLayers p kind pstar A c0) (κ : KPar d)
    {t0 t1 : ℝ} (x : Mom d) (h1 : (zpQ4 A pstar : ℝ) < t1) (h1' : t1 ≤ zpQ4 A pstar + 1)
    (h0 : (zpQ2 A pstar : ℝ) ≤ t0) (h0' : t0 ≤ zpQ2 A pstar + 1) (hlt : t0 < t1) :
    (∑ b ∈ (botBsU p kind pstar A c0).filter (fun b => botLq pstar b ≤ zpQ4 A pstar ∧ botLt pstar b ≤ zpQ4 A pstar),
      botQfam pstar κ A b t1 t0 x * (starRingEnd ℂ) (botTfam pstar κ A b t1 t0 x)).im = 0 := by
  have hext : (∑ b ∈ (botBsU p kind pstar A c0).filter
        (fun b => botLq pstar b ≤ zpQ4 A pstar ∧ botLt pstar b ≤ zpQ4 A pstar),
      extFam (botLq pstar) (botQ0 pstar κ A) b t1 t0 x *
        (starRingEnd ℂ) (extFam (botLt pstar) (botT0 pstar κ A) b t1 t0 x)).im = 0 := by
    rw [bot_filter_eq p kind pstar A c0]
    have hr := hR κ.δ κ.F hL.le hL.le_p (zpN A pstar) (zpTop p A pstar) ![t1, t0]
      ⟨⟨⟨h1.le, h1'⟩, ⟨h0, h0'⟩⟩, by simpa using hlt⟩ x
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hr
    have hcs := bot_carrier_sum_eq p kind pstar A c0 hZ.carrier
      (fun Q X LQ LX => SourceApp.couple κ.δ κ.F LQ Q (zpQ4 A pstar) (zpQ2 A pstar) t1 t0 x *
        star (SourceApp.tree κ.δ κ.F LX X (zpQ4 A pstar) (zpQ2 A pstar) t1 t0 x))
    beta_reduce at hcs
    rw [hcs] at hr
    have hsum : (∑ b ∈ botMinusFin p kind pstar A c0,
        extFam (botLq pstar) (botQ0 pstar κ A) b t1 t0 x *
          (starRingEnd ℂ) (extFam (botLt pstar) (botT0 pstar κ A) b t1 t0 x)) =
        ∑ b ∈ botMinusFin p kind pstar A c0,
          SourceApp.couple κ.δ κ.F (zpCarrierOf b.1 pstar).2.2.1 (zpCarrierOf b.1 pstar).1 (zpQ4 A pstar)
            (zpQ2 A pstar) t1 t0 x *
          star (SourceApp.tree κ.δ κ.F (zpCarrierOf b.1 pstar).2.2.2 (zpCarrierOf b.1 pstar).2.1 (zpQ4 A pstar)
            (zpQ2 A pstar) t1 t0 x) := by
      refine Finset.sum_congr rfl fun b hb => ?_
      have := bot_ext_eq_source p kind pstar A c0 hZ hL κ hb h1.le h1' t0 x
      rw [this.1, this.2]
      rfl
    rw [hsum]
    exact hr
  refine hreal_mix_of_ext (botBsU p kind pstar A c0) (botLq pstar) (botLt pstar) (zpQ4 A pstar) (botTrQ pstar) (botTrT pstar)
    (botEx pstar κ A) (botEt pstar κ A) (botQ0 pstar κ A) (botT0 pstar κ A) ?_ ?_ t0 t1 x h1 hext
  · intro b hb t ht s k
    simp [botEx, ht]
  · intro b hb t ht s k
    simp [botEt, ht]

/-! ### The remainders in the native window are the gate remainders -/

theorem bot_Qf_eq_srcQ (hZ : BotSurj p kind pstar A c0) (hL : BotLayers p kind pstar A c0) (κ : KPar d)
    {b : BT w ι} (hb : b ∈ canonFinsetK p kind A c0) {t : ℝ}
    (h1 : ((zpQQ b.1 pstar).1 : ℝ) ≤ t) (h2 : t ≤ (zpQQ b.1 pstar).1 + 1)
    (hne : (botLq pstar b : ℝ) < t ∨ ¬ botTrQ pstar b) (s : ℝ) (k : Mom d) :
    botQfam pstar κ A b t s k = botSrcQ pstar κ b t s k := by
  obtain ⟨h2', hle, hp⟩ := hL.pair b hb
  have hc := (hZ.coherent b hb).1
  rw [h2'] at hc hle
  have hext := P1.couple_eq_ext κ.δ κ.F hle hp hc s k h1 h2
  have hq : botQfam pstar κ A b t s k = extFam (botLq pstar) (botQ0 pstar κ A) b t s k := by
    unfold botQfam
    rcases hne with hlt | hn
    · exact mixFam_eq_extFam_of_lt (fun b _ t ht s k => by simp [botEx, ht]) hlt s k
    · exact mixFam_of_not hn t s k
  rw [hq]
  unfold botSrcQ
  rw [h2']
  exact hext.symm

theorem bot_Tf_eq_srcT (hZ : BotSurj p kind pstar A c0) (hL : BotLayers p kind pstar A c0) (κ : KPar d)
    {b : BT w ι} (hb : b ∈ canonFinsetK p kind A c0) {t : ℝ}
    (h1 : ((zpBranchQ b.1 pstar).1 : ℝ) ≤ t) (h2 : t ≤ (zpBranchQ b.1 pstar).1 + 1)
    (hne : (botLt pstar b : ℝ) < t ∨ ¬ botTrT pstar b) (s : ℝ) (k : Mom d) :
    botTfam pstar κ A b t s k = botSrcT pstar κ b t s k := by
  obtain ⟨h2', hle⟩ := hL.branch b hb
  have hc := (hZ.coherent b hb).2
  rw [h2'] at hc hle
  have hext := P1.tree_eq_ext κ.δ κ.F hle hc s k h1 h2
  have hq : botTfam pstar κ A b t s k = extFam (botLt pstar) (botT0 pstar κ A) b t s k := by
    unfold botTfam
    rcases hne with hlt | hn
    · exact mixFam_eq_extFam_of_lt (fun b _ t ht s k => by simp [botEt, ht]) hlt s k
    · exact mixFam_of_not hn t s k
  rw [hq]
  unfold botSrcT
  rw [h2']
  exact hext.symm

/-- **The couple remainder in the native window is the gate remainder `K* - SourceApp`.** -/
theorem bot_remQ_eq (hZ : BotSurj p kind pstar A c0) (hL : BotLayers p kind pstar A c0) (κ : KPar d)
    {b : BT w ι} (hb : b ∈ canonFinsetK p kind A c0) {t : ℝ}
    (h1 : ((zpQQ b.1 pstar).1 : ℝ) ≤ t) (h2 : t ≤ (zpQQ b.1 pstar).1 + 1)
    (hne : (botLq pstar b : ℝ) < t ∨ ¬ botTrQ pstar b) (s : ℝ) (k : Mom d) :
    botRemQ pstar κ (botQfam pstar κ A) b t s k = KQstar κ.L κ.γ κ.δ κ.F (zpObjC b.1 pstar) t s k - botSrcQ pstar κ b t s k := by
  unfold botRemQ
  rw [bot_Qf_eq_srcQ p kind pstar A c0 hZ hL κ hb h1 h2 hne]

/-- **The tree remainder in the native window is the gate remainder `K* - SourceApp`.** -/
theorem bot_remT_eq (hZ : BotSurj p kind pstar A c0) (hL : BotLayers p kind pstar A c0) (κ : KPar d)
    {b : BT w ι} (hb : b ∈ canonFinsetK p kind A c0) {t : ℝ}
    (h1 : ((zpBranchQ b.1 pstar).1 : ℝ) ≤ t) (h2 : t ≤ (zpBranchQ b.1 pstar).1 + 1)
    (hne : (botLt pstar b : ℝ) < t ∨ ¬ botTrT pstar b) (s : ℝ) (k : Mom d) :
    botRemT pstar κ (botTfam pstar κ A) b t s k = KTstar κ.L κ.γ κ.δ κ.F (zpObjT b.1 pstar) t s k - botSrcT pstar κ b t s k := by
  unfold botRemT
  rw [bot_Tf_eq_srcT p kind pstar A c0 hZ hL κ hb h1 h2 hne]

end
end WaveTurbulence.VineEstS5C.P4.Bot
