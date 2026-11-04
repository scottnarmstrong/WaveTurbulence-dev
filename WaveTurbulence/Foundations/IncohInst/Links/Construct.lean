/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Locality

/-!
# Decorations from link parameters (packet C2)

Given a root value `r` and parameters `θ` (a pair `(x, y)` at every chosen node), `cplVal θ Q a b r`
is a decoration of the code `Q` placed at `(a, b)`: at a chosen node `𝔫` of value `u` the children
get the values `(u + x, u + x - y, u - y)`, and the rest is forced by the links and the leaf pairs.
This is the construction behind the unimodular change of variables `(k_ℓ) ↔ (x_𝔫, y_𝔫)` of
TARGET (incohproof1) (L983–L990).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {V : Type*} [AddCommGroup V] {w : ℕ}

/-- The values `(u + x, u + x - y, u - y)` of the children of a node of value `u` with parameters
`θ = (x, y)`. -/
def childVals (u : V) (θ : V × V) : Fin 3 → V := ![u + θ.1, u + θ.1 - θ.2, u - θ.2]

theorem childVals_rel (u : V) (θ : V × V) :
    u = childVals u θ 0 - childVals u θ 1 + childVals u θ 2 := by
  simp only [childVals, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  abel

mutual
/-- The decoration of the couple code `Q` at `(a, b)` with root value `r` and parameters `θ`. -/
def cplVal (θ : Fin w × Path → V × V) : RegCpl → (Fin w × Path) → (Fin w × Path) → V →
    (Fin w × Path) → V
  | .triv, a, b, r => fun z => if z = a ∨ z = b then r else 0
  | .type1 c Q₁ Q₂ Q₃, a, b, r => fun z =>
    if z = a ∨ z = b then r
    else if Under (addrExt a [0]) z ∨ Under (addrExt b [c.partner 0]) z then
      cplVal θ Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) (childVals r (θ a) 0) z
    else if Under (addrExt b [1]) z ∨ Under (addrExt a [1]) z then
      cplVal θ Q₂ (addrExt b [1]) (addrExt a [1]) (childVals r (θ a) 1) z
    else cplVal θ Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) (childVals r (θ a) 2) z
  | .type2 Xp Xm Qlp, a, b, r => fun z =>
    if Under a z then
      chainVal θ Xp 1 a r (cplVal θ Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r) z
    else chainVal θ Xm (-1) b r (cplVal θ Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r) z

/-- The decoration of the chain code `X` at `a` with root value `u`, continued by `cont` below its
lone position. -/
def chainVal (θ : Fin w × Path → V × V) : RegChain → ℤˣ → (Fin w × Path) → V →
    ((Fin w × Path) → V) → (Fin w × Path) → V
  | .nil, _, _, _, cont => cont
  | .pair m Qr Qg inner rest, ζ, a, u, cont => fun z =>
    if z = a then u
    else if Under (addrExt a [m.red.1]) z ∨
        Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) z then
      (if slotSign ζ m.red.1 = 1 then
        cplVal θ Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
          (childVals u (θ a) m.red.1)
      else cplVal θ Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])
          (childVals u (θ a) m.red.1)) z
    else if Under (addrExt a [m.green.1]) z ∨
        Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) z then
      (if slotSign ζ m.green.1 = 1 then
        cplVal θ Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
          (childVals u (θ a) m.green.1)
      else cplVal θ Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])
          (childVals u (θ a) m.green.1)) z
    else if Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) z then
      chainVal θ rest (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) u cont z
    else chainVal θ inner (slotSign ζ m.c) (addrExt a [m.c]) (childVals u (θ a) m.c)
        (fun _ => childVals u (θ a) m.c) z
end

/-- Two independent positions: neither lies below the other. -/
def Indep (a b : Fin w × Path) : Prop := ¬ Under a b ∧ ¬ Under b a

theorem Indep.symm {a b : Fin w × Path} (h : Indep a b) : Indep b a := ⟨h.2, h.1⟩

theorem Indep.not_both {a b z : Fin w × Path} (h : Indep a b) (ha : Under a z) (hb : Under b z) :
    False := (under_total ha hb).elim h.1 h.2

theorem Indep.ext {a b : Fin w × Path} (h : Indep a b) (p q : Path) :
    Indep (addrExt a p) (addrExt b q) :=
  ⟨fun hu => h.not_both (under_trans (under_ext a p) hu) (under_ext b q),
    fun hu => h.not_both (under_ext a p) (under_trans (under_ext b q) hu)⟩

theorem indep_branch (a : Fin w × Path) (p : Path) {i j : Fin 3} (hij : i ≠ j) (s t : Path) :
    Indep (addrExt a (p ++ i :: s)) (addrExt a (p ++ j :: t)) :=
  ⟨fun hu => not_under_branch p hij s t hu (under_refl _),
    fun hu => not_under_branch p hij s t (under_refl _) hu⟩

theorem ne_of_under_cons {a z : Fin w × Path} (i : Fin 3) (p : Path)
    (h : Under (addrExt a (i :: p)) z) : z ≠ a := fun e => by
  subst e
  have := under_length h
  simp [addrExt] at this

theorem addrExt_nil (a : Fin w × Path) : addrExt a [] = a := by simp [addrExt]

/-! ### Chains: root value, continuation -/

theorem chainVal_root (θ : Fin w × Path → V × V) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (u : V)
    (cont : (Fin w × Path) → V) (hc : cont (addrExt a X.lonePath) = u) :
    chainVal θ X ζ a u cont a = u := by
  cases X with
  | nil => simpa [chainVal, RegChain.lonePath, addrExt_nil] using hc
  | pair m Qr Qg inner rest => simp [chainVal]

/-- The chain region and the region of its red couple. -/
theorem chain_regions {m : MiniTreeCode} {L : Path} {a z : Fin w × Path} :
    (Under (addrExt a ([m.c] ++ L ++ [m.lone])) z →
      ¬ (Under (addrExt a [m.red.1]) z ∨ Under (addrExt a ([m.c] ++ L ++ [m.red.2])) z) ∧
      ¬ (Under (addrExt a [m.green.1]) z ∨ Under (addrExt a ([m.c] ++ L ++ [m.green.2])) z)) ∧
    ((Under (addrExt a [m.green.1]) z ∨ Under (addrExt a ([m.c] ++ L ++ [m.green.2])) z) →
      ¬ (Under (addrExt a [m.red.1]) z ∨ Under (addrExt a ([m.c] ++ L ++ [m.red.2])) z)) := by
  have e : ∀ x : Fin 3, [m.c] ++ L ++ [x] = (m.c :: L) ++ x :: [] := fun x => by simp
  have e' : ∀ x : Fin 3, [m.c] ++ L ++ [x] = [] ++ m.c :: (L ++ [x]) := fun x => by simp
  have e1 : ∀ x : Fin 3, [x] = [] ++ x :: [] := fun x => rfl
  refine ⟨fun hl => ⟨?_, ?_⟩, ?_⟩
  · rintro (h | h)
    · rw [e1] at h; rw [e'] at hl
      exact not_under_branch [] (red_ne_c m) [] _ h hl
    · rw [e] at h hl
      exact not_under_branch _ (red2_ne_lone m) [] [] h hl
  · rintro (h | h)
    · rw [e1] at h; rw [e'] at hl
      exact not_under_branch [] (green_ne_c m) [] _ h hl
    · rw [e] at h hl
      exact not_under_branch _ (green2_ne_lone m) [] [] h hl
  · rintro (hg | hg) (hr | hr)
    · rw [e1] at hg hr
      exact not_under_branch [] (red_ne_green m) [] [] hr hg
    · rw [e1] at hg; rw [e'] at hr
      exact not_under_branch [] (green_ne_c m) [] _ hg hr
    · rw [e'] at hg; rw [e1] at hr
      exact not_under_branch [] (red_ne_c m) [] _ hr hg
    · rw [e] at hg hr
      exact not_under_branch _ (red2_ne_green2 m) [] [] hr hg

/-- Below its lone position a chain's decoration is the continuation. -/
theorem chainVal_lone (θ : Fin w × Path → V × V) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (u : V)
    (cont : (Fin w × Path) → V) (z : Fin w × Path) (hz : Under (addrExt a X.lonePath) z) :
    chainVal θ X ζ a u cont z = cont z := by
  cases X with
  | nil => rfl
  | pair m Qr Qg inner rest =>
    have hlp : addrExt a (RegChain.pair m Qr Qg inner rest).lonePath =
        addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath := by
      simp [RegChain.lonePath, addrExt_append]
    rw [hlp] at hz
    have hl : Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) z :=
      under_trans (under_ext _ _) hz
    have ha : z ≠ a := ne_of_under_cons m.c _ (by simpa using hl)
    obtain ⟨hr, hg⟩ := (chain_regions (m := m) (L := inner.lonePath)).1 hl
    simp only [chainVal, ha, hr, hg, hl, ↓reduceIte]
    exact chainVal_lone θ rest _ _ u cont z hz

/-! ### Couples: regions, root values -/

theorem partner_ne_one (c : MiniCplCode) (x : Fin 3) (hx : x ≠ 1) : c.partner x ≠ 1 := by
  fin_cases c <;> fin_cases x <;> simp_all [MiniCplCode.partner] <;> decide

theorem partner_ne (c : MiniCplCode) : c.partner 0 ≠ c.partner 2 := by
  fin_cases c <;> decide

theorem not_ab_of_under {a b z : Fin w × Path} (h : Indep a b) {i : Fin 3}
    (hz : Under (addrExt a [i]) z) : ¬ (z = a ∨ z = b) := by
  rintro (rfl | rfl)
  · exact ne_of_under_cons i [] hz rfl
  · exact h.1 (under_trans (under_ext a [i]) hz)

theorem type1_regions {a b z : Fin w × Path} (h : Indep a b) (c : MiniCplCode) :
    ((Under (addrExt a [0]) z ∨ Under (addrExt b [c.partner 0]) z) → ¬ (z = a ∨ z = b)) ∧
    ((Under (addrExt b [1]) z ∨ Under (addrExt a [1]) z) → ¬ (z = a ∨ z = b) ∧
      ¬ (Under (addrExt a [0]) z ∨ Under (addrExt b [c.partner 0]) z)) ∧
    ((Under (addrExt a [2]) z ∨ Under (addrExt b [c.partner 2]) z) → ¬ (z = a ∨ z = b) ∧
      ¬ (Under (addrExt a [0]) z ∨ Under (addrExt b [c.partner 0]) z) ∧
      ¬ (Under (addrExt b [1]) z ∨ Under (addrExt a [1]) z)) := by
  have br : ∀ (x : Fin w × Path) {i j : Fin 3}, i ≠ j → Under (addrExt x [i]) z →
      Under (addrExt x [j]) z → False := fun x i j hij h1 h2 =>
    not_under_branch [] hij [] [] (by simpa using h1) (by simpa using h2)
  have ind : ∀ {i j : Fin 3}, Under (addrExt a [i]) z → Under (addrExt b [j]) z → False :=
    fun h1 h2 => h.not_both (under_trans (under_ext _ _) h1) (under_trans (under_ext _ _) h2)
  have nab : ∀ {i : Fin 3}, Under (addrExt b [i]) z → ¬ (z = a ∨ z = b) := fun hz e =>
    not_ab_of_under h.symm hz e.symm
  refine ⟨?_, ?_, ?_⟩
  · rintro (hz | hz)
    · exact not_ab_of_under h hz
    · exact nab hz
  · rintro (hz | hz)
    · refine ⟨nab hz, ?_⟩
      rintro (h' | h')
      · exact ind h' hz
      · exact br b (partner_ne_one c 0 (by decide)) h' hz
    · refine ⟨not_ab_of_under h hz, ?_⟩
      rintro (h' | h')
      · exact br a (by decide) h' hz
      · exact ind hz h'
  · rintro (hz | hz)
    · refine ⟨not_ab_of_under h hz, ?_, ?_⟩
      · rintro (h' | h')
        · exact br a (by decide) h' hz
        · exact ind hz h'
      · rintro (h' | h')
        · exact ind hz h'
        · exact br a (by decide) h' hz
    · refine ⟨nab hz, ?_, ?_⟩
      · rintro (h' | h')
        · exact ind h' hz
        · exact br b (partner_ne c) h' hz
      · rintro (h' | h')
        · exact br b (partner_ne_one c 2 (by decide)).symm h' hz
        · exact ind h' hz

/-- **The roots of the constructed decoration carry the root value.** -/
theorem cplVal_root (θ : Fin w × Path → V × V) (Q : RegCpl) (a b : Fin w × Path) (r : V)
    (h : Indep a b) : cplVal θ Q a b r a = r ∧ cplVal θ Q a b r b = r := by
  cases Q with
  | triv => simp [cplVal]
  | type1 c Q₁ Q₂ Q₃ => simp [cplVal]
  | type2 Xp Xm Qlp =>
    have hQ := cplVal_root θ Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) r (h.ext _ _)
    constructor
    · simp only [cplVal, under_refl, ↓reduceIte]
      exact chainVal_root θ Xp 1 a r _ hQ.1
    · simp only [cplVal, h.1, ↓reduceIte]
      exact chainVal_root θ Xm (-1) b r _ hQ.2

/-! ### Chains: the values around a chain pair -/

theorem slot_cases (m : MiniTreeCode) (i : Fin 3) : i = m.red.1 ∨ i = m.green.1 ∨ i = m.c := by
  obtain ⟨c, b⟩ := m; fin_cases c <;> fin_cases b <;> fin_cases i <;> decide

theorem slot_cases2 (m : MiniTreeCode) (i : Fin 3) : i = m.red.2 ∨ i = m.green.2 ∨ i = m.lone := by
  obtain ⟨c, b⟩ := m; fin_cases c <;> fin_cases b <;> fin_cases i <;> decide

/-- The second node of a chain pair satisfies the node relation once the first does. -/
theorem miniTree_consistent (m : MiniTreeCode) (u : V) (A B : Fin 3 → V)
    (hA : u = A 0 - A 1 + A 2) (hl : B m.lone = u) (hr : B m.red.2 = A m.red.1)
    (hg : B m.green.2 = A m.green.1) : A m.c = B 0 - B 1 + B 2 := by
  obtain ⟨c, b⟩ := m
  fin_cases c <;> fin_cases b <;>
    simp only [MiniTreeCode.red, MiniTreeCode.green, MiniTreeCode.lone] at hl hr hg ⊢ <;>
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Fin.succ_zero_eq_one] at hl hr hg ⊢ <;>
    rw [hl, hr, hg, hA] <;> abel

theorem sunder_of_under_cons {p z : Fin w × Path} (i : Fin 3) (q : Path)
    (h : Under (addrExt p (i :: q)) z) : SUnder p z :=
  ⟨under_trans (under_ext p _) h, ne_of_under_cons i q h⟩

theorem chain_inner_region {m : MiniTreeCode} {L : Path} {a z : Fin w × Path}
    (hz : Under (addrExt a [m.c]) z) (hn : ¬ SUnder (addrExt a ([m.c] ++ L)) z) :
    z ≠ a ∧
      ¬ (Under (addrExt a [m.red.1]) z ∨ Under (addrExt a ([m.c] ++ L ++ [m.red.2])) z) ∧
      ¬ (Under (addrExt a [m.green.1]) z ∨ Under (addrExt a ([m.c] ++ L ++ [m.green.2])) z) ∧
      ¬ Under (addrExt a ([m.c] ++ L ++ [m.lone])) z := by
  have e : ∀ x : Fin 3, addrExt a ([m.c] ++ L ++ [x]) = addrExt (addrExt a ([m.c] ++ L)) (x :: []) :=
    fun x => by rw [addrExt_append]
  refine ⟨ne_of_under_cons m.c [] hz, ?_, ?_, ?_⟩
  · rintro (h | h)
    · exact not_under_branch [] (red_ne_c m) [] [] (by simpa using h) (by simpa using hz)
    · rw [e] at h; exact hn (sunder_of_under_cons _ _ h)
  · rintro (h | h)
    · exact not_under_branch [] (green_ne_c m) [] [] (by simpa using h) (by simpa using hz)
    · rw [e] at h; exact hn (sunder_of_under_cons _ _ h)
  · intro h; rw [e] at h; exact hn (sunder_of_under_cons _ _ h)

theorem oriented_root (θ : Fin w × Path → V × V) (Q : RegCpl) (x y : Fin w × Path) (R : V)
    (p : Prop) [Decidable p] (h : Indep x y) :
    (if p then cplVal θ Q x y R else cplVal θ Q y x R) x = R ∧
      (if p then cplVal θ Q x y R else cplVal θ Q y x R) y = R := by
  split_ifs
  · exact cplVal_root θ Q x y R h
  · exact (cplVal_root θ Q y x R h.symm).symm

theorem indep_red (m : MiniTreeCode) (L : Path) (a : Fin w × Path) :
    Indep (addrExt a [m.red.1]) (addrExt a ([m.c] ++ L ++ [m.red.2])) := by
  have := indep_branch a [] (red_ne_c m) [] (L ++ [m.red.2])
  simpa using this

theorem indep_green (m : MiniTreeCode) (L : Path) (a : Fin w × Path) :
    Indep (addrExt a [m.green.1]) (addrExt a ([m.c] ++ L ++ [m.green.2])) := by
  have := indep_branch a [] (green_ne_c m) [] (L ++ [m.green.2])
  simpa using this

/-- The values of the constructed chain decoration around its first pair. -/
theorem chainVal_pair_vals (θ : Fin w × Path → V × V) (m : MiniTreeCode) (Qr Qg : RegCpl)
    (inner rest : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (u : V) (cont : (Fin w × Path) → V)
    (hc : cont (addrExt a (RegChain.pair m Qr Qg inner rest).lonePath) = u) :
    (∀ i, chainVal θ (.pair m Qr Qg inner rest) ζ a u cont (addrExt a [i]) = childVals u (θ a) i) ∧
    chainVal θ (.pair m Qr Qg inner rest) ζ a u cont (addrExt a ([m.c] ++ inner.lonePath)) =
      childVals u (θ a) m.c ∧
    chainVal θ (.pair m Qr Qg inner rest) ζ a u cont
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) = u ∧
    chainVal θ (.pair m Qr Qg inner rest) ζ a u cont
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) = childVals u (θ a) m.red.1 ∧
    chainVal θ (.pair m Qr Qg inner rest) ζ a u cont
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) = childVals u (θ a) m.green.1 := by
  have hR := oriented_root θ Qr _ _ (childVals u (θ a) m.red.1) (slotSign ζ m.red.1 = 1)
    (indep_red m inner.lonePath a)
  have hG := oriented_root θ Qg _ _ (childVals u (θ a) m.green.1) (slotSign ζ m.green.1 = 1)
    (indep_green m inner.lonePath a)
  have hlenR : ¬ Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.c]) := fun h => by
    have := under_length h; simp [addrExt] at this
  have hlenG : ¬ Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.c]) := fun h => by
    have := under_length h; simp [addrExt] at this
  have hlenL : ¬ Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) (addrExt a [m.c]) := fun h => by
    have := under_length h; simp [addrExt] at this
  refine ⟨fun i => ?_, ?_, ?_, ?_, ?_⟩
  · rcases slot_cases m i with rfl | rfl | rfl
    · have hz : Under (addrExt a [m.red.1]) (addrExt a [m.red.1]) ∨
          Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1]) := Or.inl (under_refl _)
      simp only [chainVal, ne_of_under_cons m.red.1 [] (under_refl _), hz, ↓reduceIte]
      exact hR.1
    · have hz : Under (addrExt a [m.green.1]) (addrExt a [m.green.1]) ∨
          Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1]) :=
        Or.inl (under_refl _)
      have hr := (chain_regions (m := m) (L := inner.lonePath) (a := a)).2 hz
      simp only [chainVal, ne_of_under_cons m.green.1 [] (under_refl _), hz, hr, ↓reduceIte]
      exact hG.1
    · have hn : ¬ SUnder (addrExt a ([m.c] ++ inner.lonePath)) (addrExt a [m.c]) :=
        not_sunder_of_length (by simp [addrExt])
      obtain ⟨h1, h2, h3, h4⟩ := chain_inner_region (under_refl _) hn
      simp only [chainVal, h1, h2, h3, h4, ↓reduceIte]
      exact chainVal_root θ inner _ _ _ _ rfl
  · have hz : Under (addrExt a [m.c]) (addrExt a ([m.c] ++ inner.lonePath)) := by
      rw [← addrExt_append]; exact under_ext _ _
    have hn : ¬ SUnder (addrExt a ([m.c] ++ inner.lonePath)) (addrExt a ([m.c] ++ inner.lonePath)) := fun h => h.2 rfl
    obtain ⟨h1, h2, h3, h4⟩ := chain_inner_region hz hn
    simp only [chainVal, h1, h2, h3, h4, ↓reduceIte]
    rw [chainVal_lone θ inner _ _ _ _ _ (by rw [addrExt_append]; exact under_refl _)]
  · have hz : Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) :=
      under_refl _
    obtain ⟨hr, hg⟩ := (chain_regions (m := m) (L := inner.lonePath) (a := a)).1 hz
    have ha : addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]) ≠ a := ne_of_under_cons m.c _ (by simpa using hz)
    simp only [chainVal, ha, hr, hg, hz, ↓reduceIte]
    refine chainVal_root θ rest _ _ _ _ ?_
    rw [← hc]
    congr 1
    simp [RegChain.lonePath, addrExt_append]
  · have hz : Under (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) ∨
        Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) :=
      Or.inr (under_refl _)
    have ha : addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]) ≠ a := ne_of_under_cons m.c _ (by
      simpa using under_refl (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])))
    simp only [chainVal, ha, hz, ↓reduceIte]
    exact hR.2
  · have hz : Under (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) ∨
        Under (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) :=
      Or.inr (under_refl _)
    have hr := (chain_regions (m := m) (L := inner.lonePath) (a := a)).2 hz
    have ha : addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]) ≠ a := ne_of_under_cons m.c _ (by
      simpa using under_refl (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])))
    simp only [chainVal, ha, hz, hr, ↓reduceIte]
    exact hG.2

end WaveTurbulence.Links
