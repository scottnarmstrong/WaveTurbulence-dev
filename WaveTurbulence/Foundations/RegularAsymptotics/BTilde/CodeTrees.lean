/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.CodeMap

/-!
# The tree integrals of a decoded code are the code-defined `B̃_Q`

For a B2 couple code `Q` with `+` root `x` and `-` root `y`, the product of the tree integrals
`treeInt` of the two decoded trees `Q.trees` (phases `β = ζα`) equals ClassJR's
`(toJR Q).Bt x y α t s` (DH21 (newexp1), (newexp2)), provided the phases satisfy the link relation
`ζ_{𝔫'}α_{𝔫'} = -ζ_𝔫α_𝔫` (DH21/DH23 (deftildeb)) on every link (`treesProp`). For a chain, the tree
integral of the decoded chain with a subtree `h` at the lone leaf is the CPS chain integral `chainT`
with continuation the tree integral of `h` (`plugProp`). The two are proved by mutual induction.
-/

@[expose] public section

namespace WaveTurbulence.MainCoef

open TTree MeasureTheory Complex
open scoped Real

/-! ### Translation facts -/

/-! ### The mini-tree tables -/

theorem mt_red1_ne_c (m : MiniTreeCode) : m.red.1 ≠ m.c := by
  rcases m with ⟨c, b⟩; fin_cases c <;> fin_cases b <;> decide
theorem mt_green1_ne_c (m : MiniTreeCode) : m.green.1 ≠ m.c := by
  rcases m with ⟨c, b⟩; fin_cases c <;> fin_cases b <;> decide
theorem mt_green1_ne_red1 (m : MiniTreeCode) : m.green.1 ≠ m.red.1 := by
  rcases m with ⟨c, b⟩; fin_cases c <;> fin_cases b <;> decide
theorem mt_red2_ne_lone (m : MiniTreeCode) : m.red.2 ≠ m.lone := by
  rcases m with ⟨c, b⟩; fin_cases c <;> fin_cases b <;> decide
theorem mt_green2_ne_lone (m : MiniTreeCode) : m.green.2 ≠ m.lone := by
  rcases m with ⟨c, b⟩; fin_cases c <;> fin_cases b <;> decide
theorem mt_green2_ne_red2 (m : MiniTreeCode) : m.green.2 ≠ m.red.2 := by
  rcases m with ⟨c, b⟩; fin_cases c <;> fin_cases b <;> decide

theorem mt_root_cases (m : MiniTreeCode) :
    (m.c = 0 ∧ m.red.1 = 1 ∧ m.green.1 = 2) ∨ (m.c = 1 ∧ m.red.1 = 0 ∧ m.green.1 = 2) ∨
      (m.c = 2 ∧ m.red.1 = 0 ∧ m.green.1 = 1) := by
  rcases m with ⟨c, b⟩; fin_cases c <;> fin_cases b <;> decide

theorem mt_nu_cases (m : MiniTreeCode) :
    (m.lone = 0 ∧ m.red.2 = 2 ∧ m.green.2 = 1) ∨ (m.lone = 2 ∧ m.red.2 = 0 ∧ m.green.2 = 1) ∨
      (m.lone = 1 ∧ m.red.2 = 0 ∧ m.green.2 = 2) ∨ (m.lone = 1 ∧ m.red.2 = 2 ∧ m.green.2 = 0) ∨
      (m.lone = 2 ∧ m.red.2 = 1 ∧ m.green.2 = 0) ∨ (m.lone = 0 ∧ m.red.2 = 1 ∧ m.green.2 = 2) := by
  rcases m with ⟨c, b⟩; fin_cases c <;> fin_cases b <;> decide

/-- The root slots of a mini-tree: `ν` at `c`, the red and the green leaves. -/
theorem mt_prod_root (m : MiniTreeCode) (G : Fin 3 → ℂ) :
    ∏ i, G i = G m.c * G m.red.1 * G m.green.1 := by
  rw [Fin.prod_univ_three]
  rcases mt_root_cases m with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h1, h2, h3] <;> ring

/-- The slots of `ν`: the lone leaf, the red and the green leaves. -/
theorem mt_prod_nu (m : MiniTreeCode) (G : Fin 3 → ℂ) :
    ∏ k, G k = G m.lone * G m.red.2 * G m.green.2 := by
  rw [Fin.prod_univ_three]
  rcases mt_nu_cases m with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ <;> rw [h1, h2, h3] <;> ring

/-! ### Node signs of children -/

theorem nodeSgn_ext_ne_one {x : ClassJR.Addr} {i : Fin 3} (hi : i ≠ 1) :
    ClassJR.nodeSgn (ClassJR.addrExt x [i]) = ClassJR.nodeSgn x := by
  rw [nodeSgn_addrExt]
  fin_cases i <;> simp_all

theorem nodeSgn_ext_one (x : ClassJR.Addr) :
    ClassJR.nodeSgn (ClassJR.addrExt x [1]) = -ClassJR.nodeSgn x := by
  rw [nodeSgn_addrExt]
  simp

/-! ### Tree integrals -/

variable (α : ClassJR.Addr → ℝ)

theorem treeInt_node_betaAt (l m r : TTree) (x : ClassJR.Addr) (u : ℝ) :
    treeInt (.node l m r) (betaAt α x) u = ∫ τ in (0 : ℝ)..u,
      cexp (π * I * (((ClassJR.nodeSgn x * α x : ℝ) : ℂ) * τ)) *
        (treeInt l (betaAt α (ClassJR.addrExt x [0])) τ * treeInt m (betaAt α (ClassJR.addrExt x [1])) τ *
          treeInt r (betaAt α (ClassJR.addrExt x [2])) τ) := by
  rw [treeInt, betaAt_cons α x 0, betaAt_cons α x 1, betaAt_cons α x 2, betaAt_nil]

omit α in
theorem intervalIntegral_mul_intervalIntegral (f g : ℝ → ℂ) (t s : ℝ) :
    (∫ t₁ in (0 : ℝ)..t, f t₁) * (∫ s₁ in (0 : ℝ)..s, g s₁) =
      ∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s, f t₁ * g s₁ := by
  rw [← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun t₁ _ => ?_
  rw [← intervalIntegral.integral_const_mul]

omit α in
/-- The time swaps of DH21 (newexp1): only the couple `Q₂` (whose `+` root hangs from the `-` tree)
has its times swapped. -/
theorem prod_swapT_type1 {V : Type} (A B C : (V → ℝ) → ℝ → ℝ → ℂ) (β : V → ℝ) (t s : ℝ) :
    ∏ j, ClassJR.swapT (![false, true, false] j) (![A, B, C] j) β t s = A β t s * B β s t * C β t s := by
  rw [Fin.prod_univ_three]
  rfl

omit α in
theorem chainT_mul_left {V : Type} {σ : ℕ → V} {ε : ℕ → ℤ} (c : ClassJR.LegalCode) (q : ℕ)
    (F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ) (β : V → ℝ) (t : ℝ) (a b : ℂ) (g k : ℝ → ℂ)
    (hk : ∀ t', a * b * g t' = k t') :
    ClassJR.chainT σ ε c q F β t g * a * b = ClassJR.chainT σ ε c q F β t k := by
  rw [mul_assoc, mul_comm, ← ClassJR.chainT_const_mul]
  congr 1
  funext t'
  exact hk t'

omit α in
theorem chainT_mul_chainT {V : Type} {σp σm : ℕ → V} {εp εm : ℕ → ℤ} (cp cm : ClassJR.LegalCode)
    (qp qm : ℕ) (Fp Fm : ℕ → (V → ℝ) → ℝ → ℝ → ℂ) (β : V → ℝ) (t s : ℝ) (A B : ℝ → ℂ)
    (C : ℝ → ℝ → ℂ) (hC : ∀ t' s', A t' * B s' = C t' s') :
    ClassJR.chainT σp εp cp qp Fp β t A * ClassJR.chainT σm εm cm qm Fm β s B =
      ClassJR.chainT σp εp cp qp Fp β t
        (fun t' => ClassJR.chainT σm εm cm qm Fm β s (fun s' => C t' s')) := by
  have e : ∀ t', ClassJR.chainT σm εm cm qm Fm β s (fun s' => C t' s') =
      A t' * ClassJR.chainT σm εm cm qm Fm β s B := by
    intro t'
    rw [← ClassJR.chainT_const_mul]
    congr 1
    funext s'
    exact (hC t' s').symm
  simp only [e]
  rw [mul_comm, ← ClassJR.chainT_const_mul]
  congr 1
  funext t'
  ring

/-! ### Lone leaves through a slot -/

omit α in
theorem subLone_map_self (o : Option TTree.Path) (i₀ : Fin 3) (g : TTree.Path → TTree.Path) :
    subLone (o.map fun p => i₀ :: g p) i₀ = o.map g := by
  cases o <;> simp [subLone]

omit α in
theorem subLone_map_ne (o : Option TTree.Path) {i i₀ : Fin 3} (hi : i ≠ i₀)
    (g : TTree.Path → TTree.Path) : subLone (o.map fun p => i₀ :: g p) i = none := by
  cases o <;> simp [subLone, Ne.symm hi]

omit α in
theorem loneOK_map_cons (o : Option TTree.Path) (i₀ : Fin 3) (g : TTree.Path → TTree.Path)
    (s u : ℝ) : LoneOK (o.map fun p => i₀ :: g p) s u := by
  cases o <;> simp [LoneOK]

theorem treeIntL_node3 (f : Fin 3 → TTree) (lp : Option TTree.Path) (hlp : ∀ s u, LoneOK lp s u)
    (x : ClassJR.Addr) (s u : ℝ) :
    treeIntL (node3 f) lp (betaAt α x) s u = ∫ τ in (0 : ℝ)..u,
      cexp (π * I * (((ClassJR.nodeSgn x * α x : ℝ) : ℂ) * τ)) *
        ∏ i, treeIntL (f i) (subLone lp i) (betaAt α (ClassJR.addrExt x [i])) s τ := by
  rw [node3, treeIntL, ite_eq_left (hlp s u), one_mul, betaAt_cons α x 0, betaAt_cons α x 1,
    betaAt_cons α x 2, betaAt_nil]
  simp only [Fin.prod_univ_three]

/-! ### The two statements -/

/-- **Couples**: the tree integrals of `Q.trees` rooted at `x` (`+`) and `y` (`-`) multiply to the
code-defined `B̃`, under the link relation. -/
def TreesProp (Q : RegCpl) : Prop :=
  ∀ x y : ClassJR.Addr, ClassJR.nodeSgn x = 1 → ClassJR.nodeSgn y = -1 →
    (∀ l ∈ (toJR Q).linksAt x y, LinkRel α l) → ∀ t s : ℝ,
      treeInt Q.trees.1 (betaAt α x) t * treeInt Q.trees.2 (betaAt α y) s = (toJR Q).Bt x y α t s

/-- **Chains**: the tree integral of the decoded chain rooted at `x` (sign `ζ`) with `h` at the lone
leaf is the chain integral, with continuation the tree integral of `h`. The lone leaf of the whole tree
may sit inside `h`, at the path `o` from `h`'s root (`o = none`: no lone leaf, the couple case). -/
def PlugProp (X : RegChain) : Prop :=
  ∀ (ζ : ℤˣ) (x : ClassJR.Addr) (q : ℕ) (h : TTree) (o : Option TTree.Path) (s : ℝ)
    (σ : ℕ → ClassJR.Addr) (ε : ℕ → ℤ) (F : ℕ → (ClassJR.Addr → ℝ) → ℝ → ℝ → ℂ),
    ClassJR.nodeSgn x = ((ζ : ℤˣ) : ℤ) →
    (∀ j ∈ Set.Ico q (q + (toJRc X).code.size), σ j = (toJRc X).sigmaAt x q j) →
    (∀ j, ε j = ClassJR.nodeSgn (σ j)) →
    (∀ j ∈ Set.Ico q (q + (toJRc X).code.size), F j = (toJRc X).coefAt ζ x q j) →
    (∀ l ∈ (toJRc X).linksAt ζ x, LinkRel α l) → ∀ u : ℝ,
      treeIntL (X.plug ζ h) (o.map (X.lonePath ++ ·)) (betaAt α x) s u =
        ClassJR.chainT σ ε (toJRc X).code q F α u
          (fun t' => treeIntL h o (betaAt α (ClassJR.addrExt x X.lonePath)) s t')

/-! ### Pair facts -/

section PairFacts

variable (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (ζ : ℤˣ) (x : ClassJR.Addr)
  (q : ℕ)

omit α

theorem code_toJRc_pair :
    (toJRc (.pair m Qr Qg inner rest)).code = .node (toJRc inner).code (toJRc rest).code := rfl

theorem size_toJRc_pair : (toJRc (.pair m Qr Qg inner rest)).code.size =
    (toJRc inner).code.size + (toJRc rest).code.size + 1 := rfl

theorem sigmaAt_toJRc_self : (toJRc (.pair m Qr Qg inner rest)).sigmaAt x q q = x :=
  ClassJR.sigmaAt_pair_self _ _ _ _ _ _ _

theorem sigmaAt_toJRc_inner {j : ℕ} (hj : j ∈ Set.Ico (q + 1) (q + 1 + (toJRc inner).code.size)) :
    (toJRc (.pair m Qr Qg inner rest)).sigmaAt x q j =
      (toJRc inner).sigmaAt (ClassJR.addrExt x [m.c]) (q + 1) j :=
  ClassJR.sigmaAt_pair_inner _ _ _ _ _ _ _ hj

theorem sigmaAt_toJRc_rest {j : ℕ}
    (hj : j ∈ Set.Ico (q + (toJRc inner).code.size + 1)
      (q + (toJRc inner).code.size + 1 + (toJRc rest).code.size)) :
    (toJRc (.pair m Qr Qg inner rest)).sigmaAt x q j =
      (toJRc rest).sigmaAt (ClassJR.addrExt x ([m.c] ++ inner.lonePath ++ [m.lone]))
        (q + (toJRc inner).code.size + 1) j := by
  rw [← lonePath_toJRc inner]
  exact ClassJR.sigmaAt_pair_rest _ _ _ _ _ _ _ hj

theorem coefAt_toJRc_self : (toJRc (.pair m Qr Qg inner rest)).coefAt ζ x q q =
    fun α ta tb =>
      (if slotSign ζ m.red.1 = 1 then
          (toJR Qr).Bt (ClassJR.addrExt x [m.red.1])
            (ClassJR.addrExt x ([m.c] ++ inner.lonePath ++ [m.red.2])) α ta tb
        else (toJR Qr).Bt (ClassJR.addrExt x ([m.c] ++ inner.lonePath ++ [m.red.2]))
          (ClassJR.addrExt x [m.red.1]) α tb ta) *
      (if slotSign ζ m.green.1 = 1 then
          (toJR Qg).Bt (ClassJR.addrExt x [m.green.1])
            (ClassJR.addrExt x ([m.c] ++ inner.lonePath ++ [m.green.2])) α ta tb
        else (toJR Qg).Bt (ClassJR.addrExt x ([m.c] ++ inner.lonePath ++ [m.green.2]))
          (ClassJR.addrExt x [m.green.1]) α tb ta) := by
  rw [← lonePath_toJRc inner]
  simp only [toJRc, ClassJR.RegChain.coefAt, ↓reduceIte]
  rfl

theorem coefAt_toJRc_inner {j : ℕ} (hj : j ∈ Set.Ico (q + 1) (q + 1 + (toJRc inner).code.size)) :
    (toJRc (.pair m Qr Qg inner rest)).coefAt ζ x q j =
      (toJRc inner).coefAt (slotSign ζ m.c) (ClassJR.addrExt x [m.c]) (q + 1) j :=
  ClassJR.coefAt_pair_inner _ _ _ _ _ _ _ _ hj

theorem coefAt_toJRc_rest {j : ℕ}
    (hj : j ∈ Set.Ico (q + (toJRc inner).code.size + 1)
      (q + (toJRc inner).code.size + 1 + (toJRc rest).code.size)) :
    (toJRc (.pair m Qr Qg inner rest)).coefAt ζ x q j =
      (toJRc rest).coefAt (slotSign (slotSign ζ m.c) m.lone)
        (ClassJR.addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])) (q + (toJRc inner).code.size + 1) j := by
  rw [← lonePath_toJRc inner]
  exact ClassJR.coefAt_pair_rest _ _ _ _ _ _ _ _ hj

theorem linksAt_toJRc_pair : (toJRc (.pair m Qr Qg inner rest)).linksAt ζ x =
    (x, ClassJR.addrExt x ([m.c] ++ inner.lonePath)) ::
    ((if slotSign ζ m.red.1 = 1 then
        (toJR Qr).linksAt (ClassJR.addrExt x [m.red.1])
          (ClassJR.addrExt x ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else (toJR Qr).linksAt (ClassJR.addrExt x ([m.c] ++ inner.lonePath ++ [m.red.2]))
        (ClassJR.addrExt x [m.red.1])) ++
    (if slotSign ζ m.green.1 = 1 then
        (toJR Qg).linksAt (ClassJR.addrExt x [m.green.1])
          (ClassJR.addrExt x ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else (toJR Qg).linksAt (ClassJR.addrExt x ([m.c] ++ inner.lonePath ++ [m.green.2]))
        (ClassJR.addrExt x [m.green.1])) ++
    (toJRc inner).linksAt (slotSign ζ m.c) (ClassJR.addrExt x [m.c]) ++
    (toJRc rest).linksAt (slotSign (slotSign ζ m.c) m.lone)
      (ClassJR.addrExt x ([m.c] ++ inner.lonePath ++ [m.lone]))) := by
  rw [← lonePath_toJRc inner]
  rfl

end PairFacts

/-! ### The induction steps -/

/-- A red or green pair factor of a chain pair is the product of the two tree integrals. -/
theorem pair_factor {Q : RegCpl} (hQ : TreesProp α Q) {a b : ClassJR.Addr} {ζa ζb : ℤˣ}
    (ha : ClassJR.nodeSgn a = ((ζa : ℤˣ) : ℤ)) (hb : ClassJR.nodeSgn b = ((ζb : ℤˣ) : ℤ))
    (hab : ζb = -ζa)
    (hl : ∀ l ∈ (if ζa = 1 then (toJR Q).linksAt a b else (toJR Q).linksAt b a), LinkRel α l)
    (ta tb : ℝ) :
    (if ζa = 1 then (toJR Q).Bt a b α ta tb else (toJR Q).Bt b a α tb ta) =
      treeInt (treeOfSign Q.trees ζa) (betaAt α a) ta *
        treeInt (treeOfSign Q.trees ζb) (betaAt α b) tb := by
  subst hab
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or ζa with rfl | rfl
  · simp only [ite_true, treeOfSign, hne, ite_false] at hl ⊢
    exact (hQ a b (by simpa using ha) (by simpa using hb) hl ta tb).symm
  · simp only [hne, ite_false, treeOfSign, neg_neg, ite_true] at hl ⊢
    rw [mul_comm]
    exact (hQ b a (by simpa using hb) (by simpa using ha) hl tb ta).symm

theorem TreesProp.triv : TreesProp α .triv := by
  intro x y _ _ _ t s
  simp [toJR, RegCpl.trees, treeInt, ClassJR.RegCpl.Bt]

theorem TreesProp.type1 {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} (h₁ : TreesProp α Q₁)
    (h₂ : TreesProp α Q₂) (h₃ : TreesProp α Q₃) : TreesProp α (.type1 c Q₁ Q₂ Q₃) := by
  intro x y hx hy hl t s
  simp only [toJR, ClassJR.RegCpl.linksAt, List.forall_mem_cons, List.forall_mem_append] at hl
  obtain ⟨hxy, ⟨hl₁, hl₂⟩, hl₃⟩ := hl
  have hxy' : (ClassJR.nodeSgn y : ℝ) * α y = -((ClassJR.nodeSgn x : ℝ) * α x) := hxy
  have hp0 : ClassJR.MiniCplCode.partner c 0 ≠ 1 := by fin_cases c <;> decide
  have hp2 : ClassJR.MiniCplCode.partner c 2 ≠ 1 := by fin_cases c <;> decide
  have I₁ := h₁ (ClassJR.addrExt x [0]) (ClassJR.addrExt y [ClassJR.MiniCplCode.partner c 0])
    ((nodeSgn_ext_ne_one (by decide)).trans hx) ((nodeSgn_ext_ne_one hp0).trans hy) hl₁
  have I₂ := h₂ (ClassJR.addrExt y [1]) (ClassJR.addrExt x [1])
    (by rw [nodeSgn_ext_one, hy]; norm_num) (by rw [nodeSgn_ext_one, hx]) hl₂
  have I₃ := h₃ (ClassJR.addrExt x [2]) (ClassJR.addrExt y [ClassJR.MiniCplCode.partner c 2])
    ((nodeSgn_ext_ne_one (by decide)).trans hx) ((nodeSgn_ext_ne_one hp2).trans hy) hl₃
  have hexp : ∀ t₁ s₁ : ℝ, cexp (π * I * (((ClassJR.nodeSgn x * α x : ℝ) : ℂ) * t₁)) *
      cexp (π * I * (((ClassJR.nodeSgn y * α y : ℝ) : ℂ) * s₁)) =
      cexp (π * I * ((α x : ℂ) * ((t₁ : ℂ) - s₁))) := by
    intro t₁ s₁
    rw [← Complex.exp_add, hxy', hx]
    congr 1
    push_cast
    ring
  simp only [toJR, ClassJR.RegCpl.Bt, ClassJR.type1F, prod_swapT_type1, RegCpl.trees]
  obtain rfl | rfl : c = 0 ∨ c = 1 := by fin_cases c <;> simp
  · simp only [show ClassJR.MiniCplCode.partner 0 0 = 0 from rfl,
      show ClassJR.MiniCplCode.partner 0 2 = 2 from rfl, ↓reduceIte] at I₁ I₃ ⊢
    rw [treeInt_node_betaAt, treeInt_node_betaAt, intervalIntegral_mul_intervalIntegral]
    refine intervalIntegral.integral_congr fun t₁ _ =>
      intervalIntegral.integral_congr fun s₁ _ => ?_
    rw [← I₁ t₁ s₁, ← I₂ s₁ t₁, ← I₃ t₁ s₁, ← hexp]
    ring
  · simp only [show ClassJR.MiniCplCode.partner 1 0 = 2 from rfl,
      show ClassJR.MiniCplCode.partner 1 2 = 0 from rfl, show ((1 : Fin 2) = 0) ↔ False by decide,
      ite_false] at I₁ I₃ ⊢
    rw [treeInt_node_betaAt, treeInt_node_betaAt, intervalIntegral_mul_intervalIntegral]
    refine intervalIntegral.integral_congr fun t₁ _ =>
      intervalIntegral.integral_congr fun s₁ _ => ?_
    rw [← I₁ t₁ s₁, ← I₂ s₁ t₁, ← I₃ t₁ s₁, ← hexp]
    ring

theorem TreesProp.type2 {Xp Xm : RegChain} {Qlp : RegCpl} (hp : PlugProp α Xp)
    (hm : PlugProp α Xm) (hl : TreesProp α Qlp) : TreesProp α (.type2 Xp Xm Qlp) := by
  intro x y hx hy hlk t s
  simp only [toJR, ClassJR.RegCpl.linksAt, List.forall_mem_append, lonePath_toJRc] at hlk
  obtain ⟨⟨hlp, hlm⟩, hll⟩ := hlk
  have hx1 : ClassJR.nodeSgn x = ((1 : ℤˣ) : ℤ) := by rw [hx, Units.val_one]
  have hy1 : ClassJR.nodeSgn y = ((-1 : ℤˣ) : ℤ) := by rw [hy, Units.val_neg, Units.val_one]
  have Ilp := hl _ _ (by simpa using nodeSgn_lonePath Xp hx1) (by simpa using nodeSgn_lonePath Xm hy1)
    hll
  simp only [RegCpl.trees, toJR, ClassJR.RegCpl.Bt, ClassJR.type2F, lonePath_toJRc]
  have Ep := hp 1 x 0 Qlp.trees.1 none 0 ((toJRc Xp).sigmaAt x 0)
    (fun j => ClassJR.nodeSgn ((toJRc Xp).sigmaAt x 0 j)) ((toJRc Xp).coefAt 1 x 0) hx1
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) hlp t
  have Em := hm (-1) y 0 Qlp.trees.2 none 0 ((toJRc Xm).sigmaAt y 0)
    (fun j => ClassJR.nodeSgn ((toJRc Xm).sigmaAt y 0 j)) ((toJRc Xm).coefAt (-1) y 0) hy1
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) hlm s
  simp only [Option.map_none, treeIntL_none] at Ep Em
  rw [Ep, Em]
  exact chainT_mul_chainT _ _ _ _ _ _ _ _ _ _ _ _ fun t' s' => Ilp t' s'

theorem PlugProp.nil : PlugProp α .nil := by
  intro ζ x q h o s σ ε F _ _ _ _ _ u
  cases o <;> simp only [RegChain.plug, toJRc, ClassJR.RegChain.code, ClassJR.chainT_nil,
    RegChain.lonePath, ClassJR.addrExt, List.append_nil, List.nil_append, Prod.mk.eta,
    Option.map_none, Option.map_some]

theorem PlugProp.pair {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain}
    (hr : TreesProp α Qr) (hg : TreesProp α Qg) (hi : PlugProp α inner)
    (hrest : PlugProp α rest) : PlugProp α (.pair m Qr Qg inner rest) := by
  intro ζ x q h o s σ ε F hx hσ hε hF hlk u
  rw [linksAt_toJRc_pair] at hlk
  simp only [List.forall_mem_cons, List.forall_mem_append] at hlk
  obtain ⟨hab, ⟨⟨hlr, hlg⟩, hli⟩, hlrest⟩ := hlk
  have hab' : (ClassJR.nodeSgn (ClassJR.addrExt x ([m.c] ++ inner.lonePath)) : ℝ) *
      α (ClassJR.addrExt x ([m.c] ++ inner.lonePath)) = -((ClassJR.nodeSgn x : ℝ) * α x) := hab
  rw [size_toJRc_pair] at hσ hF
  have hqm : q ∈ Set.Ico q (q + ((toJRc inner).code.size + (toJRc rest).code.size + 1)) := by
    simp only [Set.mem_Ico]; omega
  have hσq : σ q = x := (hσ q hqm).trans (sigmaAt_toJRc_self ..)
  -- the inner chain
  have hxc : ClassJR.nodeSgn (ClassJR.addrExt x [m.c]) = ((slotSign ζ m.c : ℤˣ) : ℤ) :=
    nodeSgn_slot hx m.c
  have IHi : ∀ (H : TTree) (u : ℝ), treeIntL (inner.plug (slotSign ζ m.c) H)
      (o.map fun p => inner.lonePath ++ (m.lone :: (rest.lonePath ++ p)))
      (betaAt α (ClassJR.addrExt x [m.c])) s u = ClassJR.chainT σ ε (toJRc inner).code (q + 1) F α u
        (fun t' => treeIntL H (o.map fun p => m.lone :: (rest.lonePath ++ p))
          (betaAt α (ClassJR.addrExt (ClassJR.addrExt x [m.c]) inner.lonePath)) s t') := by
    intro H u
    have := hi (slotSign ζ m.c) (ClassJR.addrExt x [m.c]) (q + 1) H
      (o.map fun p => m.lone :: (rest.lonePath ++ p)) s σ ε F hxc
      (fun j hj => (hσ j (by simp only [Set.mem_Ico] at hj ⊢; omega)).trans
        (sigmaAt_toJRc_inner m Qr Qg inner rest x q hj))
      hε
      (fun j hj => (hF j (by simp only [Set.mem_Ico] at hj ⊢; omega)).trans
        (coefAt_toJRc_inner m Qr Qg inner rest ζ x q hj))
      hli u
    simpa only [Option.map_map, Function.comp_def] using this
  -- the rest of the chain
  have hxl : ClassJR.nodeSgn (ClassJR.addrExt (ClassJR.addrExt x [m.c]) inner.lonePath) =
      ((slotSign ζ m.c : ℤˣ) : ℤ) := nodeSgn_lonePath inner hxc
  have hxr : ClassJR.nodeSgn (ClassJR.addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])) =
      ((slotSign (slotSign ζ m.c) m.lone : ℤˣ) : ℤ) := by
    have := nodeSgn_slot hxl m.lone
    rwa [ClassJR.addrExt_addrExt, ClassJR.addrExt_addrExt] at this
  have IHr := hrest (slotSign (slotSign ζ m.c) m.lone)
    (ClassJR.addrExt x ([m.c] ++ inner.lonePath ++ [m.lone])) (q + (toJRc inner).code.size + 1) h o s
    σ ε F hxr
    (fun j hj => (hσ j (by simp only [Set.mem_Ico] at hj ⊢; omega)).trans
      (sigmaAt_toJRc_rest m Qr Qg inner rest x q hj))
    hε
    (fun j hj => (hF j (by simp only [Set.mem_Ico] at hj ⊢; omega)).trans
      (coefAt_toJRc_rest m Qr Qg inner rest ζ x q hj))
    hlrest
  -- the red and green couples
  have hred2 : ClassJR.nodeSgn (ClassJR.addrExt x ([m.c] ++ inner.lonePath ++ [m.red.2])) =
      ((slotSign (slotSign ζ m.c) m.red.2 : ℤˣ) : ℤ) := by
    have := nodeSgn_slot hxl m.red.2
    rwa [ClassJR.addrExt_addrExt, ClassJR.addrExt_addrExt] at this
  have hgreen2 : ClassJR.nodeSgn (ClassJR.addrExt x ([m.c] ++ inner.lonePath ++ [m.green.2])) =
      ((slotSign (slotSign ζ m.c) m.green.2 : ℤˣ) : ℤ) := by
    have := nodeSgn_slot hxl m.green.2
    rwa [ClassJR.addrExt_addrExt, ClassJR.addrExt_addrExt] at this
  have PFr := pair_factor α hr (nodeSgn_slot hx m.red.1) hred2 (MiniTreeCode.red_sign m ζ) hlr
  have PFg := pair_factor α hg (nodeSgn_slot hx m.green.1) hgreen2 (MiniTreeCode.green_sign m ζ) hlg
  -- the computation
  have elp : (fun p => (RegChain.pair m Qr Qg inner rest).lonePath ++ p) =
      fun p => m.c :: (inner.lonePath ++ (m.lone :: (rest.lonePath ++ p))) := by
    funext p
    simp [RegChain.lonePath]
  rw [elp, RegChain.plug, treeIntL_node3 α _ _ (loneOK_map_cons o m.c _), code_toJRc_pair,
    ClassJR.chainT_node]
  refine intervalIntegral.integral_congr fun ta _ => ?_
  rw [hε q, hσq, mt_prod_root m]
  simp only [↓reduceIte, mt_red1_ne_c, mt_green1_ne_c, mt_green1_ne_red1, subLone_map_self,
    subLone_map_ne o (mt_red1_ne_c m), subLone_map_ne o (mt_green1_ne_c m), treeIntL_none]
  have e1 : cexp (π * I * (((ClassJR.nodeSgn x * α x : ℝ) : ℂ) * ta)) =
      cexp (π * I * ((ClassJR.nodeSgn x : ℂ) * (α x : ℂ) * ta)) := by
    push_cast; ring_nf
  rw [e1, IHi]
  congr 1
  refine chainT_mul_left _ _ _ _ _ _ _ _ _ fun t' => ?_
  rw [treeIntL_node3 α _ _ (loneOK_map_cons o m.lone _), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun tb _ => ?_
  rw [mt_prod_nu m]
  simp only [↓reduceIte, mt_red2_ne_lone, mt_green2_ne_lone, mt_green2_ne_red2,
    ClassJR.addrExt_addrExt, RegChain.lonePath, subLone_map_self,
    subLone_map_ne o (mt_red2_ne_lone m), subLone_map_ne o (mt_green2_ne_lone m), treeIntL_none]
  rw [IHr, hF q hqm, coefAt_toJRc_self, hab']
  simp only [ClassJR.addrExt_addrExt]
  rw [PFr ta tb, PFg ta tb]
  have e2 : cexp (π * I * (((-((ClassJR.nodeSgn x : ℝ) * α x) : ℝ) : ℂ) * tb)) =
      cexp (π * I * (-((ClassJR.nodeSgn x : ℂ) * (α x : ℂ)) * tb)) := by
    push_cast; ring_nf
  rw [e2]
  ring

/-! ### The mutual induction -/

mutual
/-- **Decoded couples**: tree integrals = code-defined `B̃`. -/
theorem treesProp : ∀ Q : RegCpl, TreesProp α Q
  | .triv => TreesProp.triv α
  | .type1 _ Q₁ Q₂ Q₃ => TreesProp.type1 α (treesProp Q₁) (treesProp Q₂) (treesProp Q₃)
  | .type2 Xp Xm Qlp => TreesProp.type2 α (plugProp Xp) (plugProp Xm) (treesProp Qlp)

/-- **Decoded chains**: tree integral = chain integral. -/
theorem plugProp : ∀ X : RegChain, PlugProp α X
  | .nil => PlugProp.nil α
  | .pair _ Qr Qg inner rest =>
    PlugProp.pair α (treesProp Qr) (treesProp Qg) (plugProp inner) (plugProp rest)
end

end WaveTurbulence.MainCoef
