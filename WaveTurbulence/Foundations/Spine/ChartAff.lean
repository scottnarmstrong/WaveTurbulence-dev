/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ChainAlg
public import WaveTurbulence.Foundations.Spine.Engine1
/-! # The chart labels are affine in the rung points (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset

variable {n d : ℕ}

/-- The offsets `tvec` as an additive map of the rung point. -/
def tvecHom (j : Fin 4) : Pt d →+ (Fin d → ℤ) where
  toFun p := tvec p.1 p.2 j
  map_zero' := by fin_cases j <;> simp [tvec]
  map_add' p q := by fin_cases j <;> simp [tvec]; abel

/-- `tau` at rung `k` and slot `s` is additive in the rung point. -/
def tauHom (S : ChainSigns n) (k : Fin n) (s : Fin 4) : Pt d →+ (Fin d → ℤ) :=
  tvecHom ((S.σ k).symm s)

lemma tau_eq_tauHom (S : ChainSigns n) (P : Fin n → Pt d) (k : Fin n) (s : Fin 4) :
    S.tau P k s = tauHom S k s (P k) := rfl

/-- The `u`-rail label `railU a0 P j` as an affine label. -/
def railAff (S : ChainSigns n) (a0 : Fin d → ℤ) (j : Fin (n + 1)) : AffLab d n where
  c := a0
  lam := fun k => if k.1 < j.1 then tauHom S k 2 - tauHom S k 3 else 0

lemma railAff_eval (S : ChainSigns n) (a0 : Fin d → ℤ) (P : Fin n → Pt d) (j : Fin (n + 1)) :
    (railAff S a0 j).eval P = S.railU a0 P j := by
  unfold AffLab.eval ChainSigns.railU
  show a0 + ∑ k : Fin n, ((if k.1 < j.1 then tauHom S k 2 - tauHom S k 3 else 0 : Pt d →+ (Fin d → ℤ)) (P k)) = _
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : k.1 < j.1 <;> simp [hk, tau_eq_tauHom]

/-- The `v`-rail label. -/
def railBAff (S : ChainSigns n) (a0 b0 : Fin d → ℤ) (j : Fin (n + 1)) : AffLab d n where
  c := a0 - S.epsF j • (a0 - b0)
  lam := (railAff S a0 j).lam

lemma railBAff_eval (S : ChainSigns n) (a0 b0 : Fin d → ℤ) (P : Fin n → Pt d) (j : Fin (n + 1)) :
    (railBAff S a0 b0 j).eval P = S.railU a0 P j - S.epsF j • (a0 - b0) := by
  have h := railAff_eval S a0 P j
  have h2 : (railBAff S a0 b0 j).eval P = (a0 - S.epsF j • (a0 - b0)) + ∑ k, (railAff S a0 j).lam k (P k) := rfl
  have h3 : (railAff S a0 j).eval P = a0 + ∑ k, (railAff S a0 j).lam k (P k) := rfl
  rw [h2, ← h, h3]
  abel

/-- The rung-bond label as an affine label. -/
def rungAff (S : ChainSigns n) (a0 : Fin d → ℤ) (i : Fin n) (k : Fin 2) : AffLab d n where
  c := a0
  lam := fun k' => (if k'.1 < i.castSucc.1 then tauHom S k' 2 - tauHom S k' 3 else 0) +
    (if k' = i then tauHom S i 2 - tauHom S i (ChainSigns.rungSlot k) else 0)

lemma rungAff_eval (S : ChainSigns n) (a0 : Fin d → ℤ) (P : Fin n → Pt d) (i : Fin n) (k : Fin 2) :
    (rungAff S a0 i k).eval P = (S.inv a0 a0 P).r i k := by
  have h := railAff_eval S a0 P i.castSucc
  have h3 : (railAff S a0 i.castSucc).eval P = a0 + ∑ k, (railAff S a0 i.castSucc).lam k (P k) := rfl
  have e1 : (rungAff S a0 i k).eval P = a0 + ∑ k' : Fin n, (((if k'.1 < i.castSucc.1 then tauHom S k' 2 - tauHom S k' 3 else 0 : Pt d →+ (Fin d → ℤ)) +
      (if k' = i then tauHom S i 2 - tauHom S i (ChainSigns.rungSlot k) else 0 : Pt d →+ (Fin d → ℤ))) (P k')) := rfl
  simp only [ChainSigns.inv]
  rw [e1, ← h, h3]
  simp only [AddMonoidHom.add_apply, Finset.sum_add_distrib]
  have e2 : ∑ k' : Fin n, ((if k' = i then tauHom S i 2 - tauHom S i (ChainSigns.rungSlot k) else 0 : Pt d →+ (Fin d → ℤ)) (P k')) =
      S.tau P i 2 - S.tau P i (ChainSigns.rungSlot k) := by
    rw [Finset.sum_eq_single i]
    · simp [tau_eq_tauHom]
    · intro k' _ hk'; simp [hk']
    · simp
  have e3 : ∑ k' : Fin n, (railAff S a0 i.castSucc).lam k' (P k') =
      ∑ k' : Fin n, ((if k'.1 < i.castSucc.1 then tauHom S k' 2 - tauHom S k' 3 else 0 : Pt d →+ (Fin d → ℤ)) (P k')) := rfl
  rw [e2, e3]
  abel

end WaveTurbulence.LadderDecay
