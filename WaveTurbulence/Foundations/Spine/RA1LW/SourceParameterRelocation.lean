/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceParameterCongruence

/-! # Relocating source leaf products with their original address parameters -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Reg TTree

variable {V : Type*} {w w' : ℕ}

/-- Agreement of the parameter environments above corresponding roots
persists above any corresponding child roots. -/
private theorem environment_ext {β : Type*}
    (θ : Fin w × Path → β) (θ' : Fin w' × Path → β)
    (a : Fin w × Path) (a' : Fin w' × Path)
    (h : ∀ p, θ (addrExt a p) = θ' (addrExt a' p)) (p : Path) :
    ∀ q, θ (addrExt (addrExt a p) q) = θ' (addrExt (addrExt a' p) q) := by
  intro q
  simp only [addrExt_append]
  exact h (p++q)

variable [AddCommGroup V]

mutual
/-- The original couple leaf kernel is unchanged by relocating its two
independent roots together with the complete parameter environments. -/
theorem cplLeafProduct_relocate (F : Fin w × Path → V → ℂ) (F' : Fin w' × Path → V → ℂ)
    (θ : Fin w × Path → V × V) (θ' : Fin w' × Path → V × V) :
    (Q : RegCpl) → (a b : Fin w × Path) → (a' b' : Fin w' × Path) → (r : V) →
    Indep a b → Indep a' b' →
    (∀ p, (θ (addrExt a p), F (addrExt a p)) = (θ' (addrExt a' p), F' (addrExt a' p))) →
    (∀ p, (θ (addrExt b p), F (addrExt b p)) = (θ' (addrExt b' p), F' (addrExt b' p))) →
    cplLeafProduct F θ Q a b r = cplLeafProduct F' θ' Q a' b' r
  | .triv, a,b,a',b',r,_,_,ha,_ => by
    have h := ha []
    simp only [addrExt_nil] at h
    rw [cplLeafProduct_triv,cplLeafProduct_triv,(Prod.mk.inj h).2]
  | .type1 c Q₁ Q₂ Q₃, a,b,a',b',r,hab,hab',ha,hb => by
    have hroot : θ a = θ' a' := by
      have h := ha []
      simp only [addrExt_nil] at h
      exact (Prod.mk.inj h).1
    rw [cplLeafProduct_type1 F θ c Q₁ Q₂ Q₃ a b r hab,
      cplLeafProduct_type1 F' θ' c Q₁ Q₂ Q₃ a' b' r hab',hroot]
    rw [cplLeafProduct_relocate F F' θ θ' Q₁ _ _ _ _ _ (hab.ext _ _) (hab'.ext _ _)
      (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) a a' ha _) (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) b b' hb _),
      cplLeafProduct_relocate F F' θ θ' Q₂ _ _ _ _ _ (hab.symm.ext _ _) (hab'.symm.ext _ _)
      (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) b b' hb _) (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) a a' ha _),
      cplLeafProduct_relocate F F' θ θ' Q₃ _ _ _ _ _ (hab.ext _ _) (hab'.ext _ _)
      (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) a a' ha _) (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) b b' hb _)]
  | .type2 Xp Xm Qlp, a,b,a',b',r,hab,hab',ha,hb => by
    rw [cplLeafProduct_type2 F θ Xp Xm Qlp a b r hab,
      cplLeafProduct_type2 F' θ' Xp Xm Qlp a' b' r hab',
      chainLeafProduct_relocate F F' θ θ' Xp 1 a a' r _ _ ha,
      chainLeafProduct_relocate F F' θ θ' Xm (-1) b b' r _ _ hb,
      cplLeafProduct_relocate F F' θ θ' Qlp _ _ _ _ r (hab.ext _ _) (hab'.ext _ _)
        (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) a a' ha _) (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) b b' hb _)]
termination_by structural Q => Q

/-- The paired chain kernel relocates with its single root environment;
the excluded continuation remains arbitrary on both sides. -/
theorem chainLeafProduct_relocate (F : Fin w × Path → V → ℂ) (F' : Fin w' × Path → V → ℂ)
    (θ : Fin w × Path → V × V) (θ' : Fin w' × Path → V × V) :
    (X : RegChain) → (ζ : ℤˣ) → (a : Fin w × Path) → (a' : Fin w' × Path) → (r : V) →
    (cont : Fin w × Path → V) → (cont' : Fin w' × Path → V) →
    (∀ p, (θ (addrExt a p), F (addrExt a p)) = (θ' (addrExt a' p), F' (addrExt a' p))) →
    chainLeafProduct F θ X ζ a r cont = chainLeafProduct F' θ' X ζ a' r cont'
  | .nil, _,_,_,_,_,_,_ => rfl
  | .pair m Qr Qg inner rest, ζ,a,a',r,cont,cont',ha => by
    have hroot : θ a = θ' a' := by
      have h := ha []
      simp only [addrExt_nil] at h
      exact (Prod.mk.inj h).1
    rw [chainLeafProduct_pair,chainLeafProduct_pair,hroot]
    have hr : (if slotSign ζ m.red.1 = 1 then
        cplLeafProduct F θ Qr (addrExt a [m.red.1])
          (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (childVals r (θ' a') m.red.1)
      else cplLeafProduct F θ Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1]) (childVals r (θ' a') m.red.1)) =
      (if slotSign ζ m.red.1 = 1 then
        cplLeafProduct F' θ' Qr (addrExt a' [m.red.1])
          (addrExt a' ([m.c] ++ inner.lonePath ++ [m.red.2])) (childVals r (θ' a') m.red.1)
      else cplLeafProduct F' θ' Qr (addrExt a' ([m.c] ++ inner.lonePath ++ [m.red.2]))
        (addrExt a' [m.red.1]) (childVals r (θ' a') m.red.1)) := by
      split_ifs
      · exact cplLeafProduct_relocate F F' θ θ' Qr _ _ _ _ _
          (indep_red m _ a) (indep_red m _ a')
          (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) a a' ha _) (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) a a' ha _)
      · exact cplLeafProduct_relocate F F' θ θ' Qr _ _ _ _ _
          (indep_red m _ a).symm (indep_red m _ a').symm
          (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) a a' ha _) (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) a a' ha _)
    have hg : (if slotSign ζ m.green.1 = 1 then
        cplLeafProduct F θ Qg (addrExt a [m.green.1])
          (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (childVals r (θ' a') m.green.1)
      else cplLeafProduct F θ Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1]) (childVals r (θ' a') m.green.1)) =
      (if slotSign ζ m.green.1 = 1 then
        cplLeafProduct F' θ' Qg (addrExt a' [m.green.1])
          (addrExt a' ([m.c] ++ inner.lonePath ++ [m.green.2])) (childVals r (θ' a') m.green.1)
      else cplLeafProduct F' θ' Qg (addrExt a' ([m.c] ++ inner.lonePath ++ [m.green.2]))
        (addrExt a' [m.green.1]) (childVals r (θ' a') m.green.1)) := by
      split_ifs
      · exact cplLeafProduct_relocate F F' θ θ' Qg _ _ _ _ _
          (indep_green m _ a) (indep_green m _ a')
          (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) a a' ha _) (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) a a' ha _)
      · exact cplLeafProduct_relocate F F' θ θ' Qg _ _ _ _ _
          (indep_green m _ a).symm (indep_green m _ a').symm
          (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) a a' ha _) (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) a a' ha _)
    rw [hr,hg,
      chainLeafProduct_relocate F F' θ θ' inner _ _ _ _ _ _ (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) a a' ha _),
      chainLeafProduct_relocate F F' θ θ' rest _ _ _ _ _ _ (environment_ext (fun z => (θ z, F z)) (fun z => (θ' z, F' z)) a a' ha _)]
termination_by structural X => X
end

end WaveTurbulence.RA1Leafwise
