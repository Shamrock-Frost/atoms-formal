import Atoms.TestCategory.SeparatingIntervalCriterion
import Mathlib.Tactic.Ring

open CategoryTheory Limits Opposite

namespace Atoms.TestCategory

universe u

def NonemptyFinSet : Type u := ULift.{u} ℕ

instance : SmallCategory NonemptyFinSet.{u} where
  Hom m n := ULift.{u} (Fin (m.down + 1) → Fin (n.down + 1))
  id _ := ⟨id⟩
  comp f g := ⟨g.down ∘ f.down⟩

namespace NonemptyFinSet

theorem hom_ext {m n : NonemptyFinSet.{u}} {f g : m ⟶ n} (h : f.down = g.down) : f = g :=
  ULift.ext _ _ h

def mk (n : ℕ) : NonemptyFinSet.{u} := ⟨n⟩

def isTerminalZero : IsTerminal (C := NonemptyFinSet.{u}) (mk 0) :=
  IsTerminal.ofUniqueHom (C := NonemptyFinSet.{u}) (fun _ ↦ ⟨fun _ ↦ 0⟩)
    (fun _ m ↦ hom_ext (funext fun _ ↦ Fin.fin_one_eq_zero (m.down _)))

instance hasTerminal : HasTerminal NonemptyFinSet.{u} := isTerminalZero.hasTerminal

private def prodEquiv (m k : ℕ) : Fin (m + 1) × Fin (k + 1) ≃ Fin (m * k + m + k + 1) :=
  finProdFinEquiv.trans (finCongr (by ring))

def prodFan (m k : NonemptyFinSet.{u}) : BinaryFan m k :=
  BinaryFan.mk (P := mk.{u} (m.down * k.down + m.down + k.down))
    ⟨fun i ↦ ((prodEquiv m.down k.down).symm i).1⟩
    ⟨fun i ↦ ((prodEquiv m.down k.down).symm i).2⟩

def prodFanIsLimit (m k : NonemptyFinSet.{u}) : IsLimit (prodFan m k) :=
  BinaryFan.IsLimit.mk _ (fun f g ↦ ⟨fun x ↦ prodEquiv m.down k.down (f.down x, g.down x)⟩)
    (fun f g ↦ hom_ext (funext fun x ↦ by
      change ((prodEquiv _ _).symm (prodEquiv _ _ _)).1 = _
      simp))
    (fun f g ↦ hom_ext (funext fun x ↦ by
      change ((prodEquiv _ _).symm (prodEquiv _ _ _)).2 = _
      simp))
    (fun f g h h₁ h₂ ↦ hom_ext (funext fun x ↦ by
      subst h₁ h₂
      exact ((prodEquiv _ _).apply_symm_apply _).symm))

instance hasBinaryProducts : HasBinaryProducts NonemptyFinSet.{u} :=
  have : ∀ {m k : NonemptyFinSet.{u}}, HasLimit (pair m k) :=
    fun {m k} ↦ ⟨⟨⟨prodFan m k, prodFanIsLimit m k⟩⟩⟩
  hasBinaryProducts_of_hasLimit_pair _

abbrev interval : NonemptyFinSet.{u}ᵒᵖ ⥤ Type u := yoneda.obj (mk 1)

def intervalPt (b : Bool) : (⊤_ (NonemptyFinSet.{u}ᵒᵖ ⥤ Type u)) ⟶ interval where
  app _ := ↾fun _ ↦ ⟨fun _ ↦ if b then 1 else 0⟩

theorem isEmpty_of_intervalPt (s : PullbackCone (intervalPt.{u} false) (intervalPt true))
    (c : NonemptyFinSet.{u}ᵒᵖ) : IsEmpty (s.pt.obj c) := by
  refine ⟨fun x ↦ ?_⟩
  have h := congrArg (fun f ↦ (f.app c x).down 0) s.condition
  simp only [intervalPt, yoneda_obj_obj, Bool.false_eq_true, ↓dreduceIte, Fin.isValue, ↓reduceIte,
    NatTrans.comp_app, comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Fin.zero_eq_one_iff,
    Nat.add_eq_right] at h
  exact Nat.one_ne_zero h

theorem isPullback_intervalPt :
    IsPullback (initial.to (⊤_ (NonemptyFinSet.{u}ᵒᵖ ⥤ Type u)))
      (initial.to (⊤_ (NonemptyFinSet.{u}ᵒᵖ ⥤ Type u))) (intervalPt false) (intervalPt true) :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk (initial.hom_ext _ _)
    (fun s ↦ show s.pt ⟶ ⊥_ (NonemptyFinSet.{u}ᵒᵖ ⥤ Type u) from
      { app := fun c ↦ ↾fun x ↦ (isEmpty_of_intervalPt s c).elim x
        naturality := fun c _ _ ↦ ConcreteCategory.hom_ext _ _ fun x ↦
          (isEmpty_of_intervalPt s c).elim x })
    (fun _ ↦ terminal.hom_ext _ _) (fun _ ↦ terminal.hom_ext _ _)
    (fun s _ _ _ ↦ NatTrans.ext (funext fun c ↦ ConcreteCategory.hom_ext _ _ fun x ↦
      (isEmpty_of_intervalPt s c).elim x)))

def separatingInterval : Homotopical.SeparatingInterval NonemptyFinSet.{u} where
  interval := interval
  pt := intervalPt
  isPullback := isPullback_intervalPt

theorem locallyAspherical_yoneda (𝒲 : BasicLocalizer.{u}) (b : NonemptyFinSet.{u}) :
    𝒲.LocallyAspherical NonemptyFinSet.{u} (yoneda.obj b) := fun a ↦
  (𝒲.pshAspherical_iff_of_iso _ (PreservesLimitPair.iso yoneda a b)).1
    (𝒲.pshAspherical_yoneda _ _)

end NonemptyFinSet

namespace BasicLocalizer

instance isTest_nonemptyFinSet (𝒲 : BasicLocalizer.{u}) : 𝒲.IsTest NonemptyFinSet.{u} :=
  𝒲.isTest_of_separatingInterval _ NonemptyFinSet.separatingInterval
    (NonemptyFinSet.locallyAspherical_yoneda 𝒲 _)
    (𝒲.terminal_aspherical (Cat.of NonemptyFinSet.{u}))

end BasicLocalizer

end Atoms.TestCategory
