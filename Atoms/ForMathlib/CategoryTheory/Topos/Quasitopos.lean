import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.EffectiveUnions
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Topos.Sheaf

universe w v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace Subobject

structure StrongClassifier (C : Type u) [Category.{v} C] where
  Ω₀ : C
  Ω : C
  truth : Ω₀ ⟶ Ω
  mono_truth : Mono truth := by infer_instance
  χ₀ (U : C) : U ⟶ Ω₀
  χ {U X : C} (m : U ⟶ X) [StrongMono m] : X ⟶ Ω
  isPullback {U X : C} (m : U ⟶ X) [StrongMono m] : IsPullback m (χ₀ U) (χ m) truth
  uniq {U X : C} (m : U ⟶ X) [StrongMono m] {χ₀' : U ⟶ Ω₀} {χ' : X ⟶ Ω}
    (hχ' : IsPullback m χ₀' χ' truth) : χ' = χ m

def StrongClassifier.ofClassifier (c : Classifier C) : StrongClassifier C where
  Ω₀ := c.Ω₀
  Ω := c.Ω
  truth := c.truth
  χ₀ := c.χ₀
  χ m _ := c.χ m
  isPullback m _ := c.isPullback m
  uniq m _ _ _ h := c.uniq m h

end Subobject

class Quasitopos (C : Type u) [Category.{v} C] : Prop where
  [hasFiniteLimits : HasFiniteLimits C]
  [hasFiniteColimits : HasFiniteColimits C]
  isLeftAdjoint_pullback {X Y : C} (f : X ⟶ Y) : (Over.pullback f).IsLeftAdjoint
  nonempty_strongClassifier : Nonempty (Subobject.StrongClassifier C)

attribute [instance] Quasitopos.hasFiniteLimits Quasitopos.hasFiniteColimits
  Quasitopos.isLeftAdjoint_pullback

namespace Quasitopos

variable [Quasitopos C]

instance hasEffectiveUnions : HasEffectiveUnions C :=
  hasEffectiveUnions_of_isUniversalColimit fun H =>
    isUniversalColimit_of_preservesColimitsOfShape_pullback (fun _ => inferInstance) H.isColimit

instance finitaryPreExtensive : FinitaryPreExtensive C where
  universal' _ hc :=
    isUniversalColimit_of_preservesColimitsOfShape_pullback (fun _ => inferInstance) hc

private noncomputable def pullbackTerminalIso (A Y : C) :
    pullback (terminal.from Y) (terminal.from A) ≅ A ⨯ Y where
  hom := prod.lift (pullback.snd _ _) (pullback.fst _ _)
  inv := pullback.lift prod.snd prod.fst (terminal.hom_ext _ _)
  hom_inv_id := pullback.hom_ext
    (by rw [Category.assoc, pullback.lift_fst, prod.lift_snd, Category.id_comp])
    (by rw [Category.assoc, pullback.lift_snd, prod.lift_fst, Category.id_comp])
  inv_hom_id := prod.hom_ext
    (by rw [Category.assoc, prod.lift_fst, pullback.lift_snd, Category.id_comp])
    (by rw [Category.assoc, prod.lift_snd, pullback.lift_fst, Category.id_comp])

instance isLeftAdjoint_prod_functor_obj (A : C) : (prod.functor.obj A).IsLeftAdjoint := by
  let F : C ⥤ C :=
    (Over.equivalenceOfIsTerminal terminalIsTerminal).inverse ⋙
      Over.pullback (terminal.from A) ⋙ Over.forget A
  refine Functor.isLeftAdjoint_of_iso (F := F)
    (NatIso.ofComponents (fun Y => pullbackTerminalIso A Y) fun {X Y} f => ?_)
  change pullback.lift (pullback.fst (terminal.from X) (terminal.from A) ≫ f)
      (pullback.snd _ _) (terminal.hom_ext _ _) ≫ (pullbackTerminalIso A Y).hom =
    (pullbackTerminalIso A X).hom ≫ prod.map (𝟙 A) f
  apply prod.hom_ext
  · simp only [pullbackTerminalIso, Category.assoc, prod.lift_map, Category.comp_id]
    rw [prod.lift_fst, prod.lift_fst, pullback.lift_snd]
  · simp only [pullbackTerminalIso, Category.assoc, prod.lift_map]
    rw [prod.lift_snd, prod.lift_snd, pullback.lift_fst]

open MonoidalCategory in
@[instance_reducible]
noncomputable def monoidalClosed [CartesianMonoidalCategory C] : MonoidalClosed C :=
  .mk fun A ↦
    have : (tensorLeft A).IsLeftAdjoint :=
      Functor.isLeftAdjoint_of_iso (CartesianMonoidalCategory.tensorLeftIsoProd A).symm
    Closed.mk _ (Adjunction.ofIsLeftAdjoint (tensorLeft A))

end Quasitopos

private theorem Over.isLeftAdjoint_pullback_presheaf_aux {A : Type v} [SmallCategory A]
    {P Q : Aᵒᵖ ⥤ Type v} (f : P ⟶ Q) : (Over.pullback f).IsLeftAdjoint := by
  have : PreservesColimitsOfSize.{v, v} (Over.pullback f) :=
    ⟨fun {_} _ => preservesColimitsOfShape_pullback_of_isUniversalColimit
      (fun hc => FunctorToTypes.isUniversalColimit hc) f⟩
  let e := overEquivPresheafCostructuredArrow Q
  have : HasColimitsOfSize.{v, v} (Over P) := inferInstance
  have : PreservesColimitsOfSize.{v, v} (e.inverse ⋙ Over.pullback f) := inferInstance
  have : (e.inverse ⋙ Over.pullback f).IsLeftAdjoint :=
    Presheaf.isLeftAdjoint_of_preservesColimits.{v} _
  exact Functor.isLeftAdjoint_of_iso
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e.unitIso.symm _ ≪≫
      Functor.leftUnitor _)

private theorem Over.isLeftAdjoint_pullback_of_equivalence {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] [HasPullbacks C] [HasPullbacks D] (e : C ≌ D) {P Q : C}
    (f : P ⟶ Q) [(Over.pullback (e.functor.map f)).IsLeftAdjoint] :
    (Over.pullback f).IsLeftAdjoint := by
  let EP := Over.postEquiv P e
  let EQ := Over.postEquiv Q e
  let j : Over.map f ⋙ Over.post e.functor ≅ Over.post e.functor ⋙ Over.map (e.functor.map f) :=
    NatIso.ofComponents (fun X => Over.isoMk (Iso.refl _)
      ((Category.id_comp _).trans (e.functor.map_comp _ _).symm))
      (fun g => Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm))
  let i : Over.map f ≅ EP.functor ⋙ Over.map (e.functor.map f) ⋙ EQ.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ EQ.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight j _ ≪≫
        Functor.associator _ _ _
  let adj : Over.map f ⊣ EQ.functor ⋙ Over.pullback (e.functor.map f) ⋙ EP.inverse :=
    (EP.toAdjunction.comp ((Over.mapPullbackAdj _).comp EQ.symm.toAdjunction)).ofNatIsoLeft
      i.symm
  exact Functor.isLeftAdjoint_of_iso ((Over.mapPullbackAdj f).rightAdjointUniq adj).symm

instance Over.isLeftAdjoint_pullback_presheaf {A : Type v} [SmallCategory A]
    {P Q : Aᵒᵖ ⥤ Type (max w v)} (f : P ⟶ Q) : (Over.pullback f).IsLeftAdjoint :=
  have := Over.isLeftAdjoint_pullback_presheaf_aux
    (((AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft).functor.map f)
  Over.isLeftAdjoint_pullback_of_equivalence
    (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft f

instance Quasitopos.presheaf {A : Type v} [SmallCategory A] :
    Quasitopos (Aᵒᵖ ⥤ Type (max w v)) where
  isLeftAdjoint_pullback _ := inferInstance
  nonempty_strongClassifier :=
    ⟨Subobject.StrongClassifier.ofClassifier (HasSubobjectClassifier.exists_classifier.some)⟩

end CategoryTheory
