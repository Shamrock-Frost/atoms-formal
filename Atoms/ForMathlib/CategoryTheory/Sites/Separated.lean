import Atoms.ForMathlib.CategoryTheory.Presentable.IsCardinalFiltered
import Mathlib.CategoryTheory.ObjectProperty.EpiMono
import Mathlib.CategoryTheory.Presentable.Adjunction
import Mathlib.CategoryTheory.Presentable.Presheaf
import Mathlib.CategoryTheory.Presentable.Type
import Mathlib.CategoryTheory.Sites.LocallyInjective

universe w v u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

namespace Presieve

def LocallyEq (P : Cᵒᵖ ⥤ Type w) {c : Cᵒᵖ} (x y : P.obj c) : Prop :=
  Presheaf.equalizerSieve (F := P) x y ∈ J c.unop

variable {J}

theorem isSeparated_iff_locallyEq {P : Cᵒᵖ ⥤ Type w} :
    IsSeparated J P ↔ ∀ (c : Cᵒᵖ) (x y : P.obj c), LocallyEq J P x y → x = y := by
  refine ⟨fun h c x y hxy => (h _ hxy).ext fun _ _ hf => hf, fun h c S hS => ?_⟩
  intro t t₁ t₂ h₁ h₂
  refine h (op c) t₁ t₂ (J.superset_covering (fun d f hf => ?_) hS)
  change P.map f.op t₁ = P.map f.op t₂
  rw [h₁ f hf, h₂ f hf]

theorem IsSeparated.eq_of_locallyEq {P : Cᵒᵖ ⥤ Type w} (hP : IsSeparated J P) {c : Cᵒᵖ}
    {x y : P.obj c} (h : LocallyEq J P x y) : x = y :=
  isSeparated_iff_locallyEq.1 hP c x y h

theorem locallyEq_equivalence (P : Cᵒᵖ ⥤ Type w) (c : Cᵒᵖ) :
    _root_.Equivalence (LocallyEq J P (c := c)) where
  refl x := by
    unfold LocallyEq
    rw [Presheaf.equalizerSieve_self_eq_top]
    exact J.top_mem _
  symm {x y} h := J.superset_covering (fun _ _ hf => Eq.symm hf) h
  trans {x y z} h₁ h₂ := by
    refine J.superset_covering ?_ (J.intersection_covering h₁ h₂)
    intro d f hf
    exact Eq.trans hf.1 hf.2

theorem LocallyEq.map {P : Cᵒᵖ ⥤ Type w} {c c' : Cᵒᵖ} (f : c ⟶ c') {x y : P.obj c}
    (h : LocallyEq J P x y) : LocallyEq J P (P.map f x) (P.map f y) := by
  refine J.superset_covering (fun d g hg => ?_) (J.pullback_stable f.unop h)
  change P.map (g ≫ f.unop).op x = P.map (g ≫ f.unop).op y at hg
  change P.map g.op (P.map f x) = P.map g.op (P.map f y)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  exact hg

theorem LocallyEq.app {P Q : Cᵒᵖ ⥤ Type w} (φ : P ⟶ Q) {c : Cᵒᵖ} {x y : P.obj c}
    (h : LocallyEq J P x y) : LocallyEq J Q (φ.app c x) (φ.app c y) := by
  refine J.superset_covering (fun d f hf => ?_) h
  change P.map f.op x = P.map f.op y at hf
  change Q.map f.op (φ.app c x) = Q.map f.op (φ.app c y)
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hf]

theorem LocallyEq.of_app {P Q : Cᵒᵖ ⥤ Type w} (φ : P ⟶ Q)
    (hφ : ∀ c, Function.Injective (φ.app c)) {c : Cᵒᵖ} {x y : P.obj c}
    (h : LocallyEq J Q (φ.app c x) (φ.app c y)) : LocallyEq J P x y := by
  have := Presheaf.isLocallyInjective_of_injective J φ hφ
  unfold LocallyEq at h ⊢
  exact Presheaf.equalizerSieve_mem_of_equalizerSieve_app_mem J φ x y h

end Presieve

abbrev SeparatedPresheaf : Type (max u v (w + 1)) :=
  ObjectProperty.FullSubcategory (C := Cᵒᵖ ⥤ Type w) (Presieve.IsSeparated J)

namespace SeparatedPresheaf

instance isClosedUnderSubobjects :
    ObjectProperty.IsClosedUnderSubobjects (C := Cᵒᵖ ⥤ Type w) (Presieve.IsSeparated J) where
  prop_of_mono φ _ hQ _ S hS := (hQ S hS).of_mono φ

instance isClosedUnderLimitsOfShape {K : Type*} [Category K] [HasLimitsOfShape K (Type w)] :
    ObjectProperty.IsClosedUnderLimitsOfShape (C := Cᵒᵖ ⥤ Type w) (Presieve.IsSeparated J) K
    where
  limitsOfShape_le X := fun ⟨h⟩ => Presieve.isSeparated_iff_locallyEq.2 fun c x y hxy => by
    have hl := isLimitOfPreserves ((evaluation Cᵒᵖ (Type w)).obj c) h.isLimit
    exact (Types.isLimitEquivSections hl).injective (Subtype.ext (funext fun k =>
      (h.prop_diag_obj k).eq_of_locallyEq (hxy.app (h.π.app k))))

def reflectionObj (P : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type w where
  obj c := Quot (Presieve.LocallyEq J P (c := c))
  map f := ↾Quot.lift (fun x => Quot.mk _ (P.map f x)) fun _ _ h => Quot.sound (h.map f)
  map_id c := by
    ext x
    induction x using Quot.ind
    exact congrArg (Quot.mk _) (Functor.map_id_apply P _ _)
  map_comp f g := by
    ext x
    induction x using Quot.ind
    exact congrArg (Quot.mk _) (Functor.map_comp_apply P f g _)

def toReflectionObj (P : Cᵒᵖ ⥤ Type w) : P ⟶ reflectionObj J P where
  app _ := ↾Quot.mk _
  naturality _ _ _ := rfl

variable {J}

theorem toReflectionObj_app_eq_iff {P : Cᵒᵖ ⥤ Type w} {c : Cᵒᵖ} (x y : P.obj c) :
    (toReflectionObj J P).app c x = (toReflectionObj J P).app c y ↔
      Presieve.LocallyEq J P x y :=
  Equivalence.quot_mk_eq_iff (Presieve.locallyEq_equivalence P c) x y

theorem surjective_toReflectionObj_app (P : Cᵒᵖ ⥤ Type w) (c : Cᵒᵖ) :
    Function.Surjective ((toReflectionObj J P).app c) :=
  Quot.mk_surjective

theorem isSeparated_reflectionObj (P : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSeparated J (reflectionObj J P) := by
  refine Presieve.isSeparated_iff_locallyEq.2 fun c x y h => ?_
  obtain ⟨x, rfl⟩ := Quot.mk_surjective x
  obtain ⟨y, rfl⟩ := Quot.mk_surjective y
  refine Quot.sound (J.transitive h _ fun d f hf => ?_)
  have hf' : (toReflectionObj J P).app (op d) (P.map f.op x) =
      (toReflectionObj J P).app (op d) (P.map f.op y) := hf
  refine J.superset_covering (fun e g hg => ?_) ((toReflectionObj_app_eq_iff _ _).1 hf')
  change P.map g.op (P.map f.op x) = P.map g.op (P.map f.op y) at hg
  change P.map (g ≫ f).op x = P.map (g ≫ f).op y
  rwa [op_comp, Functor.map_comp_apply, Functor.map_comp_apply]

private def reflectionDesc {P Q : Cᵒᵖ ⥤ Type w} (hQ : Presieve.IsSeparated J Q) (φ : P ⟶ Q) :
    reflectionObj J P ⟶ Q where
  app c := ↾Quot.lift (φ.app c) fun _ _ h => hQ.eq_of_locallyEq (h.app φ)
  naturality c c' f := by
    ext x
    induction x using Quot.ind
    exact NatTrans.naturality_apply φ f _

variable (J)

private def reflectionHomEquiv (P : Cᵒᵖ ⥤ Type w) (Q : SeparatedPresheaf.{w} J) :
    (⟨reflectionObj J P, isSeparated_reflectionObj P⟩ ⟶ Q) ≃ (P ⟶ Q.obj) where
  toFun f := toReflectionObj J P ≫ f.hom
  invFun φ := ObjectProperty.homMk (reflectionDesc Q.2 φ)
  left_inv f := by
    ext c x
    induction x using Quot.ind
    rfl
  right_inv _ := rfl

def reflection : (Cᵒᵖ ⥤ Type w) ⥤ SeparatedPresheaf.{w} J :=
  Adjunction.leftAdjointOfEquiv (G := ObjectProperty.ι _) (reflectionHomEquiv J)
    fun _ _ _ _ _ => rfl

def adjunction : reflection J ⊣ ObjectProperty.ι _ :=
  Adjunction.adjunctionOfEquivLeft _ _

theorem adjunction_unit_app (P : Cᵒᵖ ⥤ Type w) :
    (adjunction J).unit.app P = toReflectionObj J P :=
  Category.comp_id (toReflectionObj J P)

instance preservesMonomorphisms_reflection : (reflection J).PreservesMonomorphisms where
  preserves {P Q} φ _ := by
    have hφ (c : Cᵒᵖ) : Function.Injective (φ.app c) :=
      (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app φ).1 inferInstance c)
    refine (ObjectProperty.ι _).mono_of_mono_map ((NatTrans.mono_iff_mono_app _).2 fun c =>
      (mono_iff_injective _).2 fun x y h => ?_)
    obtain ⟨x, rfl⟩ := Quot.mk_surjective x
    obtain ⟨y, rfl⟩ := Quot.mk_surjective y
    exact Quot.sound (Presieve.LocallyEq.of_app φ hφ ((toReflectionObj_app_eq_iff _ _).1 h))

section Presentable

variable {C : Type v} [SmallCategory C] (J : GrothendieckTopology C) (κ : Cardinal.{max w v})
  [Fact κ.IsRegular]

theorem isClosedUnderColimitsOfShape_of_hasCardinalLT (hC : HasCardinalLT (Arrow C) κ)
    (K : Type (max w v)) [SmallCategory K] [IsCardinalFiltered K κ] :
    ObjectProperty.IsClosedUnderColimitsOfShape (C := Cᵒᵖ ⥤ Type (max w v))
      (Presieve.IsSeparated J) K
    where
  colimitsOfShape_le X := fun ⟨h⟩ => Presieve.isSeparated_iff_locallyEq.2 fun c x y hxy => by
    have := isFiltered_of_isCardinalFiltered K κ
    have hev (c' : Cᵒᵖ) :
        IsColimit (((evaluation Cᵒᵖ (Type (max w v))).obj c').mapCocone h.cocone) :=
      isColimitOfPreserves ((evaluation Cᵒᵖ (Type (max w v))).obj c') h.isColimit
    obtain ⟨j, a, b, rfl, rfl⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ (hev c) x y
    let S : Type v := Σ d : C, {f : d ⟶ c.unop // Presheaf.equalizerSieve (F := X)
      ((h.ι.app j).app c a) ((h.ι.app j).app c b) f}
    have hS : HasCardinalLT S κ := hC.of_injective (fun s => Arrow.mk s.2.1) (by
      rintro ⟨d, f, hf⟩ ⟨d', f', hf'⟩ he
      obtain rfl : d = d' := congrArg Comma.left he
      obtain rfl : f = f' := by simpa using Arrow.mk_injective _ _ he
      rfl)
    obtain ⟨m, t, ht⟩ := IsCardinalFiltered.exists_map_eq_of_isColimit hS
      (fun s => hev (op s.1)) (fun s => (h.diag.obj j).map s.2.1.op a)
      (fun s => (h.diag.obj j).map s.2.1.op b) fun s => by
        have := s.2.2
        change X.map s.2.1.op ((h.ι.app j).app c a) = X.map s.2.1.op ((h.ι.app j).app c b) at this
        rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply] at this
        exact this
    have hm : (h.diag.map t).app c a = (h.diag.map t).app c b := by
      refine (h.prop_diag_obj m).eq_of_locallyEq (J.superset_covering ?_ hxy)
      intro d f hf
      change (h.diag.obj m).map f.op ((h.diag.map t).app c a) =
        (h.diag.obj m).map f.op ((h.diag.map t).app c b)
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
      exact ht ⟨d, f, hf⟩
    have hw := congrArg (fun φ => φ.app c) (h.cocone.w t)
    change (h.diag.map t ≫ h.ι.app m).app c = (h.ι.app j).app c at hw
    change (h.ι.app j).app c a = (h.ι.app j).app c b
    rw [← hw, NatTrans.comp_app, types_comp_apply, types_comp_apply, hm]

theorem isCardinalAccessible_ι (hC : HasCardinalLT (Arrow C) κ) :
    (ObjectProperty.ι (C := Cᵒᵖ ⥤ Type (max w v)) (Presieve.IsSeparated J)).IsCardinalAccessible
      κ where
  preservesColimitOfShape K _ _ :=
    have := isClosedUnderColimitsOfShape_of_hasCardinalLT J κ hC K
    inferInstance

instance isAccessible_ι :
    (ObjectProperty.ι (C := Cᵒᵖ ⥤ Type (max w v))
      (Presieve.IsSeparated J)).IsAccessible.{max w v} := by
  obtain ⟨κ, hκ, hC⟩ := HasCardinalLT.exists_regular_cardinal.{max w v} (Arrow C)
  have : Fact κ.IsRegular := ⟨hκ⟩
  have := isCardinalAccessible_ι J κ hC
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

instance isLocallyPresentable : IsLocallyPresentable.{max w v} (SeparatedPresheaf.{max w v} J) := by
  obtain ⟨κ, hκ, hC⟩ := HasCardinalLT.exists_regular_cardinal.{max w v} (Arrow C)
  have : Fact κ.IsRegular := ⟨hκ⟩
  have := isCardinalAccessible_ι J κ hC
  have : IsCardinalLocallyPresentable (Cᵒᵖ ⥤ Type (max w v)) κ :=
    ((AsSmall.equiv : C ≌ AsSmall.{max w v} C).op.congrLeft).symm.isCardinalLocallyPresentable κ
  exact ⟨κ, inferInstance, (adjunction J).isCardinalLocallyPresentable κ⟩

end Presentable

end SeparatedPresheaf

end CategoryTheory
