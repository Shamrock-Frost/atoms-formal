import Atoms.Homotopical.Localizer.InverseImage
import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.BinaryProducts

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace Atoms.Homotopical

universe v u u'

section Quillen

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v} B]

structure CylinderCompatible (u : A ⥤ B) (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v))
    (𝕁 : ExactCylinder.{v} (Bᵒᵖ ⥤ Type v)) where
  lan : (Aᵒᵖ ⥤ Type v) ⥤ (Bᵒᵖ ⥤ Type v)
  adj : lan ⊣ (Functor.whiskeringLeft Aᵒᵖ Bᵒᵖ (Type v)).obj u.op
  iso : 𝕀.I ⋙ lan ≅ lan ⋙ 𝕁.I
  endpoint_comp : ∀ (ε : Bool) (X : Aᵒᵖ ⥤ Type v),
    lan.map ((𝕀.endpoint ε).app X) ≫ iso.hom.app X = (𝕁.endpoint ε).app (lan.obj X)
  contraction_comp : ∀ X : Aᵒᵖ ⥤ Type v,
    iso.hom.app X ≫ (𝕁.contraction).app (lan.obj X) = lan.map ((𝕀.contraction).app X)

end Quillen

end Atoms.Homotopical

namespace HomotopicalAlgebra.ExactCylinder

open Atoms.Homotopical

universe v u u'

variable {A : Type u} [Category.{v} A]

@[simps]
def overCylinderFunctor (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (X : Aᵒᵖ ⥤ Type v) :
    Over X ⥤ Over X where
  obj K := Over.mk (𝕀.contraction.app K.left ≫ K.hom)
  map {K L} f := Over.homMk (𝕀.I.map f.left) (by
    have h := 𝕀.contraction.naturality f.left
    simp only [Functor.id_map] at h
    simp only [Over.mk_hom]
    rw [← Category.assoc, h, Category.assoc, Over.w])
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

variable (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (X : Aᵒᵖ ⥤ Type v)

@[simps]
def overEndpoint (ε : Bool) : 𝟭 (Over X) ⟶ 𝕀.overCylinderFunctor X where
  app K := Over.homMk ((𝕀.endpoint ε).app K.left) (by
    change (𝕀.endpoint ε).app K.left ≫ 𝕀.contraction.app K.left ≫ K.hom = K.hom
    rw [𝕀.endpoint_app_contraction_app_assoc])
  naturality K L f := Over.OverMorphism.ext ((𝕀.endpoint ε).naturality f.left)

@[simps]
def overContraction : 𝕀.overCylinderFunctor X ⟶ 𝟭 (Over X) where
  app K := Over.homMk (𝕀.contraction.app K.left)
  naturality K L f := Over.OverMorphism.ext (𝕀.contraction.naturality f.left)

@[reassoc]
theorem overEndpoint_app_overContraction_app (ε : Bool) (K : Over X) :
    (𝕀.overEndpoint X ε).app K ≫ (𝕀.overContraction X).app K = 𝟙 K :=
  Over.OverMorphism.ext (𝕀.endpoint_app_contraction_app ε K.left)

end HomotopicalAlgebra.ExactCylinder

namespace Atoms.Homotopical

universe v u u'

variable {A : Type v} [SmallCategory A]

end Atoms.Homotopical

namespace HomotopicalAlgebra.ExactCylinder

open Atoms.Homotopical

universe v u u'

variable {A : Type v} [SmallCategory A]

variable (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (X : Aᵒᵖ ⥤ Type v)

abbrev overI :
    ((CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) ⥤ ((CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) :=
  (overEquivPresheafCostructuredArrow X).inverse ⋙ 𝕀.overCylinderFunctor X ⋙
    (overEquivPresheafCostructuredArrow X).functor

def overIEndpoint (ε : Bool) : 𝟭 _ ⟶ 𝕀.overI X :=
  (overEquivPresheafCostructuredArrow X).counitInv ≫
    Functor.whiskerLeft (overEquivPresheafCostructuredArrow X).inverse
      (Functor.whiskerRight (𝕀.overEndpoint X ε) (overEquivPresheafCostructuredArrow X).functor)

def overIContraction : 𝕀.overI X ⟶ 𝟭 _ :=
  Functor.whiskerLeft (overEquivPresheafCostructuredArrow X).inverse
      (Functor.whiskerRight (𝕀.overContraction X) (overEquivPresheafCostructuredArrow X).functor) ≫
    (overEquivPresheafCostructuredArrow X).counit

theorem overIEndpoint_app (ε : Bool) (Y : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) :
    (𝕀.overIEndpoint X ε).app Y = (overEquivPresheafCostructuredArrow X).counitInv.app Y ≫
      (overEquivPresheafCostructuredArrow X).functor.map
        ((𝕀.overEndpoint X ε).app ((overEquivPresheafCostructuredArrow X).inverse.obj Y)) :=
  rfl

theorem overIContraction_app (Y : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) :
    (𝕀.overIContraction X).app Y = (overEquivPresheafCostructuredArrow X).functor.map
        ((𝕀.overContraction X).app ((overEquivPresheafCostructuredArrow X).inverse.obj Y)) ≫
      (overEquivPresheafCostructuredArrow X).counit.app Y :=
  rfl

def overIIso : 𝕀.overI X ⋙ sliceForget X ≅ sliceForget X ⋙ 𝕀.I :=
  NatIso.ofComponents
    (fun Y ↦ (Over.forget X).mapIso ((overEquivPresheafCostructuredArrow X).unitIso.app
      ((𝕀.overCylinderFunctor X).obj ((overEquivPresheafCostructuredArrow X).inverse.obj Y))).symm)
    (fun g ↦ congrArg CommaMorphism.left
      ((overEquivPresheafCostructuredArrow X).unitIso.inv.naturality
        ((𝕀.overCylinderFunctor X).map ((overEquivPresheafCostructuredArrow X).inverse.map g))))

theorem sliceForget_map_overIEndpoint_app (ε : Bool) (Y : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) :
    (sliceForget X).map ((𝕀.overIEndpoint X ε).app Y) ≫ (𝕀.overIIso X).hom.app Y =
      (𝕀.endpoint ε).app ((sliceForget X).obj Y) := by
  have h : (overEquivPresheafCostructuredArrow X).inverse.map ((𝕀.overIEndpoint X ε).app Y) ≫
      (overEquivPresheafCostructuredArrow X).unitInv.app
        ((𝕀.overCylinderFunctor X).obj ((overEquivPresheafCostructuredArrow X).inverse.obj Y)) =
      (𝕀.overEndpoint X ε).app ((overEquivPresheafCostructuredArrow X).inverse.obj Y) := by
    rw [overIEndpoint_app]
    simp
  exact congrArg CommaMorphism.left h

theorem overIIso_hom_app_contraction_app (Y : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) :
    (𝕀.overIIso X).hom.app Y ≫ 𝕀.contraction.app ((sliceForget X).obj Y) =
      (sliceForget X).map ((𝕀.overIContraction X).app Y) := by
  have h : (overEquivPresheafCostructuredArrow X).unitInv.app
        ((𝕀.overCylinderFunctor X).obj ((overEquivPresheafCostructuredArrow X).inverse.obj Y)) ≫
      (𝕀.overContraction X).app ((overEquivPresheafCostructuredArrow X).inverse.obj Y) =
      (overEquivPresheafCostructuredArrow X).inverse.map ((𝕀.overIContraction X).app Y) := by
    rw [overIContraction_app]
    simp
  exact congrArg CommaMorphism.left h

def over : ExactCylinder.{v} ((CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) where
  I := 𝕀.overI X
  endpoint ε := 𝕀.overIEndpoint X ε
  contraction := 𝕀.overIContraction X
  endpoint_contraction ε := by
    refine NatTrans.ext (funext fun Y ↦ ?_)
    rw [NatTrans.comp_app, overIEndpoint_app, overIContraction_app, Category.assoc,
      ← Functor.map_comp_assoc, overEndpoint_app_overContraction_app,
      CategoryTheory.Functor.map_id,
      Category.id_comp]
    exact (overEquivPresheafCostructuredArrow X).counitIso.inv_hom_id_app Y
  mono_endpoints Y := by
    rw [← (sliceForget X).mono_map_iff_mono]
    have h := coprodComparison_map_desc_comp (sliceForget X) _ _ ((𝕀.overIIso X).hom.app Y)
      _ _ (𝕀.sliceForget_map_overIEndpoint_app X false Y)
      (𝕀.sliceForget_map_overIEndpoint_app X true Y)
    have : (sliceForget X).IsLeftAdjoint := ⟨_, ⟨sliceForgetAdjunction X⟩⟩
    have hw : (sliceForget X).map (coprod.desc ((𝕀.overIEndpoint X false).app Y)
        ((𝕀.overIEndpoint X true).app Y)) ≫ (𝕀.overIIso X).hom.app Y =
        inv (coprodComparison (sliceForget X) Y Y) ≫ 𝕀.endpoints ((sliceForget X).obj Y) := by
      rw [IsIso.eq_inv_comp]
      exact h
    exact mono_of_mono_fac hw
  preservesMonomorphisms := ⟨fun {Y Z} g hg ↦ by
    rw [← (sliceForget X).mono_map_iff_mono]
    have : Mono ((sliceForget X).map g) := ((sliceForget X).mono_map_iff_mono g).2 hg
    change Mono ((𝕀.overI X ⋙ sliceForget X).map g)
    rw [← NatIso.naturality_2 (𝕀.overIIso X) g]
    change Mono ((𝕀.overIIso X).hom.app Y ≫ 𝕀.I.map ((sliceForget X).map g) ≫
      (𝕀.overIIso X).inv.app Z)
    infer_instance⟩
  preservesColimits := by
    have : PreservesColimitsOfSize.{v, v} (𝕀.overI X ⋙ sliceForget X) :=
      preservesColimits_of_natIso (𝕀.overIIso X).symm
    exact preservesColimits_of_reflects_of_preserves (𝕀.overI X) (sliceForget X)

noncomputable def cylinderCompatibleOver :
    CylinderCompatible (CostructuredArrow.proj yoneda X) (𝕀.over X) 𝕀 where
  lan := sliceForget X
  adj := sliceForgetAdjunction X
  iso := 𝕀.overIIso X
  endpoint_comp ε Y := 𝕀.sliceForget_map_overIEndpoint_app X ε Y
  contraction_comp Y := 𝕀.overIIso_hom_app_contraction_app X Y

end HomotopicalAlgebra.ExactCylinder

namespace Atoms.Homotopical

universe v u u'

variable {A : Type v} [SmallCategory A]

namespace CylinderCompatible

variable {C D : Type v} [SmallCategory C] [SmallCategory D] {u : C ⥤ D}
  {𝕀 : ExactCylinder.{v} (Cᵒᵖ ⥤ Type v)} {𝕁 : ExactCylinder.{v} (Dᵒᵖ ⥤ Type v)}
    (c : CylinderCompatible u 𝕀 𝕁)

theorem isPushout_map_endpointBoxSource (ε : Bool) {K Y : Cᵒᵖ ⥤ Type v} (i : K ⟶ Y) :
    IsPushout ((𝕁.endpoint ε).app (c.lan.obj K)) (c.lan.map i)
      (c.iso.inv.app K ≫ c.lan.map (pushout.inl ((𝕀.endpoint ε).app K) i))
      (c.lan.map (pushout.inr ((𝕀.endpoint ε).app K) i)) := by
  have : c.lan.IsLeftAdjoint := ⟨_, ⟨c.adj⟩⟩
  refine ((IsPushout.of_hasPushout ((𝕀.endpoint ε).app K) i).map c.lan).of_iso (Iso.refl _)
    (c.iso.app K) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.app_hom, Iso.refl_hom, Category.id_comp]
    exact c.endpoint_comp ε K
  · simp
  · simp
  · simp

theorem isoPushout_hom_endpointBox (ε : Bool) {K Y : Cᵒᵖ ⥤ Type v} (i : K ⟶ Y) :
    (c.isPushout_map_endpointBoxSource ε i).isoPushout.hom ≫ 𝕁.endpointBox ε (c.lan.map i) =
      c.lan.map (𝕀.endpointBox ε i) ≫ c.iso.hom.app Y := by
  dsimp only [ExactCylinder.endpointBox, ExactCylinder.endpointBoxSource]
  refine (c.isPushout_map_endpointBoxSource ε i).hom_ext ?_ ?_
  · rw [IsPushout.inl_isoPushout_hom_assoc]
    simp only [pushout.inl_desc, Category.assoc,
      ← Functor.map_comp_assoc]
    exact (NatIso.naturality_1 c.iso i).symm
  · rw [IsPushout.inr_isoPushout_hom_assoc]
    simp only [pushout.inr_desc, ← Functor.map_comp_assoc]
    exact (c.endpoint_comp ε Y).symm

noncomputable def endpointBoxArrowIso (ε : Bool) {K Y : Cᵒᵖ ⥤ Type v} (i : K ⟶ Y) :
    Arrow.mk (c.lan.map (𝕀.endpointBox ε i)) ≅ Arrow.mk (𝕁.endpointBox ε (c.lan.map i)) :=
  Arrow.isoMk (c.isPushout_map_endpointBoxSource ε i).isoPushout (c.iso.app Y)
    (c.isoPushout_hom_endpointBox ε i)

theorem isPushout_map_bothBoxSource {K Y : Cᵒᵖ ⥤ Type v} (i : K ⟶ Y) :
    IsPushout (𝕁.endpoints (c.lan.obj K)) (coprod.map (c.lan.map i) (c.lan.map i))
      (c.iso.inv.app K ≫ c.lan.map (pushout.inl (𝕀.endpoints K) (coprod.map i i)))
      (coprodComparison c.lan Y Y ≫ c.lan.map (pushout.inr (𝕀.endpoints K) (coprod.map i i))) := by
  have : c.lan.IsLeftAdjoint := ⟨_, ⟨c.adj⟩⟩
  refine ((IsPushout.of_hasPushout (𝕀.endpoints K) (coprod.map i i)).map c.lan).of_iso
    (asIso (coprodComparison c.lan K K)).symm (c.iso.app K)
    (asIso (coprodComparison c.lan Y Y)).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp, Iso.app_hom]
    exact coprodComparison_map_desc_comp c.lan _ _ _ _ _ (c.endpoint_comp false K)
      (c.endpoint_comp true K)
  · rw [Iso.symm_hom, asIso_inv, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp, ← Category.assoc,
      IsIso.comp_inv_eq, coprodComparison_natural]
  · simp
  · simp

theorem isoPushout_hom_bothBox {K Y : Cᵒᵖ ⥤ Type v} (i : K ⟶ Y) :
    (c.isPushout_map_bothBoxSource i).isoPushout.hom ≫ 𝕁.bothBox (c.lan.map i) =
      c.lan.map (𝕀.bothBox i) ≫ c.iso.hom.app Y := by
  dsimp only [ExactCylinder.bothBox, ExactCylinder.bothBoxSource]
  refine (c.isPushout_map_bothBoxSource i).hom_ext ?_ ?_
  · rw [IsPushout.inl_isoPushout_hom_assoc]
    simp only [pushout.inl_desc, Category.assoc,
      ← Functor.map_comp_assoc]
    exact (NatIso.naturality_1 c.iso i).symm
  · rw [IsPushout.inr_isoPushout_hom_assoc]
    simp only [pushout.inr_desc, Category.assoc,
      ← Functor.map_comp_assoc]
    exact (coprodComparison_map_desc_comp c.lan _ _ _ _ _ (c.endpoint_comp false Y)
      (c.endpoint_comp true Y)).symm

noncomputable def bothBoxArrowIso {K Y : Cᵒᵖ ⥤ Type v} (i : K ⟶ Y) :
    Arrow.mk (c.lan.map (𝕀.bothBox i)) ≅ Arrow.mk (𝕁.bothBox (c.lan.map i)) :=
  Arrow.isoMk (c.isPushout_map_bothBoxSource i).isoPushout (c.iso.app Y)
    (c.isoPushout_hom_bothBox i)

end CylinderCompatible

def sliceGenerators (T : MorphismProperty (Aᵒᵖ ⥤ Type v)) (X : Aᵒᵖ ⥤ Type v) :
    MorphismProperty ((CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) :=
  MorphismProperty.ofHoms fun j : (Σ f : T.toSet, (f.1.right ⟶ X)) ↦ sliceHom j.1.1.hom j.2

instance isSmall_sliceGenerators (T : MorphismProperty (Aᵒᵖ ⥤ Type v)) [T.IsSmall.{v}]
    (X : Aᵒᵖ ⥤ Type v) : (sliceGenerators T X).IsSmall.{v} :=
  MorphismProperty.isSmall_ofHoms _

theorem sliceGenerators_le_monomorphisms (T : MorphismProperty (Aᵒᵖ ⥤ Type v))
    (hT : T ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)) (X : Aᵒᵖ ⥤ Type v) :
    sliceGenerators T X ≤ MorphismProperty.monomorphisms _ := by
  rintro _ _ _ ⟨j⟩
  rw [monomorphisms_eq_inverseImage_sliceForget]
  exact ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff
    (sliceForgetMapSliceHomIso j.1.1.hom j.2)).2 (hT j.1.1.hom j.1.2)

theorem hasLiftingProperty_sliceHom_of_rlp {T : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    {X K L : Aᵒᵖ ⥤ Type v} (f : K ⟶ L) (hf : T f) (l : L ⟶ X)
    {Y' Z' : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v} (p : Y' ⟶ Z')
    (hp : T.rlp ((sliceForget X).map p)) : HasLiftingProperty (sliceHom f l) p := by
  have := hp f hf
  have : HasLiftingProperty ((sliceForget X).map (sliceHom f l)) ((sliceForget X).map p) :=
    HasLiftingProperty.of_arrow_iso_left (sliceForgetMapSliceHomIso f l).symm _
  exact hasLiftingProperty_of_sliceForget _ p

theorem rlp_sliceGenerators (T : MorphismProperty (Aᵒᵖ ⥤ Type v)) (X : Aᵒᵖ ⥤ Type v) :
    (sliceGenerators T X).rlp = T.rlp.inverseImage (sliceForget X) := by
  ext Y' Z' p
  constructor
  · intro hp K L i hi
    constructor
    intro a b sq
    have : HasLiftingProperty (sliceHom i (b ≫ (sliceForgetπ X).app Z')) p :=
      hp _ (MorphismProperty.ofHoms.mk
        (⟨⟨Arrow.mk i, hi⟩, b ≫ (sliceForgetπ X).app Z'⟩ : Σ f : T.toSet, (f.1.right ⟶ X)))
    exact hasLift_of_sliceHom sq
  · rintro hp _ _ _ ⟨j⟩
    exact hasLiftingProperty_sliceHom_of_rlp j.1.1.hom j.1.2 j.2 p hp

noncomputable def sliceForgetMapTerminalFromArrowIso (X : Aᵒᵖ ⥤ Type v)
    (Y : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) :
    Arrow.mk ((sliceForget X).map (terminal.from Y)) ≅ Arrow.mk ((sliceForgetπ X).app Y) :=
  Arrow.isoMk (Iso.refl _) ((Over.forget X).mapIso
    ((terminalIsTerminal.isTerminalObj (overEquivPresheafCostructuredArrow X).inverse
      _).uniqueUpToIso Over.mkIdTerminal)) (by
    rw [Functor.mapIso_hom, IsTerminal.uniqueUpToIso_hom, Over.forget_map,
      Over.mkIdTerminal_from_left, Iso.refl_hom, Category.id_comp]
    exact (Over.w ((overEquivPresheafCostructuredArrow X).inverse.map (terminal.from Y))).symm)

end Atoms.Homotopical

namespace HomotopicalAlgebra.ExactCylinder

open Atoms.Homotopical

universe v u u'

variable {A : Type v} [SmallCategory A]

theorem anodyne_over_le (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (S : MorphismProperty (Aᵒᵖ ⥤ Type v))
    (X : Aᵒᵖ ⥤ Type v) :
    (𝕀.over X).anodyne (sliceGenerators S X) ≤ (𝕀.anodyne S).inverseImage (sliceForget X) :=
  (𝕀.over X).anodyne_le _ _
    { isSaturated := IsSaturated.inverseImage (sliceForget X) _
      generators_le := by
        rintro _ _ _ ⟨j⟩
        exact ((𝕀.anodyne S).arrow_mk_iso_iff (sliceForgetMapSliceHomIso j.1.1.hom j.2)).2
          (𝕀.le_anodyne S j.1.1.hom j.1.2)
      endpointBox_mem := fun ε {_ _} i hi ↦
        ((𝕀.anodyne S).arrow_mk_iso_iff
          ((𝕀.cylinderCompatibleOver X).endpointBoxArrowIso ε i)).2
          ((𝕀.isAnodyneClass_anodyne S).endpointBox_mem ε _
            (((sliceForget X).mono_map_iff_mono i).2 hi))
      bothBox_mem := fun {_ _} i hi h ↦
        ((𝕀.anodyne S).arrow_mk_iso_iff ((𝕀.cylinderCompatibleOver X).bothBoxArrowIso i)).2
          ((𝕀.isAnodyneClass_anodyne S).bothBox_mem _
            (((sliceForget X).mono_map_iff_mono i).2 hi) h) }

theorem anodyne_over_eq_of_eq_saturation (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v))
    (S T : MorphismProperty (Aᵒᵖ ⥤ Type v)) [T.IsSmall.{v}]
    (h : 𝕀.anodyne S = saturation.{v} T) (X : Aᵒᵖ ⥤ Type v) :
    (𝕀.over X).anodyne (sliceGenerators T X) = (𝕀.anodyne S).inverseImage (sliceForget X) := by
  have hTS : 𝕀.anodyne T ≤ 𝕀.anodyne S :=
    𝕀.anodyne_le T _
      { isSaturated := inferInstance
        generators_le := by
          rw [h]
          exact le_saturation.{v} T
        endpointBox_mem := (𝕀.isAnodyneClass_anodyne S).endpointBox_mem
        bothBox_mem := (𝕀.isAnodyneClass_anodyne S).bothBox_mem }
  refine le_antisymm ((𝕀.anodyne_over_le T X).trans fun _ _ f hf ↦ hTS _ hf) ?_
  have hsat : saturation.{v} (sliceGenerators T X) =
      (𝕀.anodyne S).inverseImage (sliceForget X) := by
    rw [h, saturation_eq_llp_rlp T, ← llp_inverseImage_sliceForget X T.rlp,
      ← rlp_sliceGenerators T X, saturation_eq_llp_rlp]
  rw [← hsat]
  exact saturation_le _ _ ((𝕀.over X).le_anodyne _)

theorem anodyne_over_eq (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (S : MorphismProperty (Aᵒᵖ ⥤ Type v))
    [S.IsSmall.{v}] (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    (X : Aᵒᵖ ⥤ Type v) :
    (𝕀.over X).anodyne (sliceGenerators (𝕀.anodyneGenerators S) X) =
      (𝕀.anodyne S).inverseImage (sliceForget X) :=
  have := 𝕀.isSmall_anodyneGenerators S
  𝕀.anodyne_over_eq_of_eq_saturation S _ (𝕀.anodyne_eq_saturation_anodyneGenerators S hS) X

theorem rlp_anodyne_over_eq (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (S : MorphismProperty
    (Aᵒᵖ ⥤ Type v))
    [S.IsSmall.{v}] (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    (X : Aᵒᵖ ⥤ Type v) :
    ((𝕀.over X).anodyne (sliceGenerators (𝕀.anodyneGenerators S) X)).rlp =
      (𝕀.naiveFibrations S).inverseImage (sliceForget X) := by
  rw [𝕀.anodyne_over_eq S hS X, rlp_inverseImage_sliceForget_of_respectsIso]

theorem isFibrant_over_iff (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (S : MorphismProperty
    (Aᵒᵖ ⥤ Type v))
    [S.IsSmall.{v}] (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    (X : Aᵒᵖ ⥤ Type v) (Y : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) :
    (𝕀.over X).IsFibrant (sliceGenerators (𝕀.anodyneGenerators S) X) Y ↔
      𝕀.naiveFibrations S ((sliceForgetπ X).app Y) := by
  rw [ExactCylinder.IsFibrant, 𝕀.rlp_anodyne_over_eq S hS X]
  exact (𝕀.naiveFibrations S).arrow_mk_iso_iff (sliceForgetMapTerminalFromArrowIso X Y)

def overWeakEquivalences (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (S : MorphismProperty
    (Aᵒᵖ ⥤ Type v))
    (X : Aᵒᵖ ⥤ Type v) :
    MorphismProperty ((CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) :=
  (𝕀.over X).weakEquivalences (sliceGenerators (𝕀.anodyneGenerators S) X)

theorem overWeakEquivalences_le (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (S : MorphismProperty
    (Aᵒᵖ ⥤ Type v))
    [S.IsSmall.{v}] (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    (X : Aᵒᵖ ⥤ Type v) :
    𝕀.overWeakEquivalences S X ≤ (𝕀.weakEquivalences S).inverseImage (sliceForget X) := by
  have := 𝕀.isSmall_anodyneGenerators S
  have hT := sliceGenerators_le_monomorphisms _ (𝕀.anodyneGenerators_le_monomorphisms S hS) X
  rw [overWeakEquivalences, (𝕀.over X).weakEquivalences_eq_generatedALocalizer _ hT]
  have := 𝕀.isALocalizer_weakEquivalences S hS
  refine generatedALocalizer_le ?_
  refine iSup_le fun n ↦ ((𝕀.over X).anodyneGeneratorsStage_le_anodyne _ hT n).trans ?_
  rw [𝕀.anodyne_over_eq S hS X]
  exact fun _ _ f hf ↦ 𝕀.anodyne_le_weakEquivalences S hS _ hf

theorem weakEquivalences_over_eq_of_eq_saturation (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v))
    (S T : MorphismProperty (Aᵒᵖ ⥤ Type v))
    [S.IsSmall.{v}] (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    [T.IsSmall.{v}] (h : 𝕀.anodyne S = saturation.{v} T) (X : Aᵒᵖ ⥤ Type v) :
    (𝕀.over X).weakEquivalences (sliceGenerators T X) = 𝕀.overWeakEquivalences S X :=
  (𝕀.over X).weakEquivalences_eq_of_anodyne_eq
    ((𝕀.anodyne_over_eq_of_eq_saturation S T h X).trans (𝕀.anodyne_over_eq S hS X).symm)

end HomotopicalAlgebra.ExactCylinder
