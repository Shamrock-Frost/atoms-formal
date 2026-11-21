import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Elements
import Atoms.TestCategory.Simplicial.RightAdjointWeakness
import Atoms.TestCategory.Simplicial.KanBasicLocalizer

open CategoryTheory Limits Opposite
open Atoms.Homotopical Simplicial MorphismProperty

namespace Atoms.TestCategory

universe u

def ordinaryNerveResolution :
    SSet.asSmall.{u} ⋙ ordinaryNerveElements (AsSmall.{u} SimplexCategory) ⟶ 𝟭 SSet.{u} where
  app K :=
    { app := fun _ => ↾fun σ =>
        K.map (SimplexCategory.lastVertexHom
            (σ ⋙ (CategoryOfElements.π (SSet.asSmall.obj K)).leftOp)).op
          (σ.obj (Fin.last _)).unop.2
      naturality := by
        intro n n' θ
        ext σ
        exact SSet.map_lastVertexHom_toCat_comp K θ.unop σ }
  naturality := by
    intro K L g
    ext n σ
    exact (NatTrans.naturality_apply g _ _).symm

def ordinaryNerveResolutionLastVertexNatTrans (K : SSet.{u}) :
    ((elementsFunctor (AsSmall.{u} SimplexCategory)).map
        (SSet.asSmall.map (ordinaryNerveResolution.app K))).toFunctor ⟶
      (lastVertexFunctor
        ((elementsFunctor (AsSmall.{u} SimplexCategory)).obj (SSet.asSmall.obj K))).toFunctor where
  app X := (CategoryOfElements.homMk _ _
    (Quiver.Hom.op (ULift.up (SimplexCategory.lastVertexHom ((X.unop.2 : ComposableArrows _ _) ⋙
      (CategoryOfElements.π (SSet.asSmall.obj K)).leftOp)) : X.unop.1.unop ⟶ _)) rfl).op
  naturality {X Y} f := by
    apply SSet.elementsHom_ext
    exact SSet.comp_lastVertexHom_eq K f.unop.1.unop.down Y.unop.2 X.unop.2 f.unop.2 _

namespace BasicLocalizer

theorem ordinaryNerveResolution_mem (𝒲 : BasicLocalizer.{u}) (K : SSet.{u}) :
    𝒲.wSSet (ordinaryNerveResolution.app K) :=
  (𝒲.W_iff_of_natTrans (ordinaryNerveResolutionLastVertexNatTrans K)).2
    (𝒲.W_of_asphericalFunctor (𝒲.asphericalFunctor_lastVertexFunctor _))

end BasicLocalizer

theorem ordinaryNerveResolution_kanWeak (K : SSet.{u}) :
    kanWeak (ordinaryNerveResolution.{u}.app K) := by
  have h := kanBasicLocalizer.ordinaryNerveResolution_mem K
  rwa [kanBasicLocalizer_wSSet] at h

noncomputable def elementsFunctorAdjunctionOrdinaryNerve (A : Type u) [SmallCategory A] :
    elementsFunctor A ⊣ CategoryTheory.nerveFunctor ⋙ ordinaryNerveElementsRightAdjoint A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X C => CategoryTheory.nerveFunctor.fullyfaithful.homEquiv.trans
        ((ordinaryNerveElementsAdjunction A).homEquiv X (CategoryTheory.nerveFunctor.obj C))
      homEquiv_naturality_left_symm := by
        intro X X' C f g
        apply CategoryTheory.nerveFunctor.map_injective
        exact (CategoryTheory.nerveFunctor.fullyfaithful.map_preimage _).trans
          (((ordinaryNerveElementsAdjunction A).homEquiv_naturality_left_symm f g).trans
            ((congrArg (fun φ => _ ≫ φ)
              (CategoryTheory.nerveFunctor.fullyfaithful.map_preimage _).symm).trans
                (CategoryTheory.nerveFunctor.map_comp _ _).symm))
      homEquiv_naturality_right := by
        intro X C C' f g
        exact (congrArg ((ordinaryNerveElementsAdjunction A).homEquiv X _)
          (CategoryTheory.nerveFunctor.map_comp f g)).trans
            ((ordinaryNerveElementsAdjunction A).homEquiv_naturality_right _ _) }

namespace BasicLocalizer

theorem ordinaryNerveElements_unit_mem (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
    [hA : 𝒲.IsTest A] (X : Aᵒᵖ ⥤ Type u) :
    𝒲.wPsh A ((ordinaryNerveElementsAdjunction A).unit.app X) := by
  let adj := elementsFunctorAdjunctionOrdinaryNerve A
  have hu : adj.unit.app X = (ordinaryNerveElementsAdjunction A).unit.app X := by
    rw [← adj.homEquiv_id]
    refine (congrArg ((ordinaryNerveElementsAdjunction A).homEquiv X _)
      (CategoryTheory.nerveFunctor.map_id _)).trans ?_
    exact (ordinaryNerveElementsAdjunction A).homEquiv_id X
  have hn : 𝒲.wPsh A ((nerveAdjunction A).unit.app X) :=
    MorphismProperty.map_unit_app_mem_of_counit (nerveAdjunction A) 𝒲.W hA.counit_mem X
  rw [← Adjunction.unit_rightAdjointUniq_hom_app adj (nerveAdjunction A)] at hn
  rw [← hu]
  exact (𝒲.wPsh A).of_postcomp _ _ (isomorphisms_le_of_containsIdentities (𝒲.wPsh _) _
    (show IsIso ((adj.rightAdjointUniq (nerveAdjunction A)).app ((elementsFunctor A).obj X)).hom
      from inferInstance)) hn

end BasicLocalizer

namespace NerveSlice

open MonoidalCategory

variable {A : Type u} [SmallCategory A] (C' : Cat.{u, u}) (X : Aᵒᵖ ⥤ Type u)

def prodToNerve : (nerveFunctor A).obj C' ⊗ X ⟶ (Over.mapFunctor A).nerve C' where
  app _ := TypeCat.ofHom fun p => nerveElementFunctor C' p.1

def evalTerminal : ((((nerveFunctor A).obj C') ⊗ X).Elements)ᵒᵖ ⥤ C' :=
  (NatTrans.mapElements (prodToNerve C' X)).op ⋙
    (Over.mapFunctor A).nerveEvalTerminal (fun a => Over.mkIdIsTerminal a) C'

variable {C'} (c : C')

variable (C')

def overLiftsIso :
    NatTrans.overLifts (prodToNerve C' X) c ≅ ((nerveFunctor A).obj (Cat.of (Over c))) ⊗ X :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun q := (q.lift.toCatHom, q.elt.2)
      invFun p := ⟨((p.1.toFunctor ⋙ Over.forget c).toCatHom, p.2), p.1.toFunctor, rfl⟩
      left_inv q := NatTrans.OverLift.ext (Prod.ext (Cat.Hom.ext q.w.symm) rfl) rfl
      right_inv _ := rfl }) (fun _ => rfl)

def sliceEquivalence :
    CostructuredArrow (evalTerminal C' X) c ≌
      ((((nerveFunctor A).obj (Cat.of (Over c))) ⊗ X).Elements)ᵒᵖ :=
  (NatTrans.overLiftsEquivalence (prodToNerve C' X) c (fun a => Over.mkIdIsTerminal a)).trans
    (Cat.equivOfIso ((elementsFunctor A).mapIso (overLiftsIso C' X c)))

end NerveSlice

section NerveProduct

open MonoidalCategory NerveSlice

variable {A : Type u} [SmallCategory A] (𝒲 : BasicLocalizer.{u})

namespace BasicLocalizer

theorem wPsh_whiskerLeft_nerveFunctor [𝒲.IsLocalTest A] (C : Cat.{u, u})
    {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hf : 𝒲.wPsh A f) :
    𝒲.wPsh A ((nerveFunctor A).obj C ◁ f) := by
  refine 𝒲.quillenA ((elementsFunctor A).map ((nerveFunctor A).obj C ◁ f))
    (show Cat.of _ ⟶ C from (evalTerminal C Y).toCatHom) (fun c => ?_)
  have : HasTerminal (Cat.of (Over c)) := Over.mkIdTerminal.hasTerminal
  have ht := 𝒲.wPsh_whiskerLeft_of_locallyAspherical A
    (𝒲.locallyAspherical_nerveFunctor_obj_of_isLocalTest A (Cat.of (Over c))) hf
  refine (𝒲.W_iff_of_isEquivalence_of_iso
    (sliceEquivalence C X c).inverse.toCatHom (sliceEquivalence C Y c).inverse.toCatHom
    (sliceEquivalence C X c).isEquivalence_inverse
    (sliceEquivalence C Y c).isEquivalence_inverse _ _ ?_).1 ht
  exact NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    refine CostructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj
      (CategoryOfElements.ext _ _ _ ?_))
    exact (Category.id_comp _).trans (Category.comp_id _).symm)

theorem prod_map_rightAdjoint_nerve_mem [𝒲.IsLocalTest A] (C : Cat.{u, u})
    {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hf : 𝒲.wPsh A f) :
    𝒲.wPsh A (Limits.prod.map f
      (𝟙 ((ordinaryNerveElementsRightAdjoint A).obj (CategoryTheory.nerve C)))) := by
  let Z := (ordinaryNerveElementsRightAdjoint A).obj (CategoryTheory.nerve C)
  let N := (nerveFunctor A).obj C
  let e : Z ≅ N := (ordinaryNerveElementsRightAdjointNerveIso A).app C
  let φ : ∀ V : Aᵒᵖ ⥤ Type u, V ⨯ Z ⟶ N ⊗ V := fun V =>
    CartesianMonoidalCategory.lift (Limits.prod.snd ≫ e.hom) Limits.prod.fst
  have hφ : ∀ V, IsIso (φ V) := fun V =>
    ⟨prod.lift (CartesianMonoidalCategory.snd N V) (CartesianMonoidalCategory.fst N V ≫ e.inv),
      by apply prod.hom_ext <;> simp [φ], by
        apply CartesianMonoidalCategory.hom_ext
        · simp only [φ, Category.assoc, CartesianMonoidalCategory.lift_fst, Category.id_comp]
          rw [prod.lift_snd_assoc, Category.assoc, e.inv_hom_id, Category.comp_id]
        · simp only [φ, Category.assoc, CartesianMonoidalCategory.lift_snd, Category.id_comp]
          rw [prod.lift_fst]⟩
  have sq : Limits.prod.map f (𝟙 Z) ≫ φ Y = φ X ≫ (N ◁ f) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [φ]
  have hX : 𝒲.wPsh A (φ X) := isomorphisms_le_of_containsIdentities (𝒲.wPsh _) _ (hφ X)
  have hY : 𝒲.wPsh A (φ Y) := isomorphisms_le_of_containsIdentities (𝒲.wPsh _) _ (hφ Y)
  refine (𝒲.wPsh A).of_postcomp _ _ hY ?_
  rw [sq]
  exact (𝒲.wPsh A).comp_mem _ _ hX (𝒲.wPsh_whiskerLeft_nerveFunctor C f hf)

end BasicLocalizer

end NerveProduct

namespace BasicLocalizer

theorem prod_map_rightAdjoint_mem (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
    [𝒲.IsLocalTest A]
    {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hf : 𝒲.wPsh A f) (K : SSet.{u}) :
    𝒲.wPsh A (Limits.prod.map f (𝟙 ((ordinaryNerveElementsRightAdjoint A).obj K))) := by
  let R := ordinaryNerveElementsRightAdjoint A
  let r := ordinaryNerveResolution.app K
  have hr := 𝒲.ordinaryNerveResolution_mem K
  have hX := 𝒲.prod_rightAdjoint_map_mem A X r hr
  have hY := 𝒲.prod_rightAdjoint_map_mem A Y r hr
  have ht := 𝒲.prod_map_rightAdjoint_nerve_mem
    ((elementsFunctor (AsSmall.{u} SimplexCategory)).obj (SSet.asSmall.obj K)) f hf
  have sq : Limits.prod.map f (𝟙 _) ≫ Limits.prod.map (𝟙 Y) (R.map r) =
      Limits.prod.map (𝟙 X) (R.map r) ≫ Limits.prod.map f (𝟙 (R.obj K)) := by
    simp
  refine (𝒲.wPsh A).of_precomp _ _ hX ?_
  rw [← sq]
  exact (𝒲.wPsh A).comp_mem _ _ ht hY

end BasicLocalizer

end Atoms.TestCategory
