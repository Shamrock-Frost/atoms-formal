import Atoms.TestCategory.BasicLocalizer.SmoothFunctor
import Atoms.TestCategory.Simplicial.KanBasicLocalizer
import Atoms.Homotopical.Simplicial.KanQuillen

open CategoryTheory Limits Opposite Atoms.Homotopical

namespace Atoms.TestCategory

universe u

section NerveStep

namespace BasicLocalizer

theorem locallyConstant_nerve_forget (𝒲 : BasicLocalizer.{u}) {B : Type u} [SmallCategory B]
    (F : B ⥤ Cat.{u, u}) (hF : 𝒲.CatDiagramLocallyConstant F) :
    LocallyConstant 𝒲.wSSet
      (CategoryTheory.nerveFunctor.map (Grothendieck.forget F).toCatHom) := by
  intro m n g s
  let ιm : uliftYoneda.{u}.obj m ≅
      CategoryTheory.nerveFunctor.obj (Cat.of (ULift.{u} (Fin (m.len + 1)))) :=
    SSet.stdSimplex.isoNerve.{u} m.len
  let ιn : uliftYoneda.{u}.obj n ≅
      CategoryTheory.nerveFunctor.obj (Cat.of (ULift.{u} (Fin (n.len + 1)))) :=
    SSet.stdSimplex.isoNerve.{u} n.len
  let σ := CategoryTheory.nerveFunctor.fullyfaithful.preimage (ιn.inv ≫ s)
  let ĝ := CategoryTheory.nerveFunctor.fullyfaithful.preimage
    (ιm.inv ≫ uliftYoneda.{u}.map g ≫ ιn.hom)
  have hσ : CategoryTheory.nerveFunctor.map σ = ιn.inv ≫ s :=
    CategoryTheory.nerveFunctor.fullyfaithful.map_preimage _
  have hĝ : CategoryTheory.nerveFunctor.map ĝ = ιm.inv ≫ uliftYoneda.{u}.map g ≫ ιn.hom :=
    CategoryTheory.nerveFunctor.fullyfaithful.map_preimage _
  let G := σ.toFunctor ⋙ F
  have hG : 𝒲.W (Grothendieck.pre G ĝ.toFunctor).toCatHom := by
    exact 𝒲.W_grothendieck_pre_of_hasTerminal G (𝒲.catDiagramLocallyConstant_pre F _ hF) _
  rw [W_iff_wSSet_nerveMap] at hG
  have h' : IsPullback (CategoryTheory.nerveFunctor.map (Grothendieck.pre G ĝ.toFunctor).toCatHom)
      (CategoryTheory.nerveFunctor.map (Grothendieck.forget (ĝ.toFunctor ⋙ G)).toCatHom ≫ ιm.inv)
      (CategoryTheory.nerveFunctor.map (Grothendieck.forget G).toCatHom ≫ ιn.inv)
      (uliftYoneda.{u}.map g) :=
    ((Grothendieck.isPullback_pre G ĝ.toFunctor).map CategoryTheory.nerveFunctor).of_iso
      (Iso.refl _) (Iso.refl _) ιm.symm ιn.symm
      ((Category.comp_id _).trans (Category.id_comp _).symm) (by simp) (by simp)
      (show CategoryTheory.nerveFunctor.map ĝ ≫ ιn.inv = ιm.inv ≫ uliftYoneda.{u}.map g by
        rw [hĝ]; simp)
  have he : IsPullback (CategoryTheory.nerveFunctor.map (Grothendieck.forget G).toCatHom ≫ ιn.inv)
      (CategoryTheory.nerveFunctor.map (Grothendieck.pre F σ.toFunctor).toCatHom) s
      (CategoryTheory.nerveFunctor.map (Grothendieck.forget F).toCatHom) :=
    ((Grothendieck.isPullback_pre F σ.toFunctor).map CategoryTheory.nerveFunctor).flip.of_iso
      (Iso.refl _) ιn.symm (Iso.refl _) (Iso.refl _) (Category.id_comp _).symm
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      (show CategoryTheory.nerveFunctor.map σ ≫ 𝟙 _ = ιn.inv ≫ s by rw [hσ]; simp)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  exact (MorphismProperty.mem_iff_of_isPullback _
    (isPullback_baseChangeMap (uliftYoneda.{u}.map g) s _) h' he.isoPullback
    he.isoPullback_hom_fst).1 hG

end BasicLocalizer

end NerveStep

namespace BasicLocalizer

theorem W_grothendieck_pre_of_minimal {B D : Type u} [SmallCategory B] [SmallCategory D]
    (𝒲 : BasicLocalizer.{u}) (F : B ⥤ Cat.{u, u}) (v : D ⥤ B)
    (hF : 𝒲.CatDiagramLocallyConstant F) (hv : minimalBasicLocalizer.{u}.W v.toCatHom) :
    𝒲.W (Grothendieck.pre F v).toCatHom := by
  rw [minimalBasicLocalizer_eq_kanBasicLocalizer] at hv
  have hb := (locallyConstant_iff_kanWeak _).1 (𝒲.locallyConstant_nerve_forget F hF)
    (CategoryTheory.nerveFunctor.map v.toCatHom) (𝟙 _) ((kanBasicLocalizer_W_iff v.toCatHom).1 hv)
  rw [W_iff_wSSet_nerveMap]
  exact (MorphismProperty.mem_iff_of_isPullback _ (isPullback_baseChangeMap _ (𝟙 _) _)
    ((Grothendieck.isPullback_pre F v).map CategoryTheory.nerveFunctor)
    IsPullback.of_id_snd.isoPullback IsPullback.of_id_snd.isoPullback_hom_fst).2 hb

end BasicLocalizer

section ElementsComma

variable (𝒲 : BasicLocalizer.{u})
variable {A : Type u} [SmallCategory A] {E B : Aᵒᵖ ⥤ Type u} (p : E ⟶ B)

abbrev elementsMap : E.Elementsᵒᵖ ⥤ B.Elementsᵒᵖ := ((elementsFunctor A).map p).toFunctor

private theorem elementsComma_w (x : B.Elementsᵒᵖ) (e : E.Elementsᵒᵖ)
    (φ : op ((CategoryOfElements.map p).obj e.unop) ⟶ x) :
    yoneda.map φ.unop.1.unop ≫ (yonedaEquiv.symm x.unop.2 : yoneda.obj x.unop.1.unop ⟶ B) =
      yonedaEquiv.symm e.unop.2 ≫ p := by
  rw [yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_right]
  exact congrArg yonedaEquiv.symm φ.unop.2

theorem elementsComma_hom_comp {x : B.Elementsᵒᵖ} {y₁ y₂ : CostructuredArrow (elementsMap p) x}
    (g : y₁ ⟶ y₂) : g.left.unop.1.unop ≫ y₂.hom.unop.1.unop = y₁.hom.unop.1.unop :=
  congrArg (fun m : op ((CategoryOfElements.map p).obj y₁.left.unop) ⟶ x => m.unop.1.unop)
    (CostructuredArrow.w g)

private theorem comp_pullback_lift_eq {C : Type*} [Category C] {X Y Z T T' : C} {f : X ⟶ Z}
    {g : Y ⟶ Z} [HasPullback f g] (k : T' ⟶ T) {a : T ⟶ X} {b : T ⟶ Y} (w : a ≫ f = b ≫ g)
    {a' : T' ⟶ X} {b' : T' ⟶ Y} (w' : a' ≫ f = b' ≫ g) (ha : k ≫ a = a') (hb : k ≫ b = b') :
    k ≫ pullback.lift a b w = pullback.lift a' b' w' := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ha]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hb]

noncomputable def commaElementsToPullback (x : B.Elementsᵒᵖ) :
    CostructuredArrow (elementsMap p) x ⥤
      CostructuredArrow yoneda
        (pullback (yonedaEquiv.symm x.unop.2 : yoneda.obj x.unop.1.unop ⟶ B) p) where
  obj y := CostructuredArrow.mk (pullback.lift _ _ (elementsComma_w p x y.left y.hom))
  map {y₁ y₂} g := CostructuredArrow.homMk g.left.unop.1.unop
    (comp_pullback_lift_eq _ _ _
      ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map (elementsComma_hom_comp p g)))
      ((yonedaEquiv_symm_naturality_left _ _ _).trans (congrArg yonedaEquiv.symm g.left.unop.2)))

theorem commaElementsToPullback_hom_fst (x : B.Elementsᵒᵖ)
    (y : CostructuredArrow (elementsMap p) x) :
    ((commaElementsToPullback p x).obj y).hom ≫ pullback.fst _ _ = yoneda.map y.hom.unop.1.unop :=
  pullback.lift_fst _ _ _

theorem commaElementsToPullback_hom_snd (x : B.Elementsᵒᵖ)
    (y : CostructuredArrow (elementsMap p) x) :
    ((commaElementsToPullback p x).obj y).hom ≫ pullback.snd _ _ =
      yonedaEquiv.symm y.left.unop.2 :=
  pullback.lift_snd _ _ _

instance (x : B.Elementsᵒᵖ) : (commaElementsToPullback p x).IsEquivalence where
  faithful :=
    { map_injective {y₁ y₂} g₁ g₂ h := by
        have h' : g₁.left.unop.1.unop = g₂.left.unop.1.unop := congrArg CommaMorphism.left h
        apply CostructuredArrow.hom_ext
        apply Quiver.Hom.unop_inj
        apply CategoryOfElements.ext
        exact Quiver.Hom.unop_inj h' }
  full :=
    { map_surjective {y₁ y₂} φ := by
        have hw := CostructuredArrow.w φ
        have h₁ : yoneda.map φ.left ≫ yoneda.map y₂.hom.unop.1.unop =
            yoneda.map y₁.hom.unop.1.unop :=
          (congrArg (yoneda.map φ.left ≫ ·) (commaElementsToPullback_hom_fst p x y₂)).symm.trans
            ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst _ _) hw).trans
              (commaElementsToPullback_hom_fst p x y₁)))
        have h₂ : yonedaEquiv.symm (E.map φ.left.op y₂.left.unop.2) =
            yonedaEquiv.symm y₁.left.unop.2 :=
          (yonedaEquiv_symm_naturality_left _ _ _).symm.trans
            ((congrArg (yoneda.map φ.left ≫ ·) (commaElementsToPullback_hom_snd p x y₂)).symm.trans
              ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.snd _ _) hw).trans
                (commaElementsToPullback_hom_snd p x y₁))))
        refine ⟨CostructuredArrow.homMk
          (CategoryOfElements.homMk y₂.left.unop y₁.left.unop φ.left.op
            (yonedaEquiv.symm.injective h₂)).op ?_, rfl⟩
        apply Quiver.Hom.unop_inj
        apply CategoryOfElements.ext
        apply Quiver.Hom.unop_inj
        exact yoneda.map_injective ((yoneda.map_comp _ _).trans h₁) }
  essSurj :=
    { mem_essImage z := by
        let c := z.left
        have hB : B.map (yoneda.preimage (z.hom ≫ pullback.fst _ _)).op x.unop.2 =
            p.app (op c) (yonedaEquiv (z.hom ≫ pullback.snd _ _)) := by
          apply yonedaEquiv.symm.injective
          rw [← yonedaEquiv_symm_naturality_left, ← yonedaEquiv_symm_naturality_right,
            Equiv.symm_apply_apply, Functor.map_preimage, Category.assoc, Category.assoc,
            pullback.condition]
        let y : CostructuredArrow (elementsMap p) x := CostructuredArrow.mk
          (Y := (op (E.elementsMk (op c) (yonedaEquiv (z.hom ≫ pullback.snd _ _))) :
            E.Elementsᵒᵖ))
          (CategoryOfElements.homMk x.unop _ (yoneda.preimage (z.hom ≫ pullback.fst _ _)).op hB).op
        refine ⟨y, ⟨CostructuredArrow.isoMk (Iso.refl c) ?_⟩⟩
        apply pullback.hom_ext
        · rw [Category.assoc, commaElementsToPullback_hom_fst]
          exact (congrArg (· ≫ _) (yoneda.map_id c)).trans
            ((Category.id_comp _).trans (Functor.map_preimage _ _).symm)
        · rw [Category.assoc, commaElementsToPullback_hom_snd]
          exact (congrArg (· ≫ _) (yoneda.map_id c)).trans
            ((Category.id_comp _).trans (Equiv.symm_apply_apply _ _).symm) }

noncomputable def commaElementsToPullbackMapIso {x₁ x₂ : B.Elementsᵒᵖ} (g : x₁ ⟶ x₂) :
    commaElementsToPullback p x₁ ⋙ CostructuredArrow.map
        (baseChangeLift.{u, u} (yoneda.map g.unop.1.unop) _ p
          (CostructuredArrow.w ((CategoryOfElements.toCostructuredArrow B).map g))) ≅
      CostructuredArrow.map g ⋙ commaElementsToPullback p x₂ :=
  NatIso.ofComponents (fun y => CostructuredArrow.isoMk (Iso.refl _) (by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (commaElementsToPullback_hom_fst p x₂ _)).trans ((congrArg (· ≫ _) (yoneda.map_id _)).trans
          ((Category.id_comp _).trans ((yoneda.map_comp _ _).trans ?_))))
      exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (baseChangeLift_fst.{u, u} (yoneda.map g.unop.1.unop) _ p
          (CostructuredArrow.w ((CategoryOfElements.toCostructuredArrow B).map g)))).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
          (commaElementsToPullback_hom_fst p x₁ y))))).symm
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (commaElementsToPullback_hom_snd p x₂ _)).trans ((congrArg (· ≫ _) (yoneda.map_id _)).trans
          ((Category.id_comp _).trans ?_)))
      exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (baseChangeLift_snd.{u, u} (yoneda.map g.unop.1.unop) _ p
          (CostructuredArrow.w ((CategoryOfElements.toCostructuredArrow B).map g)))).trans
        (commaElementsToPullback_hom_snd p x₁ y))).symm)) (by
    intros
    ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

namespace BasicLocalizer

theorem W_costructuredArrow_map_elements_iff {x₁ x₂ : B.Elementsᵒᵖ} (g : x₁ ⟶ x₂) :
    𝒲.W (CostructuredArrow.map (S := elementsMap p) g).toCatHom ↔
      𝒲.wPsh A (baseChangeMap.{u, u} (yoneda.map g.unop.1.unop)
        (yonedaEquiv.symm x₂.unop.2 : yoneda.obj x₂.unop.1.unop ⟶ B) p) := by
  refine (𝒲.W_iff_of_isEquivalence_of_iso (commaElementsToPullback p x₁).toCatHom
    (commaElementsToPullback p x₂).toCatHom
    (inferInstanceAs (commaElementsToPullback p x₁).IsEquivalence)
    (inferInstanceAs (commaElementsToPullback p x₂).IsEquivalence)
    (CostructuredArrow.map (S := elementsMap p) g).toCatHom
    (CostructuredArrow.map (S := yoneda)
      (baseChangeLift.{u, u} (yoneda.map g.unop.1.unop) _ p
        (CostructuredArrow.w ((CategoryOfElements.toCostructuredArrow B).map g)))).toCatHom
    (commaElementsToPullbackMapIso p g)).trans ((𝒲.W_elementsFunctor_map_iff _).symm.trans ?_)
  exact MorphismProperty.mem_iff_of_isPullback (𝒲.wPsh A) (isPullback_baseChangeMap _ _ p)
    (isPullback_baseChangeLift _ _ p _) (Iso.refl _) (Category.id_comp _)

end BasicLocalizer

end ElementsComma

namespace BasicLocalizer

theorem locallyConstant_iff_elements {A : Type u} [SmallCategory A]
    (𝒲 : BasicLocalizer.{u}) {E B : Aᵒᵖ ⥤ Type u} (p : E ⟶ B) :
    LocallyConstant (𝒲.wPsh A) p ↔
      𝒲.CommaLocallyConstant ((elementsFunctor A).map p).toFunctor := by
  rw [locallyConstant_iff_yoneda]
  constructor
  · intro h x₁ x₂ g
    exact (𝒲.W_costructuredArrow_map_elements_iff p g).2 (h _ _ _ _)
  · intro h a a' f b
    obtain ⟨β, rfl⟩ := yonedaEquiv.symm.surjective b
    let x₂ : B.Elementsᵒᵖ := op (B.elementsMk (op a') β)
    let x₁ : B.Elementsᵒᵖ := op (B.elementsMk (op a) (B.map f.op β))
    let g : x₁ ⟶ x₂ := (CategoryOfElements.homMk x₂.unop x₁.unop f.op rfl).op
    exact (𝒲.W_costructuredArrow_map_elements_iff p g).1 (h g)

theorem W_grothendieckProj (𝒲 : BasicLocalizer.{u}) {A B : Cat.{u, u}} (u : A ⟶ B) :
    𝒲.W (CostructuredArrow.grothendieckProj u.toFunctor).toCatHom := by
  have : (CostructuredArrow.grothendieckPrecompFunctorToComma u.toFunctor
      (𝟭 B)).toCatHom.toFunctor.IsEquivalence :=
    (CostructuredArrow.grothendieckPrecompFunctorEquivalence u.toFunctor
      (𝟭 B)).isEquivalence_functor
  exact 𝒲.W.comp_mem
    (CostructuredArrow.grothendieckPrecompFunctorToComma u.toFunctor (𝟭 B)).toCatHom
    (Comma.fst u.toFunctor (𝟭 B)).toCatHom (𝒲.W_of_isEquivalence _)
    (𝒲.W_of_adjunction_right (u := (Comma.idSection u.toFunctor).toCatHom)
      (v := (Comma.fst u.toFunctor (𝟭 B)).toCatHom) (Cat.idSectionAdjunction u))

end BasicLocalizer

section MixedSquare

variable {A' A B' B : Cat.{u, u}}

private def commaSquareProjHom (w : A' ⟶ A) (u' : A' ⟶ B') (u : A ⟶ B) (v : B' ⟶ B)
    (hw : w ≫ u = u' ≫ v) :
    CostructuredArrow.grothendieckProj u'.toFunctor ⋙ w.toFunctor ⟶
      Grothendieck.map (Cat.commaSquareNatTrans w u' u v hw) ⋙
        Grothendieck.pre (CostructuredArrow.functor u.toFunctor) v.toFunctor ⋙
          CostructuredArrow.grothendieckProj u.toFunctor where
  app X := 𝟙 _
  naturality X Y m := by
    erw [Category.comp_id, Category.id_comp]
    simp only [Functor.comp_obj, Functor.comp_map, CostructuredArrow.grothendieckProj_map,
      Grothendieck.pre_map_fiber, Grothendieck.map_map_fiber, Cat.commaSquareNatTrans,
      Cat.commaSquareFunctor, Functor.toCatHom_toFunctor]
    erw [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
    exact (Category.id_comp _).symm

end MixedSquare

namespace BasicLocalizer

theorem W_of_isPullback_of_smooth_of_minimal {A' A B' B : Cat.{u, u}}
    (𝒲 : BasicLocalizer.{u}) (w : A' ⟶ A) (u' : A' ⟶ B')
    (u : A ⟶ B) (v : B' ⟶ B) (h : IsPullback w u' u v)
    (hu : 𝒲.CommaLocallyConstant u.toFunctor) (hs : 𝒲.SmoothFor v)
    (hv : minimalBasicLocalizer.{u}.W v) : 𝒲.W w := by
  have hπ' := 𝒲.W_grothendieckProj u'
  have hπ := 𝒲.W_grothendieckProj u
  have hpre := 𝒲.W_grothendieck_pre_of_minimal (CostructuredArrow.functor u.toFunctor)
    v.toFunctor hu hv
  have hmap := 𝒲.W_grothendieckMap (Cat.commaSquareNatTrans w u' u v h.w)
    (fun b => 𝒲.W_commaSquareFunctor_of_smooth w u' u v h hs b)
  have hΦ := 𝒲.W.comp_mem _ _ hmap (𝒲.W.comp_mem _ _ hpre hπ)
  have hΨ := (𝒲.W_iff_of_natTrans (commaSquareProjHom w u' u v h.w)).2 hΦ
  exact 𝒲.W.of_precomp _ _ hπ' hΨ

theorem wPsh_baseChangeMap_of_locallyConstant (𝒲 : BasicLocalizer.{u}) (A : Type u)
    [SmallCategory A] {E B : Aᵒᵖ ⥤ Type u} (p : E ⟶ B) (hp : LocallyConstant (𝒲.wPsh A) p)
    {K L : Aᵒᵖ ⥤ Type u} (f : K ⟶ L) (b : L ⟶ B)
    (hf : minimalBasicLocalizer.{u}.wPsh A f) : 𝒲.wPsh A (baseChangeMap f b p) := by
  have hL : 𝒲.CommaLocallyConstant ((elementsFunctor A).map (pullback.fst b p)).toFunctor :=
    𝒲.commaLocallyConstant_baseChange _ _ _ _
      (elements_isPullback _ _ _ _ (IsPullback.of_hasPullback b p).flip)
      (𝒲.smoothFor_elements_map b) ((𝒲.locallyConstant_iff_elements p).1 hp)
  exact 𝒲.W_of_isPullback_of_smooth_of_minimal _ _ _ _
    (elements_isPullback _ _ _ _ (isPullback_baseChangeMap f b p)) hL
    (𝒲.smoothFor_elements_map f) hf

end BasicLocalizer

theorem weakFibration_of_locallyConstant (A : Type u) [SmallCategory A]
    {E B : Aᵒᵖ ⥤ Type u} (p : E ⟶ B)
    (hp : LocallyConstant (minimalBasicLocalizer.{u}.wPsh A) p) :
    WeakFibration (minimalBasicLocalizer.{u}.wPsh A) p :=
  fun f b hf => BasicLocalizer.wPsh_baseChangeMap_of_locallyConstant _ A p hp f b hf

namespace BasicLocalizer

theorem locallyConstant_of_weakFibration (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
    {E B : Aᵒᵖ ⥤ Type u} (p : E ⟶ B) (hp : WeakFibration (𝒲.wPsh A) p) :
    LocallyConstant (𝒲.wPsh A) p :=
  (locallyConstant_iff_yoneda p).2 fun _ _ f b => hp (yoneda.map f) b (𝒲.wPsh_yoneda_map A f)

end BasicLocalizer

theorem minimal_weakFibration_iff_locallyConstant (A : Type u) [SmallCategory A]
    {E B : Aᵒᵖ ⥤ Type u} (p : E ⟶ B) :
    WeakFibration (minimalBasicLocalizer.{u}.wPsh A) p ↔
      LocallyConstant (minimalBasicLocalizer.{u}.wPsh A) p :=
  ⟨BasicLocalizer.locallyConstant_of_weakFibration _ A p, weakFibration_of_locallyConstant A p⟩

theorem weakFibration_pullback_fst {A : Type u} [SmallCategory A]
    (V : MorphismProperty (Aᵒᵖ ⥤ Type u)) [V.RespectsIso] {E B K : Aᵒᵖ ⥤ Type u}
    (p : E ⟶ B) (b : K ⟶ B) (hp : WeakFibration V p) : WeakFibration V (pullback.fst b p) :=
  fun f c hf => (V.mem_iff_of_isPullback (isPullback_baseChangeMap f (c ≫ b) p)
    (isPullback_baseChangeMap f c (pullback.fst b p)) (pullbackRightPullbackFstIso b p c)
    (pullbackRightPullbackFstIso_hom_fst b p c)).2 (hp f (c ≫ b) hf)

theorem locallyConstant_minimal_pullback (A : Type u) [SmallCategory A]
    {E B K : Aᵒᵖ ⥤ Type u} (p : E ⟶ B) (b : K ⟶ B)
    (hp : LocallyConstant (minimalBasicLocalizer.{u}.wPsh A) p) :
    LocallyConstant (minimalBasicLocalizer.{u}.wPsh A) (pullback.fst b p) := by
  exact BasicLocalizer.locallyConstant_of_weakFibration _ A _
    (weakFibration_pullback_fst _ p b (weakFibration_of_locallyConstant A p hp))

theorem sliceForget_map_baseChangeMap_sliceHom_mem_iff {A : Type u} [SmallCategory A]
    (V : MorphismProperty (Aᵒᵖ ⥤ Type u)) [V.RespectsIso] {K Y E B : Aᵒᵖ ⥤ Type u}
    (g : K ⟶ Y) (b : Y ⟶ B) (p : E ⟶ B) :
    V ((sliceForget Y).map (baseChangeMap (sliceHom g (𝟙 Y)) (𝟙 _)
        (sliceHom (pullback.fst b p) (𝟙 Y)))) ↔ V (baseChangeMap g b p) := by
  let j := sliceHom g (𝟙 Y)
  let s := sliceHom (pullback.fst b p) (𝟙 Y)
  let eg := sliceForgetMapSliceHomIso g (𝟙 Y)
  let ep := sliceForgetMapSliceHomIso (pullback.fst b p) (𝟙 Y)
  have h1 := (isPullback_sliceForget_map_iff (X := Y)).2 (isPullback_baseChangeMap j (𝟙 _) s)
  have h2 : IsPullback ((sliceForget Y).map j) eg.hom.left eg.hom.right g :=
    IsPullback.of_vert_isIso ⟨eg.hom.w.symm⟩
  let e0 := asIso (pullback.snd (𝟙 _) s)
  let e : (sliceForget Y).obj (pullback (𝟙 _) s) ≅ pullback b p :=
    (sliceForget Y).mapIso e0 ≪≫ Arrow.leftFunc.mapIso ep
  refine V.mem_iff_of_isPullback (isPullback_baseChangeMap g b p) (h1.paste_vert h2) e ?_
  have hw := ep.hom.w
  simp only [Arrow.mk_hom] at hw
  change (sliceForget Y).map e0.hom ≫ ep.hom.left ≫ pullback.fst b p = _
  rw [hw, ← Functor.map_comp_assoc, asIso_hom, ← pullback.condition]
  exact congrArg (· ≫ eg.hom.right) (congrArg (sliceForget Y).map (Category.comp_id _))

end Atoms.TestCategory
