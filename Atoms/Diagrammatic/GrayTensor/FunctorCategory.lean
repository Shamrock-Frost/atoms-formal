import Atoms.Diagrammatic.InftyCategory
import Atoms.Diagrammatic.Marked.GrayTensorClosed

open CategoryTheory Limits Opposite Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

noncomputable def functorCategory (pseudo : Bool) (X Y : DiagSet.{u}) : DiagSet.{u} :=
  MarkedPresheaf.forget.obj
    ((homFor (tensorRight pseudo ((MarkedPresheaf.flat atomMarking).obj X))
      (coversEpi_tensorRight pseudo _)).obj (MarkedDiagSet.natural.obj Y))

def functorCategoryCellEquiv (pseudo : Bool) (X Y : DiagSet.{u}) (U : Atom) :
    diagram (functorCategory pseudo X Y) U ≃
      ((tensorRight pseudo ((MarkedPresheaf.flat atomMarking).obj X)).obj
          ((MarkedPresheaf.yoneda atomMarking).obj ((MarkedSite.unmarked atomMarking).obj U)) ⟶
        MarkedDiagSet.natural.obj Y) :=
  Equiv.refl _

private noncomputable def cellMap (pseudo : Bool) (X Y : DiagSet.{u}) (U : Atom)
    (g : diagram (functorCategory pseudo X Y) U) : grayTensor (ball.{u} U) X ⟶ Y :=
  MarkedPresheaf.forget.map ((tensorRight pseudo ((MarkedPresheaf.flat atomMarking).obj X)).map
    ((MarkedPresheaf.yonedaCompFlatIso atomMarking).hom.app U) ≫
      functorCategoryCellEquiv pseudo X Y U g)

noncomputable def functorCategoryToGrayHom (pseudo : Bool) (X Y : DiagSet.{u}) :
    functorCategory pseudo X Y ⟶ (grayHomRight X).obj Y where
  app U := ↾fun g => (grayHomRightCellEquiv X Y U.unop).symm (cellMap pseudo X Y U.unop g)
  naturality U V k := by
    refine ConcreteCategory.hom_ext _ _ fun g => ?_
    refine congrArg ULift.up ?_
    have e1 : cellMap pseudo X Y V.unop ((functorCategory pseudo X Y).map k g) =
        MarkedPresheaf.forget.map
          ((tensorRight pseudo ((MarkedPresheaf.flat atomMarking).obj X)).map
            ((MarkedPresheaf.yonedaCompFlatIso atomMarking).hom.app V.unop) ≫
          (tensorRight pseudo ((MarkedPresheaf.flat atomMarking).obj X)).map
            ((MarkedPresheaf.yoneda atomMarking).map
              ((MarkedSite.unmarked atomMarking).map k.unop)) ≫
          functorCategoryCellEquiv pseudo X Y U.unop g) := rfl
    have hk := (MarkedPresheaf.yonedaCompFlatIso.{u} atomMarking).hom.naturality k.unop
    have h := congrArg (fun m => MarkedPresheaf.forget.map
      ((tensorRight pseudo ((MarkedPresheaf.flat atomMarking).obj X)).map m ≫
        functorCategoryCellEquiv pseudo X Y U.unop g)) hk
    simp only [Functor.map_comp, Category.assoc, Functor.comp_map] at h
    refine e1.trans (((MarkedPresheaf.forget.map_comp _ _).trans (congrArg (_ ≫ ·)
      (MarkedPresheaf.forget.map_comp _ _))).trans (h.symm.trans ?_))
    exact congrArg (_ ≫ ·) (MarkedPresheaf.forget.map_comp _ _).symm

private theorem functorCategoryToGrayHom_app (pseudo : Bool) (X Y : DiagSet.{u}) (U : Atom)
    (g : diagram (functorCategory pseudo X Y) U) :
    (functorCategoryToGrayHom pseudo X Y).app (op U) g =
      (grayHomRightCellEquiv X Y U).symm (cellMap pseudo X Y U g) :=
  rfl

private theorem cellMap_injective (pseudo : Bool) (X Y : DiagSet.{u}) (U : Atom) :
    Function.Injective (cellMap pseudo X Y U) := fun _ _ h =>
  (functorCategoryCellEquiv pseudo X Y U).injective ((cancel_epi _).1
    (MarkedPresheaf.forget.map_injective h))

instance mono_functorCategoryToGrayHom (pseudo : Bool) (X Y : DiagSet.{u}) :
    Mono (functorCategoryToGrayHom pseudo X Y) :=
  have (U : Atomᵒᵖ) : Mono ((functorCategoryToGrayHom pseudo X Y).app U) :=
    (mono_iff_injective _).2 fun _ _ h =>
      cellMap_injective pseudo X Y U.unop ((grayHomRightCellEquiv X Y U.unop).symm.injective h)
  NatTrans.mono_of_mono_app _

private theorem exists_cellMap_eq_iff (pseudo : Bool) (X Y : DiagSet.{u}) (U : Atom)
    (F : grayTensor (ball.{u} U) X ⟶ Y) :
    (∃ g, cellMap pseudo X Y U g = F) ↔ ∀ (T : Atom) (z : diagram (grayTensor (ball U) X) T),
      tensorMarked pseudo ((MarkedPresheaf.flat atomMarking).obj (ball U))
        ((MarkedPresheaf.flat atomMarking).obj X) T z → IsEquivalence Y (F.app (op T) z) := by
  constructor
  · rintro ⟨g, rfl⟩ T z hz
    have hm := MarkedPresheaf.map_mem_marked
      ((tensorRight pseudo ((MarkedPresheaf.flat atomMarking).obj X)).map
          ((MarkedPresheaf.yonedaCompFlatIso atomMarking).hom.app U) ≫
        functorCategoryCellEquiv pseudo X Y U g)
      ((mem_marked_markedTensor pseudo ((MarkedPresheaf.flat atomMarking).obj (ball U))
        ((MarkedPresheaf.flat atomMarking).obj X) T z).2 hz)
    exact (MarkedDiagSet.mem_marked_natural_iff Y T _).1 hm
  · intro hF
    let F' : (tensorRight pseudo ((MarkedPresheaf.flat atomMarking).obj X)).obj
        ((uliftYoneda.{u} ⋙ MarkedPresheaf.flat atomMarking).obj U) ⟶
          MarkedDiagSet.natural.obj Y :=
      MarkedPresheaf.homMk F fun T z hz => (MarkedDiagSet.mem_marked_natural_iff Y T _).2
        (hF T z ((mem_marked_markedTensor pseudo ((MarkedPresheaf.flat atomMarking).obj (ball U))
          ((MarkedPresheaf.flat atomMarking).obj X) T z).1 hz))
    refine ⟨(functorCategoryCellEquiv pseudo X Y U).symm
      ((tensorRight pseudo ((MarkedPresheaf.flat atomMarking).obj X)).map
        ((MarkedPresheaf.yonedaCompFlatIso atomMarking).inv.app U) ≫ F'), ?_⟩
    refine Eq.trans ?_ (rfl : MarkedPresheaf.forget.map F' = F)
    rw [cellMap, Equiv.apply_symm_apply, ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]

instance isIso_functorCategoryToGrayHom_false (X Y : DiagSet.{u}) :
    IsIso (functorCategoryToGrayHom false X Y) :=
  have (U : Atomᵒᵖ) : IsIso ((functorCategoryToGrayHom false X Y).app U) :=
    (isIso_iff_bijective _).2 ⟨(mono_iff_injective _).1 inferInstance, fun F => by
      obtain ⟨g, hg⟩ := (exists_cellMap_eq_iff false X Y U.unop
        (grayHomRightCellEquiv X Y U.unop F)).2 fun T z hz => degenerate_isEquivalence Y _
          (isDegenerate_app _ ((tensorMarked_flat_iff _ X T z).1 hz))
      exact ⟨g, (functorCategoryToGrayHom_app false X Y U.unop g).trans
        ((congrArg _ hg).trans ((grayHomRightCellEquiv X Y U.unop).symm_apply_apply F))⟩⟩
  NatIso.isIso_of_isIso_app _

noncomputable def functorCategoryGrayIso (X Y : DiagSet.{u}) :
    functorCategory false X Y ≅ (grayHomRight X).obj Y :=
  asIso (functorCategoryToGrayHom false X Y)

private theorem functorCategoryToGrayHom_app_homEquiv {A T Y : DiagSet.{u}}
    (g : (tensorRight false ((MarkedPresheaf.flat atomMarking).obj A)).obj
      ((MarkedPresheaf.flat atomMarking).obj T) ⟶ MarkedDiagSet.natural.obj Y)
    (U : Atom) (t : T.obj (op U)) :
    (functorCategoryToGrayHom false A Y).app (op U) ((MarkedPresheaf.forget.map
        ((tensorRightAdjunction false ((MarkedPresheaf.flat atomMarking).obj A)).homEquiv _ _
          g)).app (op U) t) =
      ((grayTensorRightAdjunction A).homEquiv T Y (MarkedPresheaf.forget.map g)).app (op U) t := by
  refine Eq.trans ?_ (Presheaf.uliftYonedaAdjunction_homEquiv_app (grayTensorRight A) (𝟙 _)
    (MarkedPresheaf.forget.map g) (Z := op U) t).symm
  refine congrArg ULift.up ?_
  have hc := MarkedPresheaf.homEquiv_adjunctionOfPreservesColimits_app _
    (coversEpi_tensorRight false _) g
    ((MarkedSite.unmarked atomMarking).obj U) t
  have hy : (MarkedPresheaf.yonedaCompFlatIso atomMarking).hom.app U ≫
      (ObjectProperty.homMk (uliftYonedaEquiv.symm t) :
        (MarkedPresheaf.yoneda atomMarking).obj ((MarkedSite.unmarked atomMarking).obj U) ⟶
          (MarkedPresheaf.flat atomMarking).obj T) =
      (MarkedPresheaf.flat atomMarking).map (uliftYonedaEquiv.symm t) :=
    MarkedPresheaf.hom_ext rfl
  have e1 := congrArg (fun c => MarkedPresheaf.forget.map
    ((tensorRight false ((MarkedPresheaf.flat atomMarking).obj A)).map
      ((MarkedPresheaf.yonedaCompFlatIso atomMarking).hom.app U) ≫ c)) hc
  refine e1.trans ?_
  rw [← Category.assoc, ← Functor.map_comp, hy, MarkedPresheaf.forget.map_comp, NatTrans.id_app,
    Category.id_comp]
  rfl

theorem homEquiv_functorCategoryToGrayHom {A T Y : DiagSet.{u}}
    (g : markedGrayTensor ((MarkedPresheaf.flat atomMarking).obj T)
      ((MarkedPresheaf.flat atomMarking).obj A) ⟶ MarkedDiagSet.natural.obj Y) :
    MarkedPresheaf.forget.map
        ((tensorRightAdjunction false ((MarkedPresheaf.flat atomMarking).obj A)).homEquiv _ _ g) ≫
        functorCategoryToGrayHom false A Y =
      (grayTensorRightAdjunction A).homEquiv T Y (MarkedPresheaf.forget.map g) :=
  NatTrans.ext (funext fun U => ConcreteCategory.hom_ext _ _ fun t =>
    functorCategoryToGrayHom_app_homEquiv g U.unop t)

private theorem forall_tensorMarked_true_iff (X Y : DiagSet.{u}) (U : Atom)
    (F : grayTensor (ball.{u} U) X ⟶ Y) :
    (∀ (T : Atom) (z : diagram (grayTensor (ball U) X) T),
      tensorMarked true ((MarkedPresheaf.flat atomMarking).obj (ball U))
        ((MarkedPresheaf.flat atomMarking).obj X) T z → IsEquivalence Y (F.app (op T) z)) ↔
      ∀ (P Q : Atom) (a : diagram (ball.{u} U) P) (b : diagram X Q), 0 < P.dimension →
        0 < Q.dimension →
          IsEquivalence Y (F.app (op (Atom.grayTensor P Q)) (grayTensorCell a b)) := by
  constructor
  · intro hF P Q a b hP hQ
    refine hF _ _ (Or.inr ⟨P, Q, a, b, Iso.refl _, Or.inr (Or.inr ⟨rfl, hP, hQ⟩), ?_⟩)
    exact (Functor.map_id_apply (grayTensor (ball U) X) (op (Atom.grayTensor P Q)) _).symm
  · rintro hF T z (hz | ⟨P, Q, a, b, e, hm, hz⟩)
    · exact degenerate_isEquivalence Y _
        (isDegenerate_app (X := grayTensor (ball.{u} U) X) (U := T) F hz)
    · have hz' : z = (grayTensor (ball.{u} U) X).map e.hom.op
          (grayTensorCell (X := ball.{u} U) (Y := X) a b) := hz
      rw [hz', NatTrans.naturality_apply F e.hom.op, isEquivalence_map_iso_iff e]
      rcases hm with ha | hb | ⟨-, hP, hQ⟩
      · exact degenerate_isEquivalence Y _ (isDegenerate_app (X := grayTensor (ball.{u} U) X) F
          (isDegenerate_grayTensorCell (X := ball.{u} U) (Y := X)
            (Or.inl ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate (ball.{u} U) P a).1 ha))))
      · exact degenerate_isEquivalence Y _ (isDegenerate_app (X := grayTensor (ball.{u} U) X) F
          (isDegenerate_grayTensorCell (X := ball.{u} U) (Y := X)
            (Or.inr ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate X Q b).1 hb))))
      · exact hF P Q a b hP hQ

theorem mem_range_functorCategoryToGrayHom_true_iff (X Y : DiagSet.{u}) (U : Atom)
    (F : grayTensor (ball.{u} U) X ⟶ Y) :
    (grayHomRightCellEquiv X Y U).symm F ∈
        Set.range ((functorCategoryToGrayHom true X Y).app (op U)) ↔
      ∀ (P Q : Atom) (a : diagram (ball.{u} U) P) (b : diagram X Q), 0 < P.dimension →
        0 < Q.dimension →
          IsEquivalence Y (F.app (op (Atom.grayTensor P Q)) (grayTensorCell a b)) :=
  (exists_congr fun g => (functorCategoryToGrayHom_app true X Y U g).symm ▸
    (grayHomRightCellEquiv X Y U).symm.injective.eq_iff).trans
    ((exists_cellMap_eq_iff true X Y U F).trans (forall_tensorMarked_true_iff X Y U F))

noncomputable def functorCategoryPseudoToGray (X Y : DiagSet.{u}) :
    functorCategory true X Y ⟶ functorCategory false X Y where
  app U := ↾fun g => (functorCategoryCellEquiv false X Y U.unop).symm
    (grayToPseudo _ _ ≫ functorCategoryCellEquiv true X Y U.unop g)
  naturality U V k := by
    ext g
    exact (grayToPseudo_naturality_assoc _ (𝟙 _) _).symm

@[reassoc] theorem functorCategoryPseudoToGray_comp_functorCategoryToGrayHom (X Y : DiagSet.{u}) :
    functorCategoryPseudoToGray X Y ≫ functorCategoryToGrayHom false X Y =
      functorCategoryToGrayHom true X Y := by
  refine NatTrans.ext (funext fun U => ConcreteCategory.hom_ext _ _ fun g => ?_)
  refine congrArg ULift.up ?_
  have e1 : cellMap false X Y U.unop ((functorCategoryPseudoToGray X Y).app U g) =
      MarkedPresheaf.forget.map ((markedTensorMap false
        ((MarkedPresheaf.yonedaCompFlatIso atomMarking).hom.app U.unop)
        (𝟙 ((MarkedPresheaf.flat atomMarking).obj X)) ≫ grayToPseudo _ _) ≫
          functorCategoryCellEquiv true X Y U.unop g) := rfl
  refine e1.trans ?_
  rw [grayToPseudo_naturality]
  exact (congrArg MarkedPresheaf.forget.map (Category.assoc _ _ _)).trans
    ((MarkedPresheaf.forget.map_comp _ _).trans ((congrArg (· ≫ _)
      (forget_map_grayToPseudo _ _)).trans (Category.id_comp _)))

theorem isIso_functorCategoryPseudoToGray (A : DiagSet.{u}) {Y : DiagSet.{u}}
    (hY : IsInftyCategory 1 Y) : IsIso (functorCategoryPseudoToGray A Y) := by
  have (U : Atomᵒᵖ) : IsIso ((functorCategoryToGrayHom true A Y).app U) :=
    (isIso_iff_bijective _).2 ⟨(mono_iff_injective _).1 inferInstance, fun F => by
      have h := (mem_range_functorCategoryToGrayHom_true_iff A Y U.unop
        (grayHomRightCellEquiv A Y U.unop F)).2 fun P Q a b hP hQ => hY.2 _ _ (by
          rw [Atom.dimension_grayTensor]
          exact_mod_cast (by omega : 1 < P.dimension + Q.dimension))
      rwa [Equiv.symm_apply_apply] at h⟩
  have : IsIso (functorCategoryToGrayHom true A Y) := NatIso.isIso_of_isIso_app _
  have : IsIso (functorCategoryPseudoToGray A Y ≫ functorCategoryToGrayHom false A Y) := by
    rw [functorCategoryPseudoToGray_comp_functorCategoryToGrayHom]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (functorCategoryToGrayHom false A Y)

end Atoms.Diagrammatic
