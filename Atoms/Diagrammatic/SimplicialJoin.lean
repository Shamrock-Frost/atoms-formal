import Atoms.Diagrammatic.Slice
import Atoms.Diagrammatic.SimplicialAdjunction
import Atoms.Shape.SimplexJoin
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.JoinSlice
import Mathlib.CategoryTheory.Adjunction.Unique

open CategoryTheory CategoryTheory.WithInitial Limits Opposite Simplicial Atoms.Shape

universe u

namespace Atoms.Diagrammatic

private instance preservesColimitsOfSize_toDiagSet :
    PreservesColimitsOfSize.{0, u} SSet.toDiagSet.{u} :=
  sSetDiagSetAdj.leftAdjoint_preservesColimits

private noncomputable def sSetIsoOfPreservesColimits {E : Type (u + 1)} [Category.{u} E]
    (F G : SSet.{u} ⥤ E) [PreservesColimitsOfSize.{0, u} F] [PreservesColimitsOfSize.{0, u} G]
    (e : uliftYoneda.{u} ⋙ F ≅ uliftYoneda.{u} ⋙ G) : F ≅ G :=
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} F (Iso.refl _)
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} G (Iso.refl _)
  Functor.leftKanExtensionUniqueOfIso F (Iso.refl _).hom e G (Iso.refl _).hom

private theorem sSetIsoOfPreservesColimits_hom_app {E : Type (u + 1)} [Category.{u} E]
    (F G : SSet.{u} ⥤ E) [PreservesColimitsOfSize.{0, u} F] [PreservesColimitsOfSize.{0, u} G]
    (e : uliftYoneda.{u} ⋙ F ≅ uliftYoneda.{u} ⋙ G) (n : SimplexCategory) :
    (sSetIsoOfPreservesColimits F G e).hom.app (uliftYoneda.obj n) = e.hom.app n := by
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} F (Iso.refl _)
  have h := F.descOfIsLeftKanExtension_fac_app (Iso.refl _).hom G (e.hom ≫ (Iso.refl _).hom) n
  refine Eq.trans ?_ (h.trans (by simp))
  simp [sSetIsoOfPreservesColimits]

private theorem toDiagSet_ext {G : SSet.{u} ⥤ DiagSet.{u}}
    {α β : ∀ K, SSet.toDiagSet.obj K ⟶ G.obj K}
    (hα : ∀ {K K'} (f : K ⟶ K'), SSet.toDiagSet.map f ≫ α K' = α K ≫ G.map f)
    (hβ : ∀ {K K'} (f : K ⟶ K'), SSet.toDiagSet.map f ≫ β K' = β K ≫ G.map f)
    (h : ∀ m : ℕ, α Δ[m] = β Δ[m]) (K : SSet.{u}) : α K = β K := by
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1}
    SSet.toDiagSet.{u} (Iso.refl _)
  have key := SSet.toDiagSet.hom_ext_of_isLeftKanExtension
    (Iso.refl (uliftYoneda.{u} ⋙ SSet.toDiagSet.{u})).hom
    (⟨α, fun _ _ f ↦ hα f⟩ : SSet.toDiagSet ⟶ G) ⟨β, fun _ _ f ↦ hβ f⟩
    (NatTrans.ext (funext fun n ↦ by
      simp only [Iso.refl_hom, Functor.whiskerLeft_app, Category.id_comp]
      exact h n.len))
  exact congr_app key K

private theorem under_ext {X : DiagSet.{u}} (F : SSet.{u} ⥤ Under X)
    [PreservesColimitsOfSize.{0, u} F] {G : SSet.{u} ⥤ DiagSet.{u}}
    {α β : ∀ K, (F.obj K).right ⟶ G.obj K}
    (hα : ∀ {K K'} (f : K ⟶ K'), (F.map f).right ≫ α K' = α K ≫ G.map f)
    (hβ : ∀ {K K'} (f : K ⟶ K'), (F.map f).right ≫ β K' = β K ≫ G.map f)
    (hX : ∀ K, (F.obj K).hom ≫ α K = (F.obj K).hom ≫ β K)
    (h : ∀ m : ℕ, α Δ[m] = β Δ[m]) (K : SSet.{u}) : α K = β K := by
  let G' : SSet.{u} ⥤ Under X :=
    { obj K := Under.mk ((F.obj K).hom ≫ α K)
      map {K K'} f := Under.homMk (G.map f) ((Category.assoc _ _ _).trans
        ((congrArg _ (hα f).symm).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ α K') (Under.w (F.map f))))))
      map_id K := Under.UnderMorphism.ext (G.map_id K)
      map_comp f g := Under.UnderMorphism.ext (G.map_comp f g) }
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} F (Iso.refl _)
  let α' : F ⟶ G' :=
    { app K := Under.homMk (α K) rfl
      naturality _ _ f := Under.UnderMorphism.ext (hα f) }
  let β' : F ⟶ G' :=
    { app K := Under.homMk (β K) (hX K).symm
      naturality _ _ f := Under.UnderMorphism.ext (hβ f) }
  have key := F.hom_ext_of_isLeftKanExtension (Iso.refl (uliftYoneda.{u} ⋙ F)).hom α' β'
    (NatTrans.ext (funext fun n ↦ Under.UnderMorphism.ext (by
      simp only [Iso.refl_hom, Functor.whiskerLeft_app, Category.id_comp]
      exact h n.len)))
  exact congrArg CommaMorphism.right (congr_app key K)

private theorem comp_comp_eq_of_eq {C : Type*} [Category* C] {X Y Y' Z W : C} {a : X ⟶ Y}
    {b : Y ⟶ Z} {c : X ⟶ Y'} {d : Y' ⟶ Z} (h : a ≫ b = c ≫ d) (k : Z ⟶ W) :
    a ≫ b ≫ k = c ≫ d ≫ k := by
  rw [← Category.assoc, h, Category.assoc]

private noncomputable def stdSimplexIso (m n : ℕ) :
    SSet.toDiagSet.obj (SSet.join Δ[m] Δ[n]) ≅
      WithInitial.join (SSet.toDiagSet.obj Δ[m]) (SSet.toDiagSet.obj Δ[n]) :=
  SSet.toDiagSet.mapIso (SSet.stdSimplexJoinIso m n) ≪≫ toDiagSetObjStdSimplexIso.{u} (m + n + 1) ≪≫
    uliftYoneda.mapIso (atomSimplexJoinIso m n).symm ≪≫ (joinBallIso _ _).symm ≪≫
      joinMapIso (toDiagSetObjStdSimplexIso m).symm (toDiagSetObjStdSimplexIso n).symm

private theorem toDiagSet_map_stdSimplex_map_comp {a b : ℕ} (f : ⦋a⦌ ⟶ ⦋b⦌) :
    SSet.toDiagSet.map (SSet.stdSimplex.map f) ≫ (toDiagSetObjStdSimplexIso.{u} b).hom =
      (toDiagSetObjStdSimplexIso a).hom ≫ uliftYoneda.map (simplexFunctor.map f) :=
  stdSimplexCompToDiagSetIso.hom.naturality f

private theorem toDiagSet_map_joinInclLeft_comp_stdSimplexIso_hom (m n : ℕ) :
    SSet.toDiagSet.map (SSet.joinInclLeft Δ[m] Δ[n]) ≫ (stdSimplexIso.{u} m n).hom =
      WithInitial.joinInclLeft _ _ := by
  have hA : simplexFunctor.map (AugmentedSimplexCategory.inl' ⦋m⦌ ⦋n⦌) ≫
      (atomSimplexJoinIso m n).inv = joinInclLeftHom (atomSimplex m) (atomSimplex n) := by
    exact (Iso.comp_inv_eq _).mpr (joinInclLeftHom_comp_atomSimplexJoinIso_hom m n).symm
  have h₁ : uliftYoneda.{u}.map (simplexFunctor.map (AugmentedSimplexCategory.inl' ⦋m⦌ ⦋n⦌)) ≫
      uliftYoneda.map (atomSimplexJoinIso m n).inv ≫ (joinBallIso _ _).inv =
        WithInitial.joinInclLeft (ball _) (ball _) :=
    (Functor.map_comp_assoc _ _ _ _).symm.trans ((congrArg (fun x ↦ uliftYoneda.map x ≫ _) hA).trans
      ((Iso.eq_comp_inv _).mpr (joinInclLeft_comp_joinBallIso_hom _ _)).symm)
  simp only [stdSimplexIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, joinMapIso_hom]
  rw [← Functor.map_comp_assoc, SSet.joinInclLeft_comp_stdSimplexJoinIso_hom,
    reassoc_of% toDiagSet_map_stdSimplex_map_comp]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((reassoc_of% h₁) _)).trans
    ((congrArg (_ ≫ ·) (WithInitial.joinInclLeft_comp_joinMap _ _)).trans
      (Iso.hom_inv_id_assoc _ _)))

private theorem toDiagSet_map_joinInclRight_comp_stdSimplexIso_hom (m n : ℕ) :
    SSet.toDiagSet.map (SSet.joinInclRight Δ[m] Δ[n]) ≫ (stdSimplexIso.{u} m n).hom =
      WithInitial.joinInclRight _ _ := by
  have hA : simplexFunctor.map (AugmentedSimplexCategory.inr' ⦋m⦌ ⦋n⦌) ≫
      (atomSimplexJoinIso m n).inv = joinInclRightHom (atomSimplex m) (atomSimplex n) := by
    exact (Iso.comp_inv_eq _).mpr (joinInclRightHom_comp_atomSimplexJoinIso_hom m n).symm
  have h₁ : uliftYoneda.{u}.map (simplexFunctor.map (AugmentedSimplexCategory.inr' ⦋m⦌ ⦋n⦌)) ≫
      uliftYoneda.map (atomSimplexJoinIso m n).inv ≫ (joinBallIso _ _).inv =
        WithInitial.joinInclRight (ball _) (ball _) :=
    (Functor.map_comp_assoc _ _ _ _).symm.trans ((congrArg (fun x ↦ uliftYoneda.map x ≫ _) hA).trans
      ((Iso.eq_comp_inv _).mpr (joinInclRight_comp_joinBallIso_hom _ _)).symm)
  simp only [stdSimplexIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, joinMapIso_hom]
  rw [← Functor.map_comp_assoc, SSet.joinInclRight_comp_stdSimplexJoinIso_hom,
    reassoc_of% toDiagSet_map_stdSimplex_map_comp]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((reassoc_of% h₁) _)).trans
    ((congrArg (_ ≫ ·) (WithInitial.joinInclRight_comp_joinMap _ _)).trans
      (Iso.hom_inv_id_assoc _ _)))

private theorem toDiagSet_map_joinMap_comp_stdSimplexIso_hom {k k' m m' : ℕ}
    (f : ⦋k⦌ ⟶ ⦋m⦌) (g : ⦋k'⦌ ⟶ ⦋m'⦌) :
    SSet.toDiagSet.map (SSet.joinMap (SSet.stdSimplex.map f) (SSet.stdSimplex.map g)) ≫
        (stdSimplexIso.{u} m m').hom =
      (stdSimplexIso k k').hom ≫
        WithInitial.joinMap (SSet.toDiagSet.map (SSet.stdSimplex.map f))
          (SSet.toDiagSet.map (SSet.stdSimplex.map g)) := by
  have hA : simplexFunctor.map (AugmentedSimplexCategory.tensorHomOf f g) ≫
      (atomSimplexJoinIso m m').inv =
        (atomSimplexJoinIso k k').inv ≫ joinHom (simplexFunctor.map f) (simplexFunctor.map g) :=
    simplexJoinNatIso.inv.naturality (X := (⦋k⦌, ⦋k'⦌)) (Y := (⦋m⦌, ⦋m'⦌)) (f, g)
  have hB : uliftYoneda.{u}.map (joinHom (simplexFunctor.map f) (simplexFunctor.map g)) ≫
      (joinBallIso _ _).inv = (joinBallIso _ _).inv ≫
        WithInitial.joinMap (uliftYoneda.map (simplexFunctor.map f))
          (uliftYoneda.map (simplexFunctor.map g)) :=
    ((Iso.eq_inv_comp _).mpr (joinMap_uliftYoneda_map_comp_joinBallIso_hom _ _).symm).trans
      (Category.assoc _ _ _).symm |> (Iso.comp_inv_eq _).mpr
  have hC : ∀ {a b : ℕ} (e : ⦋a⦌ ⟶ ⦋b⦌), uliftYoneda.{u}.map (simplexFunctor.map e) ≫
      (toDiagSetObjStdSimplexIso b).inv =
        (toDiagSetObjStdSimplexIso a).inv ≫ SSet.toDiagSet.map (SSet.stdSimplex.map e) :=
    fun e ↦ stdSimplexCompToDiagSetIso.inv.naturality e
  have hD : WithInitial.joinMap (uliftYoneda.{u}.map (simplexFunctor.map f))
      (uliftYoneda.map (simplexFunctor.map g)) ≫
        WithInitial.joinMap (toDiagSetObjStdSimplexIso m).inv (toDiagSetObjStdSimplexIso m').inv =
      WithInitial.joinMap (toDiagSetObjStdSimplexIso k).inv (toDiagSetObjStdSimplexIso k').inv ≫
        WithInitial.joinMap (SSet.toDiagSet.map (SSet.stdSimplex.map f))
          (SSet.toDiagSet.map (SSet.stdSimplex.map g)) :=
    (joinMap_comp_joinMap _ _ _ _).trans ((congrArg₂ WithInitial.joinMap (hC f) (hC g)).trans
      (joinMap_comp_joinMap _ _ _ _).symm)
  have hS : SSet.toDiagSet.map (SSet.joinMap (SSet.stdSimplex.map f) (SSet.stdSimplex.map g)) ≫
      SSet.toDiagSet.map (SSet.stdSimplexJoinIso.{u} m m').hom =
        SSet.toDiagSet.map (SSet.stdSimplexJoinIso k k').hom ≫
          SSet.toDiagSet.map (SSet.stdSimplex.map (AugmentedSimplexCategory.tensorHomOf f g)) :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg SSet.toDiagSet.map
      (SSet.joinMap_stdSimplex_map_comp_stdSimplexJoinIso_hom f g)).trans (Functor.map_comp _ _ _))
  have hA' : uliftYoneda.{u}.map (simplexFunctor.map (AugmentedSimplexCategory.tensorHomOf f g)) ≫
      uliftYoneda.map (atomSimplexJoinIso m m').inv =
        uliftYoneda.map (atomSimplexJoinIso k k').inv ≫
          uliftYoneda.map (joinHom (simplexFunctor.map f) (simplexFunctor.map g)) :=
    (Functor.map_comp _ _ _).symm.trans
      ((congrArg uliftYoneda.map hA).trans (Functor.map_comp _ _ _))
  simp only [stdSimplexIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, joinMapIso_hom,
    Category.assoc]
  exact (comp_comp_eq_of_eq hS _).trans (whisker_eq _
    ((comp_comp_eq_of_eq (toDiagSet_map_stdSimplex_map_comp _) _).trans (whisker_eq _
      ((comp_comp_eq_of_eq hA' _).trans (whisker_eq _ ((comp_comp_eq_of_eq hB _).trans
        (whisker_eq _ hD)))))))

private theorem sSetJoinMap_exchange {K K' T T' : SSet.{u}} (f : K ⟶ K')
    (g : T ⟶ T') :
    SSet.joinMap (𝟙 K) g ≫ SSet.joinMap f (𝟙 T') =
      SSet.joinMap f (𝟙 T) ≫ SSet.joinMap (𝟙 K') g := by
  rw [SSet.joinMap_comp_joinMap, SSet.joinMap_comp_joinMap, Category.id_comp, Category.comp_id,
    Category.id_comp, Category.comp_id]

private instance preservesColimitsOfSize_joinLeftUnder_post (T : SSet.{u}) :
    PreservesColimitsOfSize.{0, u} (SSet.joinLeftUnder T ⋙ Under.post SSet.toDiagSet) :=
  have : PreservesColimitsOfSize.{0, u} (SSet.joinLeftUnder T) := preservesColimitsOfSize_shrink _
  have : PreservesColimitsOfSize.{0, u} (Under.post (X := T) SSet.toDiagSet.{u}) :=
    (Under.postAdjunctionLeft sSetDiagSetAdj).leftAdjoint_preservesColimits
  comp_preservesColimits _ _

private instance preservesColimitsOfSize_joinRightUnder_post (T : SSet.{u}) :
    PreservesColimitsOfSize.{0, u} (SSet.joinRightUnder T ⋙ Under.post SSet.toDiagSet) :=
  have : PreservesColimitsOfSize.{0, u} (SSet.joinRightUnder T) :=
    preservesColimitsOfSize_shrink _
  have : PreservesColimitsOfSize.{0, u} (Under.post (X := T) SSet.toDiagSet.{u}) :=
    (Under.postAdjunctionLeft sSetDiagSetAdj).leftAdjoint_preservesColimits
  comp_preservesColimits _ _

private instance preservesColimitsOfSize_toDiagSet_joinLeftUnder (A : DiagSet.{u}) :
    PreservesColimitsOfSize.{0, u} (SSet.toDiagSet ⋙ WithInitial.joinLeftUnder A) :=
  have : PreservesColimitsOfSize.{0, u} (WithInitial.joinLeftUnder A) :=
    preservesColimitsOfSize_shrink _
  comp_preservesColimits _ _

private instance preservesColimitsOfSize_toDiagSet_joinRightUnder (A : DiagSet.{u}) :
    PreservesColimitsOfSize.{0, u} (SSet.toDiagSet ⋙ WithInitial.joinRightUnder A) :=
  have : PreservesColimitsOfSize.{0, u} (WithInitial.joinRightUnder A) :=
    preservesColimitsOfSize_shrink _
  comp_preservesColimits _ _

private noncomputable def joinLeftUnderStdSimplexIso (m : ℕ) :
    uliftYoneda.{u} ⋙ SSet.joinLeftUnder Δ[m] ⋙ Under.post SSet.toDiagSet ≅
      uliftYoneda.{u} ⋙ SSet.toDiagSet ⋙ WithInitial.joinLeftUnder (SSet.toDiagSet.obj Δ[m]) :=
  NatIso.ofComponents (fun n ↦ Under.isoMk (stdSimplexIso m n.len)
      (toDiagSet_map_joinInclLeft_comp_stdSimplexIso_hom m n.len))
    (fun {n n'} g ↦ Under.UnderMorphism.ext (by
      have e : SSet.stdSimplex.map (𝟙 ⦋m⦌) = 𝟙 Δ[m] := SSet.stdSimplex.map_id _
      have e' : SSet.toDiagSet.map (SSet.stdSimplex.map (𝟙 ⦋m⦌)) = 𝟙 _ :=
        (congrArg SSet.toDiagSet.map e).trans (SSet.toDiagSet.map_id _)
      exact (congrArg (fun x ↦ SSet.toDiagSet.map (SSet.joinMap x (SSet.stdSimplex.map g)) ≫
        (stdSimplexIso m n'.len).hom) e).symm.trans
          ((toDiagSet_map_joinMap_comp_stdSimplexIso_hom.{u} (k' := n.len) (m' := n'.len)
            (𝟙 ⦋m⦌) g).trans (congrArg (fun x ↦ (stdSimplexIso m n.len).hom ≫
              WithInitial.joinMap x (SSet.toDiagSet.map (SSet.stdSimplex.map g))) e'))))

private noncomputable def simplexJoinLeftUnderIso (m : ℕ) :
    SSet.joinLeftUnder Δ[m] ⋙ Under.post SSet.toDiagSet ≅
      SSet.toDiagSet ⋙ WithInitial.joinLeftUnder (SSet.toDiagSet.obj Δ[m]) :=
  sSetIsoOfPreservesColimits _ _ (joinLeftUnderStdSimplexIso m)

private noncomputable def simplexJoinIso (m : ℕ) (T : SSet.{u}) :
    SSet.toDiagSet.obj (SSet.join Δ[m] T) ≅
      WithInitial.join (SSet.toDiagSet.obj Δ[m]) (SSet.toDiagSet.obj T) :=
  (Under.forget _).mapIso ((simplexJoinLeftUnderIso m).app T)

private theorem toDiagSet_map_joinInclLeft_comp_simplexJoinIso_hom (m : ℕ) (T : SSet.{u}) :
    SSet.toDiagSet.map (SSet.joinInclLeft Δ[m] T) ≫ (simplexJoinIso m T).hom =
      WithInitial.joinInclLeft _ _ :=
  Under.w ((simplexJoinLeftUnderIso m).hom.app T)

private theorem toDiagSet_map_joinMap_id_comp_simplexJoinIso_hom (m : ℕ) {T T' : SSet.{u}}
    (g : T ⟶ T') :
    SSet.toDiagSet.map (SSet.joinMap (𝟙 Δ[m]) g) ≫ (simplexJoinIso m T').hom =
      (simplexJoinIso m T).hom ≫ WithInitial.joinMap (𝟙 _) (SSet.toDiagSet.map g) :=
  congrArg CommaMorphism.right ((simplexJoinLeftUnderIso m).hom.naturality g)

private theorem simplexJoinIso_hom_stdSimplex (m n : ℕ) :
    (simplexJoinIso.{u} m Δ[n]).hom = (stdSimplexIso m n).hom :=
  congrArg CommaMorphism.right (sSetIsoOfPreservesColimits_hom_app
    (SSet.joinLeftUnder Δ[m] ⋙ Under.post SSet.toDiagSet)
    (SSet.toDiagSet ⋙ WithInitial.joinLeftUnder _) (joinLeftUnderStdSimplexIso m) ⦋n⦌)

private theorem toDiagSet_map_joinInclRight_comp_simplexJoinIso_hom (m : ℕ) (T : SSet.{u}) :
    SSet.toDiagSet.map (SSet.joinInclRight Δ[m] T) ≫ (simplexJoinIso m T).hom =
      WithInitial.joinInclRight _ _ :=
  toDiagSet_ext (G := SSet.toDiagSet ⋙ WithInitial.joinLeftUnder (SSet.toDiagSet.obj Δ[m]) ⋙
      Under.forget _)
    (α := fun T ↦ SSet.toDiagSet.map (SSet.joinInclRight Δ[m] T) ≫ (simplexJoinIso m T).hom)
    (β := fun _ ↦ WithInitial.joinInclRight _ _)
    (fun {_ K'} g ↦ (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (simplexJoinIso m K').hom) (Functor.map_comp _ _ _)).symm.trans
        ((congrArg (fun x ↦ SSet.toDiagSet.map x ≫ (simplexJoinIso m K').hom)
          (SSet.joinInclRight_comp_joinMap (𝟙 Δ[m]) g).symm).trans
          ((Functor.map_comp_assoc _ _ _ _).trans
            ((whisker_eq _ (toDiagSet_map_joinMap_id_comp_simplexJoinIso_hom m g)).trans
              (Category.assoc _ _ _).symm)))))
    (fun _ ↦ (WithInitial.joinInclRight_comp_joinMap _ _).symm)
    (fun n ↦ (congrArg (_ ≫ ·) (simplexJoinIso_hom_stdSimplex m n)).trans
      (toDiagSet_map_joinInclRight_comp_stdSimplexIso_hom m n)) T

private theorem toDiagSet_map_joinMap_comp_simplexJoinIso_hom {m m' : ℕ} (f : ⦋m⦌ ⟶ ⦋m'⦌)
    (T : SSet.{u}) :
    SSet.toDiagSet.map (SSet.joinMap (SSet.stdSimplex.map f) (𝟙 T)) ≫ (simplexJoinIso m' T).hom =
      (simplexJoinIso m T).hom ≫
        WithInitial.joinMap (SSet.toDiagSet.map (SSet.stdSimplex.map f)) (𝟙 _) :=
  under_ext (SSet.joinLeftUnder Δ[m] ⋙ Under.post SSet.toDiagSet)
    (G := SSet.toDiagSet ⋙ WithInitial.joinLeftUnder (SSet.toDiagSet.obj Δ[m']) ⋙ Under.forget _)
    (α := fun T ↦ SSet.toDiagSet.map (SSet.joinMap (SSet.stdSimplex.map f) (𝟙 T)) ≫
      (simplexJoinIso m' T).hom)
    (β := fun T ↦ (simplexJoinIso m T).hom ≫
      WithInitial.joinMap (SSet.toDiagSet.map (SSet.stdSimplex.map f)) (𝟙 _))
    (fun {_ K'} g ↦ (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (simplexJoinIso m' K').hom) (Functor.map_comp _ _ _)).symm.trans
        ((congrArg (fun x ↦ SSet.toDiagSet.map x ≫ (simplexJoinIso m' K').hom)
          (sSetJoinMap_exchange _ _)).trans
          ((Functor.map_comp_assoc _ _ _ _).trans
            ((whisker_eq _ (toDiagSet_map_joinMap_id_comp_simplexJoinIso_hom m' g)).trans
              (Category.assoc _ _ _).symm)))))
    (fun g ↦ (toDiagSet_map_joinMap_id_comp_simplexJoinIso_hom m g =≫ _).trans
      ((Category.assoc _ _ _).trans ((whisker_eq _ (WithInitial.joinMap_exchange _ _)).trans
        (Category.assoc _ _ _).symm)))
    (fun T ↦ ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (Functor.map_comp _ _ _)).symm.trans
      ((congrArg (fun x ↦ SSet.toDiagSet.map x ≫ (simplexJoinIso m' T).hom)
        (SSet.joinInclLeft_comp_joinMap _ _)).trans ((Functor.map_comp_assoc _ _ _ _).trans
          (whisker_eq _ (toDiagSet_map_joinInclLeft_comp_simplexJoinIso_hom m' T)))))).trans
      ((Category.assoc _ _ _).symm.trans
        ((toDiagSet_map_joinInclLeft_comp_simplexJoinIso_hom m T =≫ _).trans
          (WithInitial.joinInclLeft_comp_joinMap _ _))).symm)
    (fun n ↦ by
      have e : SSet.stdSimplex.map (𝟙 ⦋n⦌) = 𝟙 Δ[n] := SSet.stdSimplex.map_id _
      have e' : SSet.toDiagSet.map (SSet.stdSimplex.map (𝟙 ⦋n⦌)) = 𝟙 _ :=
        (congrArg SSet.toDiagSet.map e).trans (SSet.toDiagSet.map_id _)
      exact (congrArg (fun x ↦ SSet.toDiagSet.map (SSet.joinMap (SSet.stdSimplex.map f) x) ≫
        (simplexJoinIso m' Δ[n]).hom) e).symm.trans
          ((whisker_eq _ (simplexJoinIso_hom_stdSimplex m' n)).trans
            ((toDiagSet_map_joinMap_comp_stdSimplexIso_hom.{u} f (𝟙 ⦋n⦌)).trans
              ((congrArg (fun x ↦ (stdSimplexIso m n).hom ≫
                WithInitial.joinMap (SSet.toDiagSet.map (SSet.stdSimplex.map f)) x) e').trans
                ((simplexJoinIso_hom_stdSimplex m n).symm =≫ _))))) T

private noncomputable def simplexJoinRightUnderIso (T : SSet.{u}) :
    uliftYoneda.{u} ⋙ SSet.joinRightUnder T ⋙ Under.post SSet.toDiagSet ≅
      uliftYoneda.{u} ⋙ SSet.toDiagSet ⋙ WithInitial.joinRightUnder (SSet.toDiagSet.obj T) :=
  NatIso.ofComponents (fun n ↦ Under.isoMk (simplexJoinIso n.len T)
      (toDiagSet_map_joinInclRight_comp_simplexJoinIso_hom n.len T))
    (fun {n n'} g ↦ Under.UnderMorphism.ext
      (toDiagSet_map_joinMap_comp_simplexJoinIso_hom (m := n.len) (m' := n'.len) g T))

noncomputable def toDiagSetJoinRightUnderIso (T : SSet.{u}) :
    SSet.joinRightUnder T ⋙ Under.post SSet.toDiagSet ≅
      SSet.toDiagSet ⋙ WithInitial.joinRightUnder (SSet.toDiagSet.obj T) :=
  sSetIsoOfPreservesColimits _ _ (simplexJoinRightUnderIso T)

noncomputable def toDiagSetJoinIso (K T : SSet.{u}) :
    SSet.toDiagSet.obj (SSet.join K T) ≅
      WithInitial.join (SSet.toDiagSet.obj K) (SSet.toDiagSet.obj T) :=
  (Under.forget _).mapIso ((toDiagSetJoinRightUnderIso T).app K)

@[reassoc]
theorem toDiagSet_map_joinInclRight_comp_toDiagSetJoinIso_hom (K T : SSet.{u}) :
    SSet.toDiagSet.map (SSet.joinInclRight K T) ≫ (toDiagSetJoinIso K T).hom =
      WithInitial.joinInclRight (SSet.toDiagSet.obj K) (SSet.toDiagSet.obj T) :=
  Under.w ((toDiagSetJoinRightUnderIso T).hom.app K)

private theorem toDiagSet_map_joinMap_id_comp_toDiagSetJoinIso_hom {K K' : SSet.{u}}
    (f : K ⟶ K') (T : SSet.{u}) :
    SSet.toDiagSet.map (SSet.joinMap f (𝟙 T)) ≫ (toDiagSetJoinIso K' T).hom =
      (toDiagSetJoinIso K T).hom ≫ WithInitial.joinMap (SSet.toDiagSet.map f) (𝟙 _) :=
  congrArg CommaMorphism.right ((toDiagSetJoinRightUnderIso T).hom.naturality f)

private theorem toDiagSetJoinIso_hom_stdSimplex (m : ℕ) (T : SSet.{u}) :
    (toDiagSetJoinIso Δ[m] T).hom = (simplexJoinIso m T).hom :=
  congrArg CommaMorphism.right (sSetIsoOfPreservesColimits_hom_app
    (SSet.joinRightUnder T ⋙ Under.post SSet.toDiagSet)
    (SSet.toDiagSet ⋙ WithInitial.joinRightUnder _) (simplexJoinRightUnderIso T) ⦋m⦌)

@[reassoc]
theorem toDiagSet_map_joinInclLeft_comp_toDiagSetJoinIso_hom (K T : SSet.{u}) :
    SSet.toDiagSet.map (SSet.joinInclLeft K T) ≫ (toDiagSetJoinIso K T).hom =
      WithInitial.joinInclLeft (SSet.toDiagSet.obj K) (SSet.toDiagSet.obj T) :=
  toDiagSet_ext (G := SSet.toDiagSet ⋙ WithInitial.joinRightUnder (SSet.toDiagSet.obj T) ⋙
      Under.forget _)
    (α := fun K ↦ SSet.toDiagSet.map (SSet.joinInclLeft K T) ≫ (toDiagSetJoinIso K T).hom)
    (β := fun _ ↦ WithInitial.joinInclLeft _ _)
    (fun {_ K'} f ↦ (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (toDiagSetJoinIso K' T).hom) (Functor.map_comp _ _ _)).symm.trans
        ((congrArg (fun x ↦ SSet.toDiagSet.map x ≫ (toDiagSetJoinIso K' T).hom)
          (SSet.joinInclLeft_comp_joinMap f (𝟙 T)).symm).trans
          ((Functor.map_comp_assoc _ _ _ _).trans
            ((whisker_eq _ (toDiagSet_map_joinMap_id_comp_toDiagSetJoinIso_hom f T)).trans
              (Category.assoc _ _ _).symm)))))
    (fun _ ↦ (WithInitial.joinInclLeft_comp_joinMap _ _).symm)
    (fun m ↦ (whisker_eq _ (toDiagSetJoinIso_hom_stdSimplex m T)).trans
      (toDiagSet_map_joinInclLeft_comp_simplexJoinIso_hom m T)) K

private theorem toDiagSet_map_id_joinMap_comp_toDiagSetJoinIso_hom (K : SSet.{u}) {T T' : SSet.{u}}
    (g : T ⟶ T') :
    SSet.toDiagSet.map (SSet.joinMap (𝟙 K) g) ≫ (toDiagSetJoinIso K T').hom =
      (toDiagSetJoinIso K T).hom ≫ WithInitial.joinMap (𝟙 _) (SSet.toDiagSet.map g) :=
  under_ext (SSet.joinRightUnder T ⋙ Under.post SSet.toDiagSet)
    (G := SSet.toDiagSet ⋙ WithInitial.joinRightUnder (SSet.toDiagSet.obj T') ⋙ Under.forget _)
    (α := fun K ↦ SSet.toDiagSet.map (SSet.joinMap (𝟙 K) g) ≫ (toDiagSetJoinIso K T').hom)
    (β := fun K ↦ (toDiagSetJoinIso K T).hom ≫ WithInitial.joinMap (𝟙 _) (SSet.toDiagSet.map g))
    (fun {_ K'} f ↦ (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (toDiagSetJoinIso K' T').hom) (Functor.map_comp _ _ _)).symm.trans
        ((congrArg (fun x ↦ SSet.toDiagSet.map x ≫ (toDiagSetJoinIso K' T').hom)
          (sSetJoinMap_exchange f g).symm).trans
          ((Functor.map_comp_assoc _ _ _ _).trans
            ((whisker_eq _ (toDiagSet_map_joinMap_id_comp_toDiagSetJoinIso_hom f T')).trans
              (Category.assoc _ _ _).symm)))))
    (fun f ↦ (toDiagSet_map_joinMap_id_comp_toDiagSetJoinIso_hom f T =≫ _).trans
      ((Category.assoc _ _ _).trans ((whisker_eq _ (WithInitial.joinMap_exchange _ _).symm).trans
        (Category.assoc _ _ _).symm)))
    (fun K ↦ ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (Functor.map_comp _ _ _)).symm.trans
      ((congrArg (fun x ↦ SSet.toDiagSet.map x ≫ (toDiagSetJoinIso K T').hom)
        (SSet.joinInclRight_comp_joinMap _ _)).trans ((Functor.map_comp_assoc _ _ _ _).trans
          (whisker_eq _ (toDiagSet_map_joinInclRight_comp_toDiagSetJoinIso_hom K T')))))).trans
      ((Category.assoc _ _ _).symm.trans
        ((toDiagSet_map_joinInclRight_comp_toDiagSetJoinIso_hom K T =≫ _).trans
          (WithInitial.joinInclRight_comp_joinMap _ _))).symm)
    (fun m ↦ (whisker_eq _ (toDiagSetJoinIso_hom_stdSimplex m T')).trans
      ((toDiagSet_map_joinMap_id_comp_simplexJoinIso_hom m g).trans
        ((toDiagSetJoinIso_hom_stdSimplex m T).symm =≫ _))) K

@[reassoc]
theorem toDiagSet_map_joinMap_comp_toDiagSetJoinIso_hom {K K' T T' : SSet.{u}} (f : K ⟶ K')
    (g : T ⟶ T') :
    SSet.toDiagSet.map (SSet.joinMap f g) ≫ (toDiagSetJoinIso K' T').hom =
      (toDiagSetJoinIso K T).hom ≫
        WithInitial.joinMap (SSet.toDiagSet.map f) (SSet.toDiagSet.map g) := by
  have hs : SSet.joinMap f g = SSet.joinMap f (𝟙 T) ≫ SSet.joinMap (𝟙 K') g := by
    rw [SSet.joinMap_comp_joinMap, Category.comp_id, Category.id_comp]
  have hd : WithInitial.joinMap (SSet.toDiagSet.map f) (SSet.toDiagSet.map g) =
      WithInitial.joinMap (SSet.toDiagSet.map f) (𝟙 _) ≫
        WithInitial.joinMap (𝟙 _) (SSet.toDiagSet.map g) := by
    rw [joinMap_comp_joinMap, Category.comp_id, Category.id_comp]
  rw [hs, hd, Functor.map_comp_assoc, toDiagSet_map_id_joinMap_comp_toDiagSetJoinIso_hom,
    reassoc_of% toDiagSet_map_joinMap_id_comp_toDiagSetJoinIso_hom]

theorem toDiagSetJoinIso_stdSimplex (m n : ℕ) :
    (toDiagSetJoinIso Δ[m] Δ[n]).hom =
      SSet.toDiagSet.map (SSet.stdSimplexJoinIso m n).hom ≫
        (toDiagSetObjStdSimplexIso.{u} (m + n + 1)).hom ≫
          uliftYoneda.map (atomSimplexJoinIso m n).inv ≫ (joinBallIso _ _).inv ≫
            WithInitial.joinMap (toDiagSetObjStdSimplexIso m).inv
              (toDiagSetObjStdSimplexIso n).inv :=
  (toDiagSetJoinIso_hom_stdSimplex m Δ[n]).trans (simplexJoinIso_hom_stdSimplex m n)

noncomputable def toDiagSetJoinLeftUnderIso (K : SSet.{u}) :
    SSet.joinLeftUnder K ⋙ Under.post SSet.toDiagSet ≅
      SSet.toDiagSet ⋙ WithInitial.joinLeftUnder (SSet.toDiagSet.obj K) :=
  NatIso.ofComponents (fun T ↦ Under.isoMk (toDiagSetJoinIso K T)
      (toDiagSet_map_joinInclLeft_comp_toDiagSetJoinIso_hom K T))
    (fun g ↦ Under.UnderMorphism.ext (toDiagSet_map_id_joinMap_comp_toDiagSetJoinIso_hom K g))

private noncomputable def sliceAdjunctionSSet (K : SSet.{u}) :
    SSet.toDiagSet ⋙ WithInitial.joinRightUnder (SSet.toDiagSet.obj K) ⊣
      Under.post DiagSet.toSSet ⋙ Under.map (sSetDiagSetAdj.unit.app K) ⋙ SSet.slice K :=
  ((SSet.joinRightUnderAdjunction K).comp (Under.postAdjunctionLeft sSetDiagSetAdj)).ofNatIsoLeft
    (toDiagSetJoinRightUnderIso K)

private noncomputable def sliceAdjunctionDiagSet (K : SSet.{u}) :
    SSet.toDiagSet ⋙ WithInitial.joinRightUnder (SSet.toDiagSet.obj K) ⊣
      WithInitial.slice (SSet.toDiagSet.obj K) ⋙ DiagSet.toSSet :=
  sSetDiagSetAdj.comp (WithInitial.joinRightUnderAdjunction (SSet.toDiagSet.obj K))

noncomputable def toSSetSliceIso (K : SSet.{u}) :
    WithInitial.slice (SSet.toDiagSet.obj K) ⋙ DiagSet.toSSet ≅
      Under.post DiagSet.toSSet ⋙ Under.map (sSetDiagSetAdj.unit.app K) ⋙ SSet.slice K :=
  (sliceAdjunctionDiagSet K).rightAdjointUniq (sliceAdjunctionSSet K)

noncomputable def toSSetCosliceIso (K : SSet.{u}) :
    WithInitial.coslice (SSet.toDiagSet.obj K) ⋙ DiagSet.toSSet ≅
      Under.post DiagSet.toSSet ⋙ Under.map (sSetDiagSetAdj.unit.app K) ⋙ SSet.coslice K :=
  Adjunction.rightAdjointUniq
    (sSetDiagSetAdj.comp (WithInitial.joinLeftUnderAdjunction (SSet.toDiagSet.obj K)))
    (((SSet.joinLeftUnderAdjunction K).comp (Under.postAdjunctionLeft sSetDiagSetAdj)).ofNatIsoLeft
      (toDiagSetJoinLeftUnderIso K))

private theorem joinInclLeft_comp_sliceAdjunctionDiagSet_counit_app_right (K : SSet.{u})
    (p : Under (SSet.toDiagSet.obj K)) :
    joinInclLeft _ _ ≫ ((sliceAdjunctionDiagSet K).counit.app p).right =
      (sSetDiagSetAdj.homEquiv _ _).symm
        (DiagSet.toSSet.map ((sliceProj (SSet.toDiagSet.obj K)).app p)) := by
  refine (joinInclLeft_comp_joinMap_assoc (sSetDiagSetAdj.counit.app _) (𝟙 _)
    ((WithInitial.joinRightUnderAdjunction (SSet.toDiagSet.obj K)).counit.app p).right).trans ?_
  refine (congrArg (_ ≫ ·) (sliceProj_app_eq _ p).symm).trans ?_
  exact (sSetDiagSetAdj.counit.naturality _).symm.trans (sSetDiagSetAdj.homEquiv_counit _ _ _).symm

private theorem joinInclLeft_comp_sliceAdjunctionSSet_counit_app_right (K : SSet.{u})
    (p : Under (SSet.toDiagSet.obj K)) :
    joinInclLeft _ _ ≫ ((sliceAdjunctionSSet K).counit.app p).right =
      (sSetDiagSetAdj.homEquiv _ _).symm (SSet.sliceπ _) :=
  (Category.assoc _ _ _).symm.trans ((((Iso.comp_inv_eq _).mpr
    (toDiagSet_map_joinInclLeft_comp_toDiagSetJoinIso_hom _ K).symm) =≫ _).trans
      ((Functor.map_comp_assoc _ _ _ _).symm.trans (sSetDiagSetAdj.homEquiv_counit _ _ _).symm))

@[reassoc]
theorem toSSetSliceIso_hom_app_comp_sliceπ (K : SSet.{u}) (p : Under (SSet.toDiagSet.obj K)) :
    (toSSetSliceIso K).hom.app p ≫ SSet.sliceπ _ =
      DiagSet.toSSet.map ((sliceProj (SSet.toDiagSet.obj K)).app p) := by
  have e := ((sliceAdjunctionSSet K).homEquiv_counit _ _ _).symm.trans
    (Adjunction.homEquiv_symm_rightAdjointUniq_hom_app (sliceAdjunctionDiagSet K)
      (sliceAdjunctionSSet K) p)
  refine (sSetDiagSetAdj.homEquiv _ _).symm.injective ?_
  refine (sSetDiagSetAdj.homEquiv_naturality_left_symm _ _).trans ?_
  refine (congrArg (_ ≫ ·)
    (joinInclLeft_comp_sliceAdjunctionSSet_counit_app_right K p).symm).trans ?_
  refine (joinInclLeft_comp_joinMap_assoc _ (𝟙 _) _).symm.trans ?_
  exact (congrArg (fun f ↦ joinInclLeft _ _ ≫ f.right) e).trans
    (joinInclLeft_comp_sliceAdjunctionDiagSet_counit_app_right K p)

private noncomputable def underMapCounitIso (A : DiagSet.{u}) :
    Under.map (sSetDiagSetAdj.counit.app A) ⋙ Under.post DiagSet.toSSet ⋙
      Under.map (sSetDiagSetAdj.unit.app (DiagSet.toSSet.obj A)) ≅ Under.post DiagSet.toSSet :=
  NatIso.ofComponents (fun _ ↦ Under.isoMk (Iso.refl _)
    ((Category.comp_id _).trans ((congrArg (_ ≫ ·) (DiagSet.toSSet.map_comp _ _)).trans
      (sSetDiagSetAdj.right_triangle_components_assoc A _))))
    (fun _ ↦ Under.UnderMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm))

noncomputable def sliceComparison (A : DiagSet.{u}) :
    WithInitial.slice A ⋙ DiagSet.toSSet ⟶
      Under.post DiagSet.toSSet ⋙ SSet.slice (DiagSet.toSSet.obj A) :=
  Functor.whiskerRight (sliceRestrict (sSetDiagSetAdj.counit.app A)) DiagSet.toSSet ≫
    Functor.whiskerLeft (Under.map (sSetDiagSetAdj.counit.app A))
      (toSSetSliceIso (DiagSet.toSSet.obj A)).hom ≫
        Functor.whiskerRight (underMapCounitIso A).hom (SSet.slice (DiagSet.toSSet.obj A))

@[reassoc]
theorem sliceComparison_app_comp_sliceπ (A : DiagSet.{u}) (p : Under A) :
    (sliceComparison A).app p ≫ SSet.sliceπ _ = DiagSet.toSSet.map ((sliceProj A).app p) := by
  dsimp only [sliceComparison, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [Category.assoc, Category.assoc, SSet.slice_map_sliceπ]
  refine (whisker_eq _ (whisker_eq _ (Category.comp_id _))).trans ?_
  refine (whisker_eq _ (toSSetSliceIso_hom_app_comp_sliceπ _ _)).trans ?_
  exact (DiagSet.toSSet.map_comp _ _).symm.trans
    (congrArg DiagSet.toSSet.map (sliceRestrict_app_comp_sliceProj_app _ _))

end Atoms.Diagrammatic
