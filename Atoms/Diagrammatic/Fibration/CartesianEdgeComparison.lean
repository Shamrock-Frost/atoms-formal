import Atoms.Diagrammatic.Fibration.CartesianEdge
import Atoms.Diagrammatic.Joyal.Comparison
import Atoms.Diagrammatic.SimplicialJoin
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianEdge
import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
import Atoms.Homotopical.Simplicial.FibrewiseEquivalence

open CategoryTheory Limits Opposite HomotopicalAlgebra Simplicial Atoms.Shape
open CategoryTheory.WithInitial (join joinInclRight joinMap slice sliceRes
  hasLiftingProperty_leibnizSlice_iff)
open scoped Atoms.Diagrammatic.DiagSet.Join

universe u

namespace Atoms.Diagrammatic

noncomputable def toDiagSetJoinFunctorIso :
    Functor.curry.obj SSet.joinFunctor.{u} ⋙
        (Functor.whiskeringRight SSet.{u} SSet.{u} DiagSet.{u}).obj SSet.toDiagSet ≅
      SSet.toDiagSet ⋙ 𝒥 ⋙ (Functor.whiskeringLeft SSet.{u} DiagSet.{u} DiagSet.{u}).obj
        SSet.toDiagSet :=
  NatIso.ofComponents
    (fun K ↦ NatIso.ofComponents (fun T ↦ toDiagSetJoinIso K T) fun g ↦
      (toDiagSet_map_joinMap_comp_toDiagSetJoinIso_hom (𝟙 K) g).trans
        (congrArg (fun φ ↦ (toDiagSetJoinIso K _).hom ≫ joinMap φ (SSet.toDiagSet.map g))
          (SSet.toDiagSet.map_id K)))
    fun f ↦ NatTrans.ext <| funext fun T ↦
      (toDiagSet_map_joinMap_comp_toDiagSetJoinIso_hom f (𝟙 T)).trans
        (congrArg (fun φ ↦ (toDiagSetJoinIso _ T).hom ≫ joinMap (SSet.toDiagSet.map f) φ)
          (SSet.toDiagSet.map_id T))

private noncomputable def toDiagSetδZeroIso :
    Arrow.mk (SSet.toDiagSet.{u}.map (SSet.stdSimplex.δ (0 : Fin 2))) ≅ Arrow.mk arrowOutput.{u} :=
  Arrow.isoMk (toDiagSetObjStdSimplexIso 0)
    (toDiagSetObjStdSimplexIso 1 ≪≫ uliftYoneda.mapIso atomSimplexOneIsoGlobe) (by
      have h : SSet.toDiagSet.{u}.map (SSet.stdSimplex.δ (0 : Fin 2)) ≫
          (toDiagSetObjStdSimplexIso 1).hom = (toDiagSetObjStdSimplexIso 0).hom ≫
            uliftYoneda.map (simplexHom (SimplexCategory.δ (0 : Fin 2)).toOrderHom) :=
        stdSimplexCompToDiagSetIso.hom.naturality _
      have hδ : simplexHom (SimplexCategory.δ (0 : Fin 2)).toOrderHom ≫
          atomSimplexOneIsoGlobe.hom = atomGlobeVertex true :=
        simplexHom_δ_comp_atomSimplexOneIsoGlobe_hom true
      refine Eq.trans ?_ ((h =≫ uliftYoneda.map atomSimplexOneIsoGlobe.hom).symm.trans
        (Category.assoc _ _ _))
      rw [Category.assoc, ← Functor.map_comp, hδ]
      rfl)

private noncomputable def toDiagSetPushoutObjObj {K L : SSet.{u}} {i : K ⟶ L}
    (sq : (Functor.curry.obj SSet.joinFunctor).PushoutObjObj i (SSet.stdSimplex.δ (0 : Fin 2))) :
    Functor.PushoutObjObj 𝒥 (SSet.toDiagSet.map i) arrowOutput.{u} :=
  have : PreservesColimitsOfSize.{0, 0} SSet.toDiagSet.{u} :=
    sSetDiagSetAdj.leftAdjoint_preservesColimits
  (sq.map toDiagSetJoinFunctorIso).ofArrowIsoRight toDiagSetδZeroIso

private noncomputable def toDiagSetJoinArrowIso (K : SSet.{u}) :
    SSet.toDiagSet.obj (SSet.join K Δ[1]) ≅ join (SSet.toDiagSet.obj K) (ball.{u} (atomGlobe 1)) :=
  toDiagSetJoinIso K Δ[1] ≪≫
    WithInitial.joinMapIso (Iso.refl _) (Comma.rightIso toDiagSetδZeroIso)

private lemma toDiagSetPushoutObjObj_ι {K L : SSet.{u}} {i : K ⟶ L}
    (sq : (Functor.curry.obj SSet.joinFunctor).PushoutObjObj i (SSet.stdSimplex.δ (0 : Fin 2))) :
    (toDiagSetPushoutObjObj sq).ι = SSet.toDiagSet.map sq.ι ≫ (toDiagSetJoinArrowIso L).hom :=
  Category.assoc _ _ _

variable {E S : DiagSet.{u}} {x y : E.Vertex}

private lemma toDiagSetδZeroIso_hom_right_comp (e : E.Edge x y) :
    toDiagSetδZeroIso.hom.right ≫ uliftYonedaEquiv.symm e.cell =
      (sSetDiagSetAdj.homEquiv _ _).symm (SSet.yonedaEquiv.symm (E.edgeEquivSSet e).edge) := by
  rw [homEquiv_symm_yonedaEquiv_symm, DiagSet.edgeEquivSSet_edge, uliftYonedaEquiv_symm_map]
  exact Category.assoc _ _ _

private lemma joinInclRight_comp_inr_comp_homEquiv_symm_iff {K L : SSet.{u}} {i : K ⟶ L}
    (sq : (Functor.curry.obj SSet.joinFunctor).PushoutObjObj i (SSet.stdSimplex.δ (0 : Fin 2)))
    (e : E.Edge x y) (u : sq.pt ⟶ DiagSet.toSSet.obj E) :
    joinInclRight _ _ ≫ (toDiagSetPushoutObjObj sq).inr ≫ (sSetDiagSetAdj.homEquiv _ _).symm u =
        uliftYonedaEquiv.symm e.cell ↔
      SSet.joinInclRight K Δ[1] ≫ sq.inr ≫ u = SSet.yonedaEquiv.symm (E.edgeEquivSSet e).edge := by
  have hR : joinInclRight (SSet.toDiagSet.obj K) (SSet.toDiagSet.obj Δ[1]) ≫
      (toDiagSetJoinIso K Δ[1]).inv = SSet.toDiagSet.map (SSet.joinInclRight K Δ[1]) :=
    (Iso.comp_inv_eq _).2 (toDiagSet_map_joinInclRight_comp_toDiagSetJoinIso_hom K Δ[1]).symm
  have hinr : joinInclRight (SSet.toDiagSet.obj K) (ball.{u} (atomGlobe 1)) ≫
      (toDiagSetPushoutObjObj sq).inr = (Comma.rightIso toDiagSetδZeroIso).inv ≫
        SSet.toDiagSet.map (SSet.joinInclRight K Δ[1] ≫ sq.inr) :=
    (Category.assoc _ _ _).symm.trans
      ((WithInitial.joinInclRight_comp_joinMap (𝟙 _) toDiagSetδZeroIso.inv.right =≫ _).trans
        ((Category.assoc _ _ _).trans (whisker_eq _ (((Category.assoc _ _ _).symm.trans
          (hR =≫ _)).trans (Functor.map_comp _ _ _).symm))))
  have h : joinInclRight _ _ ≫ (toDiagSetPushoutObjObj sq).inr ≫
      (sSetDiagSetAdj.homEquiv _ _).symm u = (Comma.rightIso toDiagSetδZeroIso).inv ≫
        (sSetDiagSetAdj.homEquiv _ _).symm (SSet.joinInclRight K Δ[1] ≫ sq.inr ≫ u) :=
    (Category.assoc _ _ _).symm.trans ((hinr =≫ _).trans ((Category.assoc _ _ _).trans
      (whisker_eq _ (((sSetDiagSetAdj.homEquiv_naturality_left_symm _ _).symm.trans
        (congrArg _ (Category.assoc _ _ _)))))))
  exact (Eq.congr_left h).trans ((Iso.inv_comp_eq _).trans
    ((Eq.congr_right (toDiagSetδZeroIso_hom_right_comp e)).trans (Equiv.apply_eq_iff_eq _)))

theorem DiagSet.Edge.hasLiftingProperty_toDiagSet_map_iff {K L : SSet.{u}} (i : K ⟶ L)
    (p : E ⟶ S) (e : E.Edge x y) :
    HasLiftingProperty (SSet.toDiagSet.map i) (e.leibnizSlice p) ↔
      HasLiftingProperty i (SSet.leibnizSlice (SSet.stdSimplex.δ 0) (DiagSet.toSSet.map p)
        (SSet.yonedaEquiv.symm (E.edgeEquivSSet e).edge)) := by
  let sq := Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj SSet.joinFunctor) i
    (SSet.stdSimplex.δ (0 : Fin 2))
  let θ := toDiagSetJoinArrowIso L
  have hι := toDiagSetPushoutObjObj_ι sq
  rw [DiagSet.Edge.leibnizSlice, hasLiftingProperty_leibnizSlice_iff (toDiagSetPushoutObjObj sq) p,
    SSet.hasLiftingProperty_leibnizSlice_iff sq]
  refine ⟨fun h u v hsq hu ↦ ?_, fun h a b hsq ha ↦ ?_⟩
  · have hsq' : CommSq ((sSetDiagSetAdj.homEquiv _ _).symm u) (toDiagSetPushoutObjObj sq).ι p
        (θ.inv ≫ (sSetDiagSetAdj.homEquiv _ _).symm v) :=
      ⟨(sSetDiagSetAdj.homEquiv_naturality_right_symm _ _).symm.trans ((congrArg _ hsq.w).trans
        ((sSetDiagSetAdj.homEquiv_naturality_left_symm _ _).trans
          (((Category.assoc _ _ _).trans (whisker_eq _ (θ.hom_inv_id_assoc _))).symm.trans
            (hι =≫ _).symm)))⟩
    obtain ⟨l⟩ := (h hsq' ((joinInclRight_comp_inr_comp_homEquiv_symm_iff sq e u).2
      hu)).exists_lift
    exact ⟨⟨⟨sSetDiagSetAdj.homEquiv _ _ (θ.hom ≫ l.l),
      ((sSetDiagSetAdj.homEquiv_naturality_left _ _).symm.trans (congrArg _
        (((Category.assoc _ _ _).symm.trans (hι.symm =≫ _)).trans l.fac_left))).trans
          (Equiv.apply_symm_apply _ _),
      ((sSetDiagSetAdj.homEquiv_naturality_right _ _).symm.trans (congrArg _
        (((Category.assoc _ _ _).trans (whisker_eq _ l.fac_right)).trans
          (θ.hom_inv_id_assoc _)))).trans (Equiv.apply_symm_apply _ _)⟩⟩⟩
  · have hsq' : CommSq (sSetDiagSetAdj.homEquiv _ _ a) sq.ι (DiagSet.toSSet.map p)
        (sSetDiagSetAdj.homEquiv _ _ (θ.hom ≫ b)) :=
      ⟨(sSetDiagSetAdj.homEquiv_naturality_right _ _).symm.trans ((congrArg _
        (hsq.w.trans ((hι =≫ b).trans (Category.assoc _ _ _)))).trans
          (sSetDiagSetAdj.homEquiv_naturality_left _ _))⟩
    obtain ⟨l⟩ := (h hsq' ((joinInclRight_comp_inr_comp_homEquiv_symm_iff sq e _).1
      ((whisker_eq _ (whisker_eq _ (Equiv.symm_apply_apply _ a))).trans ha))).exists_lift
    exact ⟨⟨⟨θ.inv ≫ (sSetDiagSetAdj.homEquiv _ _).symm l.l,
      (hι =≫ _).trans (((Category.assoc _ _ _).trans (whisker_eq _ (θ.hom_inv_id_assoc _))).trans
        (((sSetDiagSetAdj.homEquiv_naturality_left_symm _ _).symm.trans
          (congrArg _ l.fac_left)).trans (Equiv.symm_apply_apply _ _))),
      (Category.assoc _ _ _).trans ((whisker_eq _
        (((sSetDiagSetAdj.homEquiv_naturality_right_symm _ _).symm.trans
          (congrArg _ l.fac_right)).trans (Equiv.symm_apply_apply _ _))).trans
            (θ.inv_hom_id_assoc _))⟩⟩⟩

theorem DiagSet.IsCartesianEdge.isCartesianEdge_toSSet {p : E ⟶ S} {e : E.Edge x y}
    (he : DiagSet.IsCartesianEdge p e) :
    SSet.IsCartesianEdge (DiagSet.toSSet.map p)
      (SSet.yonedaEquiv.symm (E.edgeEquivSSet e).edge) := by
  rintro _ _ _ ⟨n⟩
  have := mono_toDiagSet_map_boundary_ι.{u} n
  exact (DiagSet.Edge.hasLiftingProperty_toDiagSet_map_iff _ p e).1
    (he _ (MorphismProperty.monomorphisms.infer_property _))

theorem rlp_I_toSSet_map_of_rlp_monomorphisms {A B : DiagSet.{u}} {g : A ⟶ B}
    (hg : (MorphismProperty.monomorphisms DiagSet.{u}).rlp g) :
    SSet.modelCategoryQuillen.I.rlp (DiagSet.toSSet.map g) := by
  intro K L i hi
  have : Mono i := SSet.modelCategoryQuillen.I_le_monomorphisms i hi
  exact (sSetDiagSetAdj.hasLiftingProperty_iff _ _).1
    (hg _ (MorphismProperty.monomorphisms.infer_property _))

open SSet.modelCategoryJoyal in
theorem rlp_monomorphisms_of_rlp_I_toSSet_map {A B : DiagSet.{u}} (g : A ⟶ B)
    [Fibration ((DiagSet.toInfty 1).map g)] [hB : IsFibrant ((DiagSet.toInfty 1).obj B)]
    (hg : SSet.modelCategoryQuillen.I.rlp (DiagSet.toSSet.map g)) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp g := by
  let g' := (DiagSet.toInfty 1).map g
  have hA : IsFibrant ((DiagSet.toInfty 1).obj A) := isFibrant_of_fibration g'
  have : WeakEquivalence (DiagSet.Infty.toSSet.map g') := weakEquivalence_of_rlp_I hg
  have : WeakEquivalence (SSet.toDiagSetInfty.map (DiagSet.Infty.toSSet.map g')) :=
    isQuillen_sSetDiagSetAdj.weakEquivalence_map _
  have := weakEquivalence_sSetDiagSetAdj_counit_app _ hA
  have := weakEquivalence_sSetDiagSetAdj_counit_app _ hB
  have : WeakEquivalence
      (DiagSet.Infty.sSetDiagSetAdj.counit.app ((DiagSet.toInfty 1).obj A) ≫ g') := by
    rw [← DiagSet.Infty.sSetDiagSetAdj.counit_naturality g']
    infer_instance
  have : WeakEquivalence g' :=
    weakEquivalence_of_precomp
      (DiagSet.Infty.sSetDiagSetAdj.counit.app ((DiagSet.toInfty 1).obj A)) _
  exact rlp_monomorphisms_of_trivialFibration_toInfty_map 1

theorem DiagSet.isCartesianEdge_of_isCartesianEdge_toSSet {p : E ⟶ S} {e : E.Edge x y}
    [Fibration ((DiagSet.toInfty 1).map (e.leibnizSlice p))]
    [IsFibrant ((DiagSet.toInfty 1).obj (e.sliceTarget p))]
    (he : SSet.IsCartesianEdge (DiagSet.toSSet.map p)
      (SSet.yonedaEquiv.symm (E.edgeEquivSSet e).edge)) :
    DiagSet.IsCartesianEdge p e :=
  rlp_monomorphisms_of_rlp_I_toSSet_map _ fun _ _ i hi ↦
    (sSetDiagSetAdj.hasLiftingProperty_iff i _).1
      ((DiagSet.Edge.hasLiftingProperty_toDiagSet_map_iff i p e).2 (he i hi))

theorem DiagSet.isCartesianEdge_iff_isCartesianEdge_toSSet (p : E ⟶ S) (e : E.Edge x y)
    [Fibration ((DiagSet.toInfty 1).map (e.leibnizSlice p))]
    [IsFibrant ((DiagSet.toInfty 1).obj (e.sliceTarget p))] :
    DiagSet.IsCartesianEdge p e ↔
      SSet.IsCartesianEdge (DiagSet.toSSet.map p)
        (SSet.yonedaEquiv.symm (E.edgeEquivSSet e).edge) :=
  ⟨DiagSet.IsCartesianEdge.isCartesianEdge_toSSet,
    DiagSet.isCartesianEdge_of_isCartesianEdge_toSSet⟩

private lemma quasicategory_innerFibration_toSSet {p : E ⟶ S}
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    (DiagSet.toSSet.obj E).Quasicategory ∧ (DiagSet.toSSet.obj S).Quasicategory ∧
      SSet.InnerFibration (DiagSet.toSSet.map p) :=
  ⟨quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj E)
      (isFibrant_of_fibration ((DiagSet.toInfty 1).map p)),
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj S) inferInstance,
    innerFibration_toSSet_map ((DiagSet.toInfty 1).map p) inferInstance⟩

private lemma stdSimplex_δ_comp_yonedaEquiv_symm (σ : diagram E (atomSimplex 2)) (i : Fin 3)
    {a b : E.Vertex} {e : E.Edge a b}
    (h : E.map (atomSimplexOneIsoGlobe.inv ≫ simplexHom (SimplexCategory.δ i).toOrderHom).op σ =
      e.cell) :
    SSet.stdSimplex.δ i ≫ (SSet.yonedaEquiv (X := DiagSet.toSSet.obj E) (n := ⦋2⦌)).symm σ =
      SSet.yonedaEquiv.symm (E.edgeEquivSSet e).edge := by
  refine (SSet.yonedaEquiv_symm_naturality_left (X := DiagSet.toSSet.obj E) (SimplexCategory.δ i)
    σ).trans (congrArg _ ?_)
  rw [DiagSet.edgeEquivSSet_edge, ← h, ← Functor.map_comp_apply, ← op_comp,
    Iso.hom_inv_id_assoc]
  rfl

theorem DiagSet.IsCartesianEdge.of_simplex_two {p : E ⟶ S} {z : E.Vertex}
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (σ : diagram E (atomSimplex 2)) {e₀₁ : E.Edge x y} {e₁₂ : E.Edge y z} {e₀₂ : E.Edge x z}
    (h₀₁ : E.map (atomSimplexOneIsoGlobe.inv ≫
      simplexHom (SimplexCategory.δ (2 : Fin 3)).toOrderHom).op σ = e₀₁.cell)
    (h₁₂ : E.map (atomSimplexOneIsoGlobe.inv ≫
      simplexHom (SimplexCategory.δ (0 : Fin 3)).toOrderHom).op σ = e₁₂.cell)
    (h₀₂ : E.map (atomSimplexOneIsoGlobe.inv ≫
      simplexHom (SimplexCategory.δ (1 : Fin 3)).toOrderHom).op σ = e₀₂.cell)
    [Fibration ((DiagSet.toInfty 1).map (e₀₂.leibnizSlice p))]
    [IsFibrant ((DiagSet.toInfty 1).obj (e₀₂.sliceTarget p))]
    (he₀₁ : DiagSet.IsCartesianEdge p e₀₁) (he₁₂ : DiagSet.IsCartesianEdge p e₁₂) :
    DiagSet.IsCartesianEdge p e₀₂ := by
  obtain ⟨_, _, _⟩ := quasicategory_innerFibration_toSSet (p := p)
  have hg := he₁₂.isCartesianEdge_toSSet
  have hf := he₀₁.isCartesianEdge_toSSet
  rw [← stdSimplex_δ_comp_yonedaEquiv_symm σ 0 h₁₂] at hg
  rw [← stdSimplex_δ_comp_yonedaEquiv_symm σ 2 h₀₁] at hf
  refine DiagSet.isCartesianEdge_of_isCartesianEdge_toSSet ?_
  rw [← stdSimplex_δ_comp_yonedaEquiv_symm σ 1 h₀₂]
  exact (SSet.isCartesianEdge_δ_two_iff_δ_one (DiagSet.toSSet.map p) _ hg).1 hf

end Atoms.Diagrammatic
