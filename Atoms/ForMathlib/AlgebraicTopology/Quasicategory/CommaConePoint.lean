import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CommaCone
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.FibrewisePath
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.MapOver

open CategoryTheory Limits Simplicial MonoidalClosed

universe u

namespace SSet

@[reassoc]
theorem commaConeBase_comp_eval_end {Q : SSet.{u}} (d : Δ[0] ⟶ Q) (α : Bool) :
    SSet.commaConeBase d ≫
        (ihom (∂Δ[1] : SSet.{u})).map
          (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) Q) ≫
        SSet.evalVertex (SSet.yonedaEquiv
          (SSet.boundary.ι (cond α 0 1) : Δ[0] ⟶ (∂Δ[1] : SSet.{u}))) Q =
      cond α (SSet.stdSimplex.isTerminalObj₀.from Q ≫ d) (𝟙 Q) := by
  rw [SSet.ihom_map_comp_evalVertex]
  have he : SSet.evalVertex (SSet.yonedaEquiv
      (SSet.boundary.ι (cond α 0 1) : Δ[0] ⟶ (∂Δ[1] : SSet.{u})))
        ((ihom Δ[0]).obj Q) =
      (pre (SSet.boundary.ι (cond α 0 1))).app _ ≫
        SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) _ := by
    rw [SSet.pre_app_comp_evalVertex, ← SSet.yonedaEquiv_comp, Category.id_comp]
  rw [he]
  simp only [Category.assoc]
  cases α
  · simp only [cond_false, SSet.commaConeBase_pre_boundary_ι_one_assoc,
      SSet.constDiagram_comp_evalVertex_assoc, SSet.constDiagram_comp_evalVertex]
  · simp only [cond_true, SSet.commaConeBase_pre_boundary_ι_zero_assoc,
      SSet.constDiagram_comp_evalVertex_assoc]
    rw [SSet.comp_evalVertex, SSet.diagramPoint, uncurry_curry,
      CartesianMonoidalCategory.lift_fst_assoc, ← Category.assoc]
    exact congrArg (· ≫ d) (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

theorem isPullback_commaCone_point {Q : SSet.{u}} (d : Δ[0] ⟶ Q) :
    IsPullback
      (SSet.commaConeArrow d ≫ (ihom (Δ[1] : SSet.{u})).map
        (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) Q))
      (SSet.commaConeπ d) ((pre (∂Δ[1]).ι).app Q)
      (SSet.commaConeBase d ≫ (ihom (∂Δ[1] : SSet.{u})).map
        (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) Q)) := by
  refine (SSet.isPullback_commaCone d).of_iso (Iso.refl _)
    ((ihom (Δ[1] : SSet.{u})).mapIso
      (asIso (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) Q))) (Iso.refl _)
    ((ihom (∂Δ[1] : SSet.{u})).mapIso
      (asIso (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) Q))) ?_ ?_ ?_ ?_
  · exact (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact ((pre (∂Δ[1]).ι).naturality _).symm
  · exact (Category.id_comp _).symm

private theorem vertex_commaConeBase {Q : SSet.{u}} (c c₀ : Q _⦋0⦌) :
    SSet.yonedaEquiv.symm c ≫ SSet.commaConeBase (SSet.yonedaEquiv.symm c₀) ≫
        (ihom (∂Δ[1] : SSet.{u})).map
          (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) Q) =
      SSet.boundaryPoint c c₀ := by
  have he (α : Bool) := congrArg (fun f : Q ⟶ Q => SSet.yonedaEquiv.symm c ≫ f)
    (commaConeBase_comp_eval_end (SSet.yonedaEquiv.symm c₀) α)
  apply (cancel_mono (SSet.boundaryEval Q)).1
  rw [SSet.boundaryPoint_comp_boundaryEval]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, SSet.boundaryEval, CartesianMonoidalCategory.lift_fst]
    simpa only [cond_false, Category.assoc, Category.comp_id]
      using he false
  · simp only [Category.assoc, SSet.boundaryEval, CartesianMonoidalCategory.lift_snd]
    have ht : SSet.yonedaEquiv.symm c ≫ SSet.stdSimplex.isTerminalObj₀.from Q = 𝟙 Δ[0] :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    simpa only [cond_true, Category.assoc, reassoc_of% ht, Category.id_comp] using he true

noncomputable def mappingSpaceToCommaCone {Q : SSet.{u}} (c c₀ : Q _⦋0⦌) :
    SSet.mappingSpace Q c c₀ ⟶ SSet.commaCone (SSet.yonedaEquiv.symm c₀) :=
  (isPullback_commaCone_point (SSet.yonedaEquiv.symm c₀)).lift
    (pullback.fst _ _) (pullback.snd _ _ ≫ SSet.yonedaEquiv.symm c) (by
      exact (SSet.mappingSpace_fst_pre c c₀).trans
        ((congrArg (pullback.snd _ _ ≫ ·) (vertex_commaConeBase c c₀)).symm.trans
          (Category.assoc _ _ _).symm))

theorem isPullback_mappingSpaceToCommaCone {Q : SSet.{u}} (c c₀ : Q _⦋0⦌) :
    IsPullback (mappingSpaceToCommaCone c c₀) (pullback.snd _ _)
      (SSet.commaConeπ (SSet.yonedaEquiv.symm c₀)) (SSet.yonedaEquiv.symm c) := by
  refine IsPullback.of_right ?_ (IsPullback.lift_snd _ _ _ _)
    (isPullback_commaCone_point (SSet.yonedaEquiv.symm c₀))
  have hf : mappingSpaceToCommaCone c c₀ ≫ SSet.commaConeArrow _ ≫
      (ihom (Δ[1] : SSet.{u})).map
        (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) Q) = pullback.fst _ _ :=
    IsPullback.lift_fst _ _ _ _
  change IsPullback (mappingSpaceToCommaCone c c₀ ≫ SSet.commaConeArrow _ ≫
      (ihom (Δ[1] : SSet.{u})).map
        (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) Q)) (pullback.snd _ _)
    ((pre (∂Δ[1]).ι).app Q) (SSet.yonedaEquiv.symm c ≫
      SSet.commaConeBase (SSet.yonedaEquiv.symm c₀) ≫
        (ihom (∂Δ[1] : SSet.{u})).map
          (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) Q))
  rw [hf, vertex_commaConeBase]
  exact SSet.isPullback_mappingSpace_pre Q c c₀

@[reassoc]
theorem mappingSpaceToCommaCone_arrow {Q : SSet.{u}} (c c₀ : Q _⦋0⦌) :
    mappingSpaceToCommaCone c c₀ ≫ SSet.commaConeArrow (SSet.yonedaEquiv.symm c₀) ≫
        (ihom (Δ[1] : SSet.{u})).map
          (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) Q) =
      pullback.fst _ _ := IsPullback.lift_fst _ _ _ _

@[reassoc]
theorem mappingSpaceToCommaCone_π {Q : SSet.{u}} (c c₀ : Q _⦋0⦌) :
    mappingSpaceToCommaCone c c₀ ≫ SSet.commaConeπ (SSet.yonedaEquiv.symm c₀) =
      pullback.snd _ _ ≫ SSet.yonedaEquiv.symm c := IsPullback.lift_snd _ _ _ _

end SSet
