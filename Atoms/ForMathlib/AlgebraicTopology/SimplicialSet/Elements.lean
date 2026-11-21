import Atoms.ForMathlib.AlgebraicTopology.SimplexCategory.Basic
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.CategoryTheory.Elements

universe u

namespace SSet

open CategoryTheory Opposite Simplicial

theorem elementsHom_ext {K : SSet.{u}} {X Y : ((SSet.asSmall.obj K).Elements)ᵒᵖ} {f g : X ⟶ Y}
    (h : f.unop.1.unop.down = g.unop.1.unop.down) : f = g :=
  Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ (Quiver.Hom.unop_inj (ULift.ext _ _ h)))

theorem map_lastVertexHom_toCat_comp (K : SSet.{u}) {m k : ℕ} (θ : ⦋m⦌ ⟶ ⦋k⦌)
    (σ : ComposableArrows ((SSet.asSmall.obj K).Elements)ᵒᵖ k) :
    K.map (SimplexCategory.lastVertexHom (((SimplexCategory.toCat.map θ).toFunctor ⋙ σ) ⋙
        (CategoryOfElements.π (SSet.asSmall.obj K)).leftOp)).op
        (σ.obj ((SimplexCategory.toCat.map θ).toFunctor.obj (Fin.last m))).unop.2 =
      K.map θ.op (K.map (SimplexCategory.lastVertexHom (σ ⋙
        (CategoryOfElements.π (SSet.asSmall.obj K)).leftOp)).op (σ.obj (Fin.last k)).unop.2) := by
  have hx : (σ.obj ((SimplexCategory.toCat.map θ).toFunctor.obj (Fin.last m))).unop.2 =
      K.map ((σ.map (homOfLE (Fin.le_last ((SimplexCategory.toCat.map θ).toFunctor.obj
        (Fin.last m))))).unop.1.unop.down).op (σ.obj (Fin.last k)).unop.2 :=
    (σ.map (homOfLE (Fin.le_last _))).unop.2.symm
  rw [hx]
  refine (Functor.map_comp_apply K _ _ _).symm.trans
    ((congrArg (fun φ => K.map φ _) ?_).trans (Functor.map_comp_apply K _ _ _))
  exact congrArg Quiver.Hom.op
    (SimplexCategory.lastVertexHom_toCat_comp θ
      (σ ⋙ (CategoryOfElements.π (SSet.asSmall.obj K)).leftOp))

theorem comp_lastVertexHom_eq (K : SSet.{u}) {m k : ℕ} (θ : ⦋m⦌ ⟶ ⦋k⦌)
    (τ : ComposableArrows ((SSet.asSmall.obj K).Elements)ᵒᵖ k)
    (σ : ComposableArrows ((SSet.asSmall.obj K).Elements)ᵒᵖ m)
    (h : (SimplexCategory.toCat.map θ).toFunctor ⋙ τ = σ)
    (e : σ.obj (Fin.last m) = τ.obj ((SimplexCategory.toCat.map θ).toFunctor.obj (Fin.last m))) :
    θ ≫ SimplexCategory.lastVertexHom (τ ⋙ (CategoryOfElements.π (SSet.asSmall.obj K)).leftOp) =
      SimplexCategory.lastVertexHom (σ ⋙ (CategoryOfElements.π (SSet.asSmall.obj K)).leftOp) ≫
        (eqToHom e ≫ τ.map (homOfLE (Fin.le_last
          ((SimplexCategory.toCat.map θ).toFunctor.obj (Fin.last m))))).unop.1.unop.down := by
  subst h
  rw [eqToHom_refl, Category.id_comp]
  exact (SimplexCategory.lastVertexHom_toCat_comp θ
    (τ ⋙ (CategoryOfElements.π (SSet.asSmall.obj K)).leftOp)).symm

end SSet
