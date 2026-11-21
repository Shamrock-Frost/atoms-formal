import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.CategoryTheory.Category.ULift

universe u

namespace SimplexCategory

open CategoryTheory Simplicial

variable {n : ℕ}

theorem map_toOrderHom_eq (G : Fin (n + 1) ⥤ AsSmall.{u} SimplexCategory) {i j k : Fin (n + 1)}
    (f : i ⟶ j) (g : j ⟶ k) (h : i ⟶ k) (x : Fin ((ULift.down (G.obj i)).len + 1)) :
    (G.map h).down.toOrderHom x = (G.map g).down.toOrderHom ((G.map f).down.toOrderHom x) := by
  obtain rfl : h = f ≫ g := Subsingleton.elim _ _
  exact congrArg (fun φ : G.obj i ⟶ G.obj k => φ.down.toOrderHom x) (G.map_comp f g)

def lastVertexHom (G : Fin (n + 1) ⥤ AsSmall.{u} SimplexCategory) :
    ⦋n⦌ ⟶ ULift.down (G.obj (Fin.last n)) :=
  SimplexCategory.Hom.mk
    { toFun := fun i => (G.map (homOfLE (Fin.le_last i))).down.toOrderHom (Fin.last _)
      monotone' := fun i j hij => by
        dsimp only
        rw [map_toOrderHom_eq G (homOfLE hij) (homOfLE (Fin.le_last j))
          (homOfLE (Fin.le_last i))]
        exact (G.map (homOfLE (Fin.le_last j))).down.toOrderHom.monotone (Fin.le_last _) }

theorem lastVertexHom_toCat_comp {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (G : Fin (n + 1) ⥤ AsSmall.{u} SimplexCategory) :
    lastVertexHom ((SimplexCategory.toCat.map θ).toFunctor ⋙ G) ≫
        (G.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))).down =
      θ ≫ lastVertexHom G := by
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i => ?_))
  exact (map_toOrderHom_eq G _ _ _ _).symm

end SimplexCategory
