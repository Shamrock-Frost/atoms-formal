import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso
import Mathlib.AlgebraicTopology.SimplicialSet.Op

open CategoryTheory Limits Simplicial

universe v u

namespace SSet

open Opposite

private def finRevFunctor (n : ℕ) : Fin (n + 1) ⥤ (Fin (n + 1))ᵒᵖ where
  obj i := op i.rev
  map h := (homOfLE (Fin.rev_le_rev.2 (leOfHom h))).op

private theorem functor_ext_of_thin {A B : Type*} [Category* A] [Category* B] [Quiver.IsThin B]
    {F G : A ⥤ B} (h : ∀ a, F.obj a = G.obj a) : F = G :=
  CategoryTheory.Functor.ext h (fun _ _ _ ↦ Subsingleton.elim _ _)

private theorem finRevFunctor_comp_op (n : ℕ) :
    finRevFunctor n ⋙ (finRevFunctor n).op = opOp (Fin (n + 1)) :=
  functor_ext_of_thin fun i ↦ congrArg (fun j ↦ op (op j)) (Fin.rev_rev i)

variable (C : Type u) [Category.{v} C]

private def nerveOpEquiv (n : SimplexCategoryᵒᵖ) : (nerve C).op.obj n ≃ (nerve Cᵒᵖ).obj n where
  toFun F := finRevFunctor _ ⋙ (opObjEquiv F).op
  invFun G := opObjEquiv.symm (finRevFunctor _ ⋙ G.leftOp)
  left_inv F := congrArg (· ⋙ (opObjEquiv F).op.leftOp) (finRevFunctor_comp_op _)
  right_inv G := congrArg (· ⋙ G.leftOp.op) (finRevFunctor_comp_op _)

def nerveOpIso : (nerve C).op ≅ nerve Cᵒᵖ :=
  NatIso.ofComponents (fun n ↦ (nerveOpEquiv C n).toIso) (fun {n m} f ↦ by
    ext F
    have : finRevFunctor m.unop.len ⋙
          (SimplexCategory.rev.map f.unop).toOrderHom.monotone.functor.op =
        f.unop.toOrderHom.monotone.functor ⋙ finRevFunctor n.unop.len :=
      functor_ext_of_thin fun i ↦ congrArg (fun j ↦ op (f.unop.toOrderHom j).rev) (Fin.rev_rev i)
    exact congrArg (· ⋙ (opObjEquiv F).op) this)

theorem stdSimplex.yonedaEquiv_opIso_inv_comp {X : SSet.{u}} {n : ℕ} (σ : Δ[n] ⟶ X) :
    yonedaEquiv ((stdSimplex.opIso ⦋n⦌).inv ≫ opFunctor.map σ) =
      opObjEquiv.symm (yonedaEquiv σ) := by
  rw [yonedaEquiv_comp, opFunctor_map]
  congr 1
  have h : opObjEquiv (yonedaEquiv (stdSimplex.opIso.{u} ⦋n⦌).inv) = yonedaEquiv (𝟙 Δ[n]) :=
    stdSimplex.ext _ _ fun i ↦ Fin.rev_rev i
  rw [h, ← yonedaEquiv_comp, Category.id_comp]

theorem yonedaEquiv_symm_opObjEquiv_symm {X : SSet.{u}} {n : ℕ} (σ : X _⦋n⦌) :
    yonedaEquiv.symm (opObjEquiv.symm σ) =
      (stdSimplex.opIso ⦋n⦌).inv ≫ opFunctor.map (yonedaEquiv.symm σ) := by
  apply yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_opIso_inv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

instance isEquivalence_opFunctor : opFunctor.{u}.IsEquivalence :=
  opEquivalence.isEquivalence_functor

theorem rlp_opFunctor_map_iff {W : MorphismProperty SSet.{u}}
    (hW : ∀ ⦃A B : SSet.{u}⦄ (i : A ⟶ B), W i → W (opFunctor.map i)) {X Y : SSet.{u}}
    (p : X ⟶ Y) : W.rlp (opFunctor.map p) ↔ W.rlp p := by
  have h {X Y : SSet.{u}} {p : X ⟶ Y} (hp : W.rlp p) : W.rlp (opFunctor.map p) := by
    intro A B i hi
    refine (HasLiftingProperty.iff_of_arrow_iso_left
      (Arrow.isoOfNatIso opFunctorCompOpFunctorIso (Arrow.mk i)).symm _).2 ?_
    exact (Functor.hasLiftingProperty_iff_of_isEquivalence opFunctor _ _).2 (hp _ (hW i hi))
  exact ⟨fun hp ↦ (W.rlp.arrow_mk_iso_iff
    (Arrow.isoOfNatIso opFunctorCompOpFunctorIso (Arrow.mk p))).1 (h hp), h⟩

theorem rlp_I_opFunctor_map_iff {X Y : SSet.{u}} (p : X ⟶ Y) :
    modelCategoryQuillen.I.rlp (opFunctor.map p) ↔ modelCategoryQuillen.I.rlp p := by
  rw [← rlp_monomorphisms]
  exact rlp_opFunctor_map_iff (fun _ _ i hi ↦ (opFunctor.{u}.mono_map_iff_mono i).2 hi) p

end SSet

namespace CategoryTheory.Codiscrete

open SSet

variable (X : Type u)

private theorem nerve_ext {n : SimplexCategoryᵒᵖ} {F G : (nerve (Codiscrete X)).obj n}
    (h : ∀ k, F.obj k = G.obj k) : F = G :=
  CategoryTheory.Functor.ext h (fun _ _ _ ↦ rfl)

private def nerveRevEquiv (n : SimplexCategoryᵒᵖ) :
    (nerve (Codiscrete X)).op.obj n ≃ (nerve (Codiscrete X)).obj n where
  toFun F := Codiscrete.functor fun k ↦ ((opObjEquiv F).obj k.rev).as
  invFun F := opObjEquiv.symm (Codiscrete.functor fun k ↦ (F.obj k.rev).as)
  left_inv F := nerve_ext X fun k ↦ congrArg F.obj (Fin.rev_rev k)
  right_inv F := nerve_ext X fun k ↦ congrArg F.obj (Fin.rev_rev k)

def nerveOpIso : (nerve (Codiscrete X)).op ≅ nerve (Codiscrete X) :=
  NatIso.ofComponents (fun n ↦ (nerveRevEquiv X n).toIso) (fun f ↦ by
    ext F k
    exact congrArg (fun j ↦ (F.obj (f.unop.toOrderHom j).rev).as) (Fin.rev_rev k))

private theorem nerveOpIso_hom_app_zero (x : nerve (Codiscrete X) _⦋0⦌) :
    (nerveOpIso X).hom.app _ (opObjEquiv.symm x) = x :=
  nerve_ext X fun _ ↦ congrArg x.obj (Subsingleton.elim (α := Fin 1) _ _)

end CategoryTheory.Codiscrete

namespace SSet

def coherentIsoOpIso : coherentIso.{u}.op ≅ coherentIso.{u} :=
  Codiscrete.nerveOpIso _

theorem coherentIsoOpIso_hom_app_x₀ :
    coherentIsoOpIso.hom.app _ (opObjEquiv.symm coherentIso.x₀) = coherentIso.x₀ :=
  Codiscrete.nerveOpIso_hom_app_zero _ _

theorem coherentIsoOpIso_hom_app_x₁ :
    coherentIsoOpIso.hom.app _ (opObjEquiv.symm coherentIso.x₁) = coherentIso.x₁ :=
  Codiscrete.nerveOpIso_hom_app_zero _ _

end SSet
