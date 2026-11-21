import Atoms.Diagrammatic.OneTruncation

open CategoryTheory Simplicial Opposite
open Atoms.Shape

universe u

namespace Atoms.Diagrammatic

namespace OneTruncation

def ballSimplex {k n : ℕ} (g : ⦋k⦌ ⟶ ⦋n⦌) :
    (DiagSet.toSSet.obj (ball.{u} (atomSimplex n))) _⦋k⦌ :=
  ULift.up (simplexFunctor.map g)

theorem ballSimplex_id (n : ℕ) :
    ballSimplex.{u} (𝟙 ⦋n⦌) = uliftYonedaEquiv (𝟙 (ball.{u} (atomSimplex n))) :=
  ULift.ext _ _ (simplexFunctor.map_id _)

theorem exists_ballSimplex_eq {k n : ℕ}
    (c : (DiagSet.toSSet.obj (ball.{u} (atomSimplex n))) _⦋k⦌) : ∃ g, ballSimplex g = c :=
  ⟨simplexFunctor.preimage c.down, ULift.ext _ _ (simplexFunctor.map_preimage _)⟩

@[simp]
theorem map_ballSimplex {j k n : ℕ} (f : ⦋j⦌ ⟶ ⦋k⦌) (g : ⦋k⦌ ⟶ ⦋n⦌) :
    (DiagSet.toSSet.obj (ball.{u} (atomSimplex n))).map f.op (ballSimplex g) =
      ballSimplex (f ≫ g) :=
  ULift.ext _ _ (simplexFunctor.map_comp f g).symm

@[simp]
theorem toSSet_map_app_ballSimplex {k m n : ℕ} (f : ⦋k⦌ ⟶ ⦋m⦌) (g : ⦋m⦌ ⟶ ⦋n⦌) :
    (DiagSet.toSSet.map (uliftYoneda.map (simplexFunctor.map g))).app _ (ballSimplex.{u} f) =
      ballSimplex (f ≫ g) :=
  ULift.ext _ _ (simplexFunctor.map_comp f g).symm

def ballEdge {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) :
    SSet.Edge (ballSimplex.{u} (SimplexCategory.const ⦋0⦌ ⦋n⦌ i))
      (ballSimplex.{u} (SimplexCategory.const ⦋0⦌ ⦋n⦌ j)) :=
  SSet.Edge.mk (ballSimplex (SimplexCategory.mkOfLe i j h))
    ((map_ballSimplex _ _).trans (congrArg ballSimplex (SimplexCategory.Hom.ext_zero_left _ _)))
    ((map_ballSimplex _ _).trans (congrArg ballSimplex (SimplexCategory.Hom.ext_zero_left _ _)))

@[simp]
theorem ballEdge_edge {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) :
    (ballEdge.{u} h).edge = ballSimplex (SimplexCategory.mkOfLe i j h) :=
  rfl

theorem ballEdge_refl {n : ℕ} (i : Fin (n + 1)) :
    ballEdge.{u} (le_refl i) = SSet.Edge.id _ :=
  SSet.Edge.ext ((congrArg ballSimplex (SimplexCategory.Hom.ext_one_left _ _)).trans
    (map_ballSimplex _ _).symm)

def ballCompStruct {n : ℕ} {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    SSet.Edge.CompStruct (ballEdge.{u} hij) (ballEdge.{u} hjk) (ballEdge.{u} (hij.trans hjk)) :=
  SSet.Edge.CompStruct.mk (ballSimplex (SimplexCategory.mkOfLeComp i j k hij hjk))
    ((map_ballSimplex _ _).trans (congrArg ballSimplex (SimplexCategory.Hom.ext_one_left _ _)))
    ((map_ballSimplex _ _).trans (congrArg ballSimplex (SimplexCategory.Hom.ext_one_left _ _)))
    ((map_ballSimplex _ _).trans (congrArg ballSimplex (SimplexCategory.Hom.ext_one_left _ _)))

@[simp]
theorem toFin_obj_mk_ballSimplex {n : ℕ} (f : ⦋0⦌ ⟶ ⦋n⦌) :
    (toFin.{u} n).obj (mk (ballSimplex f)) = f.toOrderHom 0 := by
  have h : mk (ballSimplex.{u} f) = (oneTruncation.map (uliftYoneda.map
      (simplexFunctor.map f))).toFunctor.obj (mk (ballSimplex (𝟙 ⦋0⦌))) :=
    (congrArg mk ((congrArg ballSimplex (Category.id_comp f)).symm.trans
      (toSSet_map_app_ballSimplex _ _).symm)).trans (oneTruncation_map_obj_mk _ _).symm
  exact (congrArg (toFin n).obj h).trans ((congrArg (fun F => F.obj (mk (ballSimplex (𝟙 ⦋0⦌))))
    (oneTruncation_map_comp_toFin.{u} f)).trans
      (congrArg f.toOrderHom (Subsingleton.elim (α := Fin 1) _ _)))

noncomputable def fromFin (n : ℕ) : Fin (n + 1) ⥤ OneTruncation (ball.{u} (atomSimplex n)) where
  obj i := mk (ballSimplex (SimplexCategory.const ⦋0⦌ ⦋n⦌ i))
  map f := homMk (ballEdge (leOfHom f))
  map_id i := (congrArg homMk (ballEdge_refl i)).trans (homMk_id _)
  map_comp f g := (homMk_comp_homMk (ballCompStruct (leOfHom f) (leOfHom g))).symm

@[simp]
theorem fromFin_obj {n : ℕ} (i : Fin (n + 1)) :
    (fromFin.{u} n).obj i = mk (ballSimplex (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)) :=
  rfl

@[simp]
theorem fromFin_map {n : ℕ} {i j : Fin (n + 1)} (f : i ⟶ j) :
    (fromFin.{u} n).map f = homMk (ballEdge (leOfHom f)) :=
  rfl

theorem fromFin_comp_toFin (n : ℕ) : fromFin.{u} n ⋙ toFin.{u} n = 𝟭 (Fin (n + 1)) :=
  CategoryTheory.Functor.ext (fun _ => toFin_obj_mk_ballSimplex _) fun _ _ _ =>
    Subsingleton.elim _ _

theorem toFin_comp_fromFin (n : ℕ) :
    toFin.{u} n ⋙ fromFin.{u} n = 𝟭 (OneTruncation (ball.{u} (atomSimplex n))) := by
  refine functor_ext fun x y e => ?_
  obtain ⟨g, hg⟩ := exists_ballSimplex_eq e.edge
  have hx : x = ballSimplex (SimplexCategory.δ 1 ≫ g) :=
    e.src_eq.symm.trans ((congrArg _ hg.symm).trans (map_ballSimplex _ _))
  have hy : y = ballSimplex (SimplexCategory.δ 0 ≫ g) :=
    e.tgt_eq.symm.trans ((congrArg _ hg.symm).trans (map_ballSimplex _ _))
  have he : (ballEdge (leOfHom ((toFin n).map (homMk e)))).edge = e.edge :=
    (congrArg ballSimplex (SimplexCategory.Hom.ext_one_left (SimplexCategory.mkOfLe _ _ _) g
      ((congrArg (fun x => (toFin n).obj (mk x)) hx).trans (toFin_obj_mk_ballSimplex _))
      ((congrArg (fun y => (toFin n).obj (mk y)) hy).trans (toFin_obj_mk_ballSimplex _)))).trans hg
  exact arrowMk_homMk_eq _ e he

theorem fromFin_naturality {m n : ℕ} (g : ⦋m⦌ ⟶ ⦋n⦌) :
    (SimplexCategory.toCat.map g).toFunctor ⋙ fromFin.{u} n =
      fromFin.{u} m ⋙ (oneTruncation.map (uliftYoneda.map (simplexFunctor.map g))).toFunctor := by
  have hg := oneTruncation_map_comp_toFin.{u} g
  exact (((((((Functor.id_comp _).symm.trans
    (congrArg (· ⋙ (SimplexCategory.toCat.map g).toFunctor ⋙ fromFin.{u} n)
      (fromFin_comp_toFin.{u} m).symm)).trans
    (Functor.assoc _ _ _)).trans
    (congrArg (fromFin.{u} m ⋙ ·) (Functor.assoc _ _ _).symm)).trans
    (congrArg (fun F => fromFin.{u} m ⋙ F ⋙ fromFin.{u} n) hg.symm)).trans
    (congrArg (fromFin.{u} m ⋙ ·) (Functor.assoc _ _ _))).trans
    (congrArg (fun F => fromFin.{u} m ⋙
      (oneTruncation.map (uliftYoneda.map (simplexFunctor.map g))).toFunctor ⋙ F)
      (toFin_comp_fromFin.{u} n))).trans
    (congrArg (fromFin.{u} m ⋙ ·) (Functor.comp_id _))

end OneTruncation

noncomputable def toSSetCategoricalNerveIso (C : Cat.{u, u}) :
    DiagSet.toSSet.obj (categoricalNerve.obj C) ≅ nerve C where
  hom :=
    { app n := ↾fun F => OneTruncation.fromFin n.unop.len ⋙ F
      naturality m n g := by
        ext F
        exact (congrArg (· ⋙ F) (OneTruncation.fromFin_naturality g.unop)).symm }
  inv := nerveToCategoricalNerve C
  hom_inv_id := by
    ext n F
    exact congrArg (· ⋙ F) (OneTruncation.toFin_comp_fromFin n.unop.len)
  inv_hom_id := by
    ext n A
    exact congrArg (· ⋙ A) (OneTruncation.fromFin_comp_toFin n.unop.len)

@[simp]
theorem toSSetCategoricalNerveIso_hom_app (C : Cat.{u, u}) (n : SimplexCategoryᵒᵖ)
    (F : (DiagSet.toSSet.obj (categoricalNerve.obj C)).obj n) :
    (toSSetCategoricalNerveIso C).hom.app n F = OneTruncation.fromFin n.unop.len ⋙ F :=
  rfl

theorem toSSetCategoricalNerveIso_inv (C : Cat.{u, u}) :
    (toSSetCategoricalNerveIso C).inv = nerveToCategoricalNerve C :=
  rfl

noncomputable def categoricalNerveCompToSSetIso :
    categoricalNerve.{u} ⋙ DiagSet.toSSet ≅ nerveFunctor.{u, u} :=
  NatIso.ofComponents toSSetCategoricalNerveIso fun _ => rfl

@[simp]
theorem categoricalNerveCompToSSetIso_app (C : Cat.{u, u}) :
    categoricalNerveCompToSSetIso.app C = toSSetCategoricalNerveIso C :=
  rfl

end Atoms.Diagrammatic
