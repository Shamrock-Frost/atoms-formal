import Atoms.Diagrammatic.GrayTensor.FunctorCategory
import Atoms.Diagrammatic.GrayTensor.Monoidal
import Atoms.Diagrammatic.Localization.ModelStructure
import Atoms.Diagrammatic.SimplicialAdjunction
import Atoms.Diagrammatic.Vertex
import Atoms.ForMathlib.CategoryTheory.Limits.FunctorToTypes
import Atoms.Shape.SimplexFace
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

open CategoryTheory Limits Opposite Simplicial Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

noncomputable def intervalSource : ball.{u} atomPoint ⟶ ball.{u} (atomSimplex 1) :=
  uliftYoneda.map (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom)

noncomputable def intervalTarget : ball.{u} atomPoint ⟶ ball.{u} (atomSimplex 1) :=
  uliftYoneda.map (simplexHom (SimplexCategory.δ (0 : Fin 2)).toOrderHom)

noncomputable def isTerminalBallAtomSimplexZero : IsTerminal (ball.{u} (atomSimplex 0)) :=
  isTerminalBallAtomPoint

theorem grayTensorLeft_map_eq (A : DiagSet.{u}) {B B' : DiagSet.{u}} (g : B ⟶ B') :
    (grayTensorLeft A).map g = grayTensorBifunctor.map ((𝟙 A, g) : (A, B) ⟶ (A, B')) :=
  rfl

theorem grayTensorRight_map_eq {A A' : DiagSet.{u}} (f : A ⟶ A') (B : DiagSet.{u}) :
    (grayTensorRight B).map f = grayTensorBifunctor.map ((f, 𝟙 B) : (A, B) ⟶ (A', B)) :=
  rfl

theorem grayTensorLeft_map_comp_grayTensorRight_map {A A' B B' : DiagSet.{u}} (f : A ⟶ A')
    (g : B ⟶ B') :
    (grayTensorLeft A).map g ≫ (grayTensorRight B').map f =
      (grayTensorRight B).map f ≫ (grayTensorLeft A').map g := by
  rw [grayTensorLeft_map_eq, grayTensorRight_map_eq, grayTensorLeft_map_eq, grayTensorRight_map_eq,
    ← Functor.map_comp, ← Functor.map_comp, prod_comp, prod_comp]
  simp only [Category.id_comp, Category.comp_id]

theorem grayTensorRight_map_grayTensorSnd {A A' : DiagSet.{u}} (f : A ⟶ A') (B : DiagSet.{u}) :
    (grayTensorRight B).map f ≫ grayTensorSnd A' B = grayTensorSnd A B := by
  rw [grayTensorRight_map_eq, grayTensorSnd, grayTensorSnd, ← Category.assoc, ← Functor.map_comp,
    prod_comp, Category.id_comp, isTerminalBallAtomPoint.hom_ext (f ≫ _)
      (isTerminalBallAtomPoint.from A)]

theorem grayTensorLeft_map_grayTensorSnd (A : DiagSet.{u}) {B B' : DiagSet.{u}} (g : B ⟶ B') :
    (grayTensorLeft A).map g ≫ grayTensorSnd A B' = grayTensorSnd A B ≫ g := by
  rw [grayTensorLeft_map_eq, grayTensorSnd, grayTensorSnd, ← Category.assoc, ← Functor.map_comp,
    prod_comp, Category.assoc, ← GrayDiagSet.leftUnitor_naturality, ← Category.assoc,
    ← Functor.map_comp, prod_comp]
  simp only [Category.id_comp, Category.comp_id]

theorem grayHomRightCellEquiv_map (B Z : DiagSet.{u}) {U V : Atom} (g : V ⟶ U)
    (F : diagram ((grayHomRight B).obj Z) U) :
    grayHomRightCellEquiv B Z V (((grayHomRight B).obj Z).map g.op F) =
      (grayTensorRight B).map (uliftYoneda.map g) ≫ grayHomRightCellEquiv B Z U F :=
  rfl

theorem grayHomRightCellEquiv_map_app (B : DiagSet.{u}) {Z Z' : DiagSet.{u}} (f : Z ⟶ Z')
    (U : Atom) (F : diagram ((grayHomRight B).obj Z) U) :
    grayHomRightCellEquiv B Z' U (((grayHomRight B).map f).app (op U) F) =
      grayHomRightCellEquiv B Z U F ≫ f :=
  rfl

theorem grayHomRightCellEquiv_homEquiv_app (B T Z : DiagSet.{u})
    (F : grayTensor T B ⟶ Z) (U : Atom) (t : diagram T U) :
    grayHomRightCellEquiv B Z U (((grayTensorRightAdjunction B).homEquiv T Z F).app (op U) t) =
      (grayTensorRight B).map (uliftYonedaEquiv.symm t) ≫ F := by
  rfl

theorem grayTensor_hom_ext_left {A B Z : DiagSet.{u}} {f g : grayTensor A B ⟶ Z}
    (h : ∀ (U : Atom) (a : diagram A U), (grayTensorRight B).map (uliftYonedaEquiv.symm a) ≫ f =
      (grayTensorRight B).map (uliftYonedaEquiv.symm a) ≫ g) : f = g := by
  refine grayTensor_hom_ext fun U V a b => ?_
  have e : grayTensorCell a b = ((grayTensorRight B).map (uliftYonedaEquiv.symm a)).app _
      (grayTensorCell (uliftYonedaEquiv (𝟙 (ball.{u} U))) b) :=
    ((grayTensorCell_naturality (uliftYonedaEquiv.symm a) (𝟙 B) _ b).trans
      (congrArg (grayTensorCell · b) (Equiv.apply_symm_apply uliftYonedaEquiv a))).symm
  rw [e, ← NatTrans.comp_app_apply, ← NatTrans.comp_app_apply, h]

def IsFixedEnds (x y : X.Vertex) {A : DiagSet.{u}}
    (F : grayTensor A (ball.{u} (atomSimplex 1)) ⟶ X) : Prop :=
  (grayTensorLeft A).map intervalSource ≫ F =
      grayTensorSnd A (ball atomPoint) ≫ vertexHom x ∧
    (grayTensorLeft A).map intervalTarget ≫ F =
      grayTensorSnd A (ball atomPoint) ≫ vertexHom y

section FixedEnds

variable {x y : X.Vertex}

theorem IsFixedEnds.comp {A A' : DiagSet.{u}} {F : grayTensor A (ball.{u} (atomSimplex 1)) ⟶ X}
    (hF : IsFixedEnds x y F) (f : A' ⟶ A) :
    IsFixedEnds x y ((grayTensorRight (ball.{u} (atomSimplex 1))).map f ≫ F) := by
  constructor
  · rw [← Category.assoc, grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc, hF.1,
      ← Category.assoc, grayTensorRight_map_grayTensorSnd]
  · rw [← Category.assoc, grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc, hF.2,
      ← Category.assoc, grayTensorRight_map_grayTensorSnd]

theorem isFixedEnds_iff_forall {A : DiagSet.{u}} (F : grayTensor A (ball.{u} (atomSimplex 1)) ⟶ X) :
    IsFixedEnds x y F ↔ ∀ (U : Atom) (a : diagram A U),
      IsFixedEnds x y ((grayTensorRight (ball.{u} (atomSimplex 1))).map
        (uliftYonedaEquiv.symm a) ≫ F) := by
  refine ⟨fun hF U a => hF.comp _, fun h => ⟨?_, ?_⟩⟩ <;>
    refine grayTensor_hom_ext_left fun U a => ?_
  · rw [← Category.assoc, ← grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc,
      (h U a).1, ← Category.assoc, grayTensorRight_map_grayTensorSnd]
  · rw [← Category.assoc, ← grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc,
      (h U a).2, ← Category.assoc, grayTensorRight_map_grayTensorSnd]

end FixedEnds

def DiagSet.mappingSpace (X : DiagSet.{u}) (x y : X.Vertex) :
    Subfunctor ((grayHomRight (ball.{u} (atomSimplex 1))).obj X) where
  obj U := {F | IsFixedEnds x y (grayHomRightCellEquiv (ball (atomSimplex 1)) X U.unop F)}
  map _ _ hF := hF.comp _

theorem DiagSet.mem_mappingSpace_iff (x y : X.Vertex) {U : Atom}
    (F : diagram ((grayHomRight (ball.{u} (atomSimplex 1))).obj X) U) :
    F ∈ (X.mappingSpace x y).obj (op U) ↔
      IsFixedEnds x y (grayHomRightCellEquiv (ball (atomSimplex 1)) X U F) :=
  Iff.rfl

noncomputable def DiagSet.mappingSpaceHomEquiv (x y : X.Vertex)
    (T : DiagSet.{u}) :
    (T ⟶ (X.mappingSpace x y).toFunctor) ≃
      {F : grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X // IsFixedEnds x y F} where
  toFun g := ⟨((grayTensorRightAdjunction _).homEquiv T X).symm (g ≫ (X.mappingSpace x y).ι),
    (isFixedEnds_iff_forall _).2 fun U t => by
      have e := grayHomRightCellEquiv_homEquiv_app _ T X
        (((grayTensorRightAdjunction _).homEquiv T X).symm (g ≫ (X.mappingSpace x y).ι)) U t
      rw [Equiv.apply_symm_apply] at e
      rw [← e]
      exact (g.app (op U) t).2⟩
  invFun F := Subfunctor.lift ((grayTensorRightAdjunction _).homEquiv T X F.1) <| by
    rintro ⟨U⟩ _ ⟨t, rfl⟩
    refine (DiagSet.mem_mappingSpace_iff x y _).2 ?_
    rw [grayHomRightCellEquiv_homEquiv_app]
    exact F.2.comp _
  left_inv g := by
    refine (cancel_mono (X.mappingSpace x y).ι).1 ?_
    rw [Subfunctor.lift_ι, Equiv.apply_symm_apply]
  right_inv F := Subtype.ext ((congrArg _ (Subfunctor.lift_ι _ _)).trans
    (Equiv.symm_apply_apply _ _))

theorem DiagSet.mappingSpaceHomEquiv_comp {X : DiagSet.{u}} (x y : X.Vertex)
    {T T' : DiagSet.{u}} (g : T' ⟶ T) (t : T ⟶ (X.mappingSpace x y).toFunctor) :
    (X.mappingSpaceHomEquiv x y T' (g ≫ t)).1 =
      (grayTensorRight _).map g ≫ (X.mappingSpaceHomEquiv x y T t).1 :=
  (congrArg _ (Category.assoc _ _ _)).trans
    ((grayTensorRightAdjunction _).homEquiv_naturality_left_symm _ _)

instance isIso_grayTensorSnd_ballAtomSimplexZero (B : DiagSet.{u}) :
    IsIso (grayTensorSnd (ball.{u} atomPoint) B) := by
  have : IsIso (isTerminalBallAtomPoint.from (ball.{u} atomPoint)) :=
    isIso_of_isTerminal isTerminalBallAtomPoint isTerminalBallAtomPoint _
  have : IsIso (X := ((ball.{u} atomPoint, B) : DiagSet.{u} × DiagSet.{u}))
      (Y := (ball.{u} atomPoint, B)) (isTerminalBallAtomPoint.from _, 𝟙 B) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  exact inferInstanceAs (IsIso (grayTensorBifunctor.map _ ≫ _))

instance isIso_grayTensorSnd_ballAtomSimplex_zero (B : DiagSet.{u}) :
    IsIso (grayTensorSnd (ball.{u} (atomSimplex 0)) B) :=
  isIso_grayTensorSnd_ballAtomSimplexZero B

@[reassoc]
private theorem inv_grayTensorSnd_naturality {B B' : DiagSet.{u}} (g : B ⟶ B') :
    g ≫ inv (grayTensorSnd (ball.{u} atomPoint) B') =
      inv (grayTensorSnd (ball.{u} atomPoint) B) ≫
        (grayTensorLeft (ball.{u} atomPoint)).map g := by
  rw [IsIso.comp_inv_eq, Category.assoc, grayTensorLeft_map_grayTensorSnd, IsIso.inv_hom_id_assoc]

section FixedEnds

variable {x y : X.Vertex}

private theorem isFixedEnds_ballAtomSimplexZero_iff
    (G : grayTensor (ball.{u} atomPoint) (ball.{u} (atomSimplex 1)) ⟶ X) :
    IsFixedEnds x y G ↔
      intervalSource ≫ inv (grayTensorSnd (ball.{u} atomPoint) _) ≫ G =
          vertexHom x ∧
        intervalTarget ≫ inv (grayTensorSnd (ball.{u} atomPoint) _) ≫ G =
          vertexHom y := by
  simp only [IsFixedEnds, inv_grayTensorSnd_naturality_assoc, IsIso.inv_comp_eq]

private theorem δ_uliftYonedaEquiv (e : ball.{u} (atomSimplex 1) ⟶ X) (i : Fin 2) :
    (DiagSet.toSSet.obj X).δ i (uliftYonedaEquiv e : diagram X (atomSimplex 1)) =
      uliftYonedaEquiv (uliftYoneda.map (simplexHom (SimplexCategory.δ i).toOrderHom) ≫ e) :=
  uliftYonedaEquiv_naturality (F := X) e (simplexHom (SimplexCategory.δ i).toOrderHom).op

private theorem uliftYonedaEquiv_symm_δ (e : (DiagSet.toSSet.obj X) _⦋1⦌) (i : Fin 2) :
    uliftYoneda.map (simplexHom (SimplexCategory.δ i).toOrderHom) ≫
        (uliftYonedaEquiv.symm (e : diagram X (atomSimplex 1)) : ball.{u} (atomSimplex 1) ⟶ X) =
      vertexHom (X.vertexEquivSSet.symm ((DiagSet.toSSet.obj X).δ i e)) :=
  (uliftYonedaEquiv_symm_map (F := X) (simplexHom (SimplexCategory.δ i).toOrderHom).op e).symm

private noncomputable def edgeEquivIntervalHom (x y : X.Vertex) :
    SSet.Edge (X.vertexEquivSSet x) (X.vertexEquivSSet y) ≃
      {e : ball.{u} (atomSimplex 1) ⟶ X //
      intervalSource ≫ e = vertexHom x ∧
        intervalTarget ≫ e = vertexHom y} where
  toFun f := ⟨uliftYonedaEquiv.symm (f.edge : diagram X (atomSimplex 1)),
    (uliftYonedaEquiv_symm_δ f.edge 1).trans (congrArg _ f.src_eq),
    (uliftYonedaEquiv_symm_δ f.edge 0).trans (congrArg _ f.tgt_eq)⟩
  invFun e := SSet.Edge.mk (uliftYonedaEquiv e.1 : diagram X (atomSimplex 1))
    ((δ_uliftYonedaEquiv e.1 1).trans ((congrArg uliftYonedaEquiv e.2.1).trans
      (Equiv.apply_symm_apply _ _)))
    ((δ_uliftYonedaEquiv e.1 0).trans ((congrArg uliftYonedaEquiv e.2.2).trans
      (Equiv.apply_symm_apply _ _)))
  left_inv _ := SSet.Edge.ext (Equiv.apply_symm_apply _ _)
  right_inv _ := Subtype.ext (Equiv.symm_apply_apply _ _)

end FixedEnds

noncomputable def DiagSet.mappingSpaceVerticesEquiv (x y : X.Vertex) :
    DiagSet.Vertex (X.mappingSpace x y).toFunctor ≃ X.Edge x y :=
  ((Equiv.subtypeEquiv (p := fun F => F ∈ (X.mappingSpace x y).obj (op (atomSimplex 0)))
      (q := fun G => IsFixedEnds x y G)
      (grayHomRightCellEquiv (ball.{u} (atomSimplex 1)) X (atomSimplex 0)) fun _ => Iff.rfl).trans
    ((Equiv.subtypeEquiv
      { toFun G := inv (grayTensorSnd (ball.{u} atomPoint) _) ≫ G
        invFun e := grayTensorSnd (ball.{u} atomPoint) _ ≫ e
        left_inv G := IsIso.hom_inv_id_assoc _ G
        right_inv e := IsIso.inv_hom_id_assoc _ e }
      fun G => isFixedEnds_ballAtomSimplexZero_iff G).trans
        (edgeEquivIntervalHom x y).symm)).trans X.edgeEquivSSet.symm

theorem DiagSet.mappingSpaceVerticesEquiv_edge (x y : X.Vertex)
    (v : DiagSet.Vertex (X.mappingSpace x y).toFunctor) :
    (X.edgeEquivSSet (X.mappingSpaceVerticesEquiv x y v)).edge = uliftYonedaEquiv
      (inv (grayTensorSnd (ball.{u} atomPoint) (ball (atomSimplex 1))) ≫
        grayHomRightCellEquiv (ball.{u} (atomSimplex 1)) X (atomSimplex 0) v.1) :=
  congrArg SSet.Edge.edge (Equiv.apply_symm_apply _ _)

theorem DiagSet.mappingSpaceHomEquiv_vertexHom {X : DiagSet.{u}}
    (x y : X.Vertex) (v : DiagSet.Vertex (X.mappingSpace x y).toFunctor) :
    (X.mappingSpaceHomEquiv x y _ (vertexHom v)).1 =
      grayHomRightCellEquiv (ball.{u} (atomSimplex 1)) X (atomSimplex 0) v.1 := by
  have h := grayHomRightCellEquiv_homEquiv_app (ball.{u} (atomSimplex 1)) _ X
    (X.mappingSpaceHomEquiv x y _ (vertexHom v)).1 atomPoint (uliftYonedaEquiv (𝟙 _))
  dsimp only [DiagSet.mappingSpaceHomEquiv, Equiv.coe_fn_mk] at h ⊢
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply, CategoryTheory.Functor.map_id,
    Category.id_comp] at h
  rw [← h]
  exact congrArg (fun c => grayHomRightCellEquiv _ X _ ((X.mappingSpace x y).ι.app _ c))
    (uliftYonedaEquiv_vertexHom (X := (X.mappingSpace x y).toFunctor) v)

theorem IsFixedEnds.map {x y : X.Vertex} {A : DiagSet.{u}}
    {F : grayTensor A (ball.{u} (atomSimplex 1)) ⟶ X} (hF : IsFixedEnds x y F) (f : X ⟶ Y) :
    IsFixedEnds (x.map f) (y.map f) (F ≫ f) := by
  constructor
  · rw [← Category.assoc, hF.1, Category.assoc]
    exact congrArg _ (vertexHom_comp x f)
  · rw [← Category.assoc, hF.2, Category.assoc]
    exact congrArg _ (vertexHom_comp y f)

noncomputable def DiagSet.mappingSpaceMap (f : X ⟶ Y) (x y : X.Vertex) :
    (X.mappingSpace x y).toFunctor ⟶
      (Y.mappingSpace (x.map f) (y.map f)).toFunctor :=
  Subfunctor.lift ((X.mappingSpace x y).ι ≫ (grayHomRight (ball.{u} (atomSimplex 1))).map f) <| by
    rintro ⟨U⟩ _ ⟨F, rfl⟩
    exact F.2.map f

@[reassoc (attr := simp)]
theorem DiagSet.mappingSpaceMap_ι (f : X ⟶ Y) (x y : X.Vertex) :
    X.mappingSpaceMap f x y ≫ (Y.mappingSpace _ _).ι =
      (X.mappingSpace x y).ι ≫ (grayHomRight (ball.{u} (atomSimplex 1))).map f :=
  Subfunctor.lift_ι _ _

theorem DiagSet.mappingSpaceVerticesEquiv_map (f : X ⟶ Y) (x y : X.Vertex)
    (v : DiagSet.Vertex (X.mappingSpace x y).toFunctor) :
    Y.edgeEquivSSet (Y.mappingSpaceVerticesEquiv _ _ (v.map (X.mappingSpaceMap f x y))) =
      (X.edgeEquivSSet (X.mappingSpaceVerticesEquiv x y v)).map (DiagSet.toSSet.map f) :=
  SSet.Edge.ext <| (DiagSet.mappingSpaceVerticesEquiv_edge _ _ _).trans
    (congrArg ((DiagSet.toSSet.map f).app _) (DiagSet.mappingSpaceVerticesEquiv_edge x y v)).symm

@[simp]
theorem DiagSet.mappingSpaceMap_id (x y : X.Vertex) :
    X.mappingSpaceMap (𝟙 X) x y = 𝟙 _ :=
  NatTrans.ext (funext fun U => ConcreteCategory.hom_ext _ _ fun F => Subtype.ext
    (congrArg (fun φ : (grayHomRight (ball.{u} (atomSimplex 1))).obj X ⟶ _ => φ.app U F.1)
      ((grayHomRight _).map_id X)))

theorem DiagSet.mappingSpaceMap_comp {Z : DiagSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x y : X.Vertex) :
    X.mappingSpaceMap (f ≫ g) x y = X.mappingSpaceMap f x y ≫ Y.mappingSpaceMap g _ _ :=
  NatTrans.ext (funext fun U => ConcreteCategory.hom_ext _ _ fun F => Subtype.ext
    (congrArg (fun φ : (grayHomRight (ball.{u} (atomSimplex 1))).obj X ⟶ _ => φ.app U F.1)
      ((grayHomRight _).map_comp f g)))

theorem DiagSet.mappingSpaceHomEquiv_mappingSpaceMap {X Y : DiagSet.{u}} (p : X ⟶ Y)
    (x y : X.Vertex) {T : DiagSet.{u}}
    (t : T ⟶ (X.mappingSpace x y).toFunctor) :
    (Y.mappingSpaceHomEquiv _ _ T (t ≫ X.mappingSpaceMap p x y)).1 =
      (X.mappingSpaceHomEquiv x y T t).1 ≫ p := by
  dsimp only [DiagSet.mappingSpaceHomEquiv, Equiv.coe_fn_mk]
  rw [Category.assoc, DiagSet.mappingSpaceMap_ι, ← Category.assoc,
    Adjunction.homEquiv_naturality_right_symm]

noncomputable def DiagSet.mappingSpaceId (X : DiagSet.{u}) (x : X.Vertex) :
    ball.{u} atomPoint ⟶ (X.mappingSpace x x).toFunctor :=
  vertexHom ((X.mappingSpaceVerticesEquiv x x).symm (DiagSet.Edge.id x))

theorem DiagSet.mappingSpaceHomEquiv_mappingSpaceId (X : DiagSet.{u})
    (x : X.Vertex) (T : DiagSet.{u}) :
    (X.mappingSpaceHomEquiv x x T (isTerminalBallAtomPoint.from T ≫ X.mappingSpaceId x)).1 =
      grayTensorSnd T (ball.{u} (atomSimplex 1)) ≫ isTerminalBallAtomPoint.from _ ≫
        vertexHom x := by
  have h : grayHomRightCellEquiv (ball.{u} (atomSimplex 1)) X (atomSimplex 0)
        ((X.mappingSpaceVerticesEquiv x x).symm
          (X.edgeEquivSSet.symm (SSet.Edge.id (X.vertexEquivSSet x)))).1 =
      grayTensorSnd (ball.{u} atomPoint) (ball.{u} (atomSimplex 1)) ≫
        isTerminalBallAtomPoint.from _ ≫ vertexHom x := by
    refine (IsIso.inv_comp_eq (grayTensorSnd (ball.{u} atomPoint) (ball.{u} (atomSimplex 1)))).1
      (((Equiv.eq_symm_apply _).2 ((DiagSet.mappingSpaceVerticesEquiv_edge x x _).symm.trans
        ((congrArg (fun e => (X.edgeEquivSSet e).edge) (Equiv.apply_symm_apply _ _)).trans
          ((congrArg SSet.Edge.edge (Equiv.apply_symm_apply _ _)).trans
            (SSet.Edge.id_edge _))))).trans ?_)
    exact (uliftYonedaEquiv_symm_map (F := X)
      (simplexHom (SimplexCategory.σ (n := 0) 0).toOrderHom).op (X.vertexEquivSSet x)).trans
        (congrArg (· ≫ vertexHom x) (isTerminalBallAtomPoint.hom_ext _ _))
  rw [DiagSet.mappingSpaceHomEquiv_comp, DiagSet.mappingSpaceId,
    DiagSet.mappingSpaceHomEquiv_vertexHom, ← DiagSet.edgeEquivSSet_symm_id x, h,
    ← Category.assoc,
    grayTensorRight_map_grayTensorSnd]

theorem DiagSet.mappingSpaceId_comp_mappingSpaceMap {X Y : DiagSet.{u}} (f : X ⟶ Y)
    (x : X.Vertex) :
    X.mappingSpaceId x ≫ X.mappingSpaceMap f x x = Y.mappingSpaceId (x.map f) := by
  simp only [DiagSet.mappingSpaceId, ← DiagSet.edgeEquivSSet_symm_id]
  refine (vertexHom_comp _ _).trans (congrArg vertexHom
    (((Y.mappingSpaceVerticesEquiv _ _).trans Y.edgeEquivSSet).injective ?_))
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (DiagSet.mappingSpaceVerticesEquiv_map f x x _).trans
    ((congrArg (SSet.Edge.map · _) ((congrArg X.edgeEquivSSet (Equiv.apply_symm_apply _ _)).trans
      (Equiv.apply_symm_apply _ _))).trans (SSet.Edge.map_id _ _))

noncomputable def grayHomRestrict {A B : DiagSet.{u}} (i : A ⟶ B) :
    grayHomRight B ⟶ grayHomRight A where
  app Z :=
    { app U := ↾fun F => (grayHomRightCellEquiv A Z U.unop).symm
        ((grayTensorLeft (ball U.unop)).map i ≫ grayHomRightCellEquiv B Z U.unop F)
      naturality U V g := ConcreteCategory.hom_ext _ _ fun F =>
        (grayHomRightCellEquiv A Z V.unop).injective <| by
          rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
          refine (Equiv.apply_symm_apply _ _).trans ?_
          refine Eq.trans ?_ ((grayHomRightCellEquiv_map A Z g.unop _).trans
            (congrArg _ (Equiv.apply_symm_apply _ _))).symm
          refine (congrArg _ (grayHomRightCellEquiv_map B Z g.unop F)).trans ?_
          rw [← Category.assoc, grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc] }
  naturality Z Z' f := NatTrans.ext (funext fun U => ConcreteCategory.hom_ext _ _ fun F =>
        (grayHomRightCellEquiv A Z' U.unop).injective <| by
          rw [NatTrans.comp_app, NatTrans.comp_app, ConcreteCategory.comp_apply,
            ConcreteCategory.comp_apply]
          refine (Equiv.apply_symm_apply _ _).trans ?_
          refine Eq.trans ?_ ((grayHomRightCellEquiv_map_app A f U.unop _).trans
            (congrArg (· ≫ f) (Equiv.apply_symm_apply _ _))).symm
          exact (congrArg _ (grayHomRightCellEquiv_map_app B f U.unop F)).trans
            (Category.assoc _ _ _).symm)

theorem grayHomRightCellEquiv_grayHomRestrict {A B : DiagSet.{u}} (i : A ⟶ B) (Z : DiagSet.{u})
    (U : Atom) (F : diagram ((grayHomRight B).obj Z) U) :
    grayHomRightCellEquiv A Z U (((grayHomRestrict i).app Z).app (op U) F) =
      (grayTensorLeft (ball U)).map i ≫ grayHomRightCellEquiv B Z U F :=
  Equiv.apply_symm_apply _ _

private theorem grayHomRight_natTrans_ext {B : DiagSet.{u}} {P : DiagSet.{u} ⥤ DiagSet.{u}}
    {α β : P ⟶ grayHomRight B}
    (h : ∀ (Z : DiagSet.{u}) (U : Atom) (F : diagram (P.obj Z) U),
      grayHomRightCellEquiv B Z U ((α.app Z).app (op U) F) =
        grayHomRightCellEquiv B Z U ((β.app Z).app (op U) F)) :
    α = β :=
  NatTrans.ext (funext fun Z => NatTrans.ext (funext fun U => ConcreteCategory.hom_ext _ _ fun F =>
    (grayHomRightCellEquiv B Z U.unop).injective (h Z U.unop F)))

@[simp]
theorem grayHomRestrict_id (B : DiagSet.{u}) : grayHomRestrict (𝟙 B) = 𝟙 (grayHomRight B) :=
  grayHomRight_natTrans_ext fun Z U F => by
    rw [grayHomRightCellEquiv_grayHomRestrict, CategoryTheory.Functor.map_id, Category.id_comp]
    rfl

theorem grayHomRestrict_comp {A B C : DiagSet.{u}} (i : A ⟶ B) (j : B ⟶ C) :
    grayHomRestrict (i ≫ j) = grayHomRestrict j ≫ grayHomRestrict i :=
  grayHomRight_natTrans_ext fun Z U F => by
    rw [grayHomRightCellEquiv_grayHomRestrict, NatTrans.comp_app, NatTrans.comp_app,
      ConcreteCategory.comp_apply, grayHomRightCellEquiv_grayHomRestrict,
      grayHomRightCellEquiv_grayHomRestrict, Functor.map_comp, Category.assoc]

@[simps]
noncomputable def grayHomRightBifunctor : DiagSet.{u}ᵒᵖ ⥤ DiagSet.{u} ⥤ DiagSet.{u} where
  obj B := grayHomRight B.unop
  map i := grayHomRestrict i.unop
  map_comp i j := grayHomRestrict_comp j.unop i.unop

theorem grayHomLeftCellEquiv_map (A Z : DiagSet.{u}) {V W : Atom} (g : W ⟶ V)
    (F : diagram ((grayHomLeft A).obj Z) V) :
    grayHomLeftCellEquiv A Z W (((grayHomLeft A).obj Z).map g.op F) =
      (grayTensorLeft A).map (uliftYoneda.map g) ≫ grayHomLeftCellEquiv A Z V F :=
  rfl

theorem grayHomLeftCellEquiv_map_app (A : DiagSet.{u}) {Z Z' : DiagSet.{u}} (f : Z ⟶ Z')
    (V : Atom) (F : diagram ((grayHomLeft A).obj Z) V) :
    grayHomLeftCellEquiv A Z' V (((grayHomLeft A).map f).app (op V) F) =
      grayHomLeftCellEquiv A Z V F ≫ f :=
  rfl

theorem grayHomLeftCellEquiv_homEquiv_app (A T Z : DiagSet.{u})
    (F : grayTensor A T ⟶ Z) (V : Atom) (t : diagram T V) :
    grayHomLeftCellEquiv A Z V (((grayTensorLeftAdjunction A).homEquiv T Z F).app (op V) t) =
      (grayTensorLeft A).map (uliftYonedaEquiv.symm t) ≫ F :=
  rfl

noncomputable def grayHomLeftRestrict {A B : DiagSet.{u}} (i : A ⟶ B) :
    grayHomLeft B ⟶ grayHomLeft A where
  app Z :=
    { app V := ↾fun F => (grayHomLeftCellEquiv A Z V.unop).symm
        ((grayTensorRight (ball V.unop)).map i ≫ grayHomLeftCellEquiv B Z V.unop F)
      naturality V W g := ConcreteCategory.hom_ext _ _ fun F =>
        (grayHomLeftCellEquiv A Z W.unop).injective <| by
          rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
          refine (Equiv.apply_symm_apply _ _).trans ?_
          refine Eq.trans ?_ ((grayHomLeftCellEquiv_map A Z g.unop _).trans
            (congrArg _ (Equiv.apply_symm_apply _ _))).symm
          refine (congrArg _ (grayHomLeftCellEquiv_map B Z g.unop F)).trans ?_
          rw [← Category.assoc, ← grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc] }
  naturality Z Z' f := NatTrans.ext (funext fun V => ConcreteCategory.hom_ext _ _ fun F =>
        (grayHomLeftCellEquiv A Z' V.unop).injective <| by
          rw [NatTrans.comp_app, NatTrans.comp_app, ConcreteCategory.comp_apply,
            ConcreteCategory.comp_apply]
          refine (Equiv.apply_symm_apply _ _).trans ?_
          refine Eq.trans ?_ ((grayHomLeftCellEquiv_map_app A f V.unop _).trans
            (congrArg (· ≫ f) (Equiv.apply_symm_apply _ _))).symm
          exact (congrArg _ (grayHomLeftCellEquiv_map_app B f V.unop F)).trans
            (Category.assoc _ _ _).symm)

theorem grayHomLeftCellEquiv_grayHomLeftRestrict {A B : DiagSet.{u}} (i : A ⟶ B)
    (Z : DiagSet.{u}) (V : Atom) (F : diagram ((grayHomLeft B).obj Z) V) :
    grayHomLeftCellEquiv A Z V (((grayHomLeftRestrict i).app Z).app (op V) F) =
      (grayTensorRight (ball V)).map i ≫ grayHomLeftCellEquiv B Z V F :=
  Equiv.apply_symm_apply _ _

private theorem grayHomLeft_natTrans_ext {A : DiagSet.{u}} {P : DiagSet.{u} ⥤ DiagSet.{u}}
    {α β : P ⟶ grayHomLeft A}
    (h : ∀ (Z : DiagSet.{u}) (V : Atom) (F : diagram (P.obj Z) V),
      grayHomLeftCellEquiv A Z V ((α.app Z).app (op V) F) =
        grayHomLeftCellEquiv A Z V ((β.app Z).app (op V) F)) :
    α = β :=
  NatTrans.ext (funext fun Z => NatTrans.ext (funext fun V => ConcreteCategory.hom_ext _ _ fun F =>
    (grayHomLeftCellEquiv A Z V.unop).injective (h Z V.unop F)))

@[simp]
theorem grayHomLeftRestrict_id (B : DiagSet.{u}) :
    grayHomLeftRestrict (𝟙 B) = 𝟙 (grayHomLeft B) :=
  grayHomLeft_natTrans_ext fun Z V F => by
    rw [grayHomLeftCellEquiv_grayHomLeftRestrict, CategoryTheory.Functor.map_id, Category.id_comp]
    rfl

theorem grayHomLeftRestrict_comp {A B C : DiagSet.{u}} (i : A ⟶ B) (j : B ⟶ C) :
    grayHomLeftRestrict (i ≫ j) = grayHomLeftRestrict j ≫ grayHomLeftRestrict i :=
  grayHomLeft_natTrans_ext fun Z V F => by
    rw [grayHomLeftCellEquiv_grayHomLeftRestrict, NatTrans.comp_app, NatTrans.comp_app,
      ConcreteCategory.comp_apply, grayHomLeftCellEquiv_grayHomLeftRestrict,
      grayHomLeftCellEquiv_grayHomLeftRestrict, Functor.map_comp, Category.assoc]

@[simps]
noncomputable def grayHomLeftBifunctor : DiagSet.{u}ᵒᵖ ⥤ DiagSet.{u} ⥤ DiagSet.{u} where
  obj A := grayHomLeft A.unop
  map i := grayHomLeftRestrict i.unop
  map_comp i j := grayHomLeftRestrict_comp j.unop i.unop

noncomputable abbrev intervalBoundary : DiagSet.{u} :=
  ball.{u} atomPoint ⨿ ball.{u} atomPoint

noncomputable abbrev intervalBoundaryι : intervalBoundary.{u} ⟶ ball.{u} (atomSimplex 1) :=
  coprod.desc intervalSource intervalTarget

theorem intervalSource_app_ne (U : Atomᵒᵖ) (t t' : (ball.{u} (atomSimplex 0)).obj U) :
    intervalSource.app U t ≠ intervalTarget.app U t' := by
  intro h
  have hs : intervalSource.app U t =
      (uliftYoneda.map (simplexHom (SimplexCategory.δ (1 : Fin 2)).toOrderHom)).app U t := rfl
  have ht : intervalTarget.app U t' =
      (uliftYoneda.map (simplexHom (SimplexCategory.δ (0 : Fin 2)).toOrderHom)).app U t' := rfl
  rw [hs, ht] at h
  have h' := congrArg (fun c : ULift (U.unop ⟶ atomSimplex 1) =>
    atomSimplexVertices 1 (c.down U.unop.top)) h
  simp only [uliftYoneda_map_app, TypeCat.ofHom_apply, ConcreteCategory.comp_apply] at h'
  rw [eq_top_atomSimplex_zero (ConcreteCategory.hom t.down _),
    eq_top_atomSimplex_zero (ConcreteCategory.hom t'.down _), atomSimplexVertices_simplexHom,
    atomSimplexVertices_simplexHom, atomSimplexVertices_top] at h'
  exact absurd h' (by decide)

theorem exists_intervalBoundaryι_app_eq (a : (ball.{u} (atomSimplex 1)).Vertex) :
    ∃ v : intervalBoundary.{u}.Vertex, v.map intervalBoundaryι = a := by
  obtain ⟨g⟩ := a
  have hg : simplexFunctor.map (simplexFunctor.preimage (X := ⦋0⦌) (Y := ⦋1⦌) g) = g :=
    simplexFunctor.map_preimage (X := ⦋0⦌) (Y := ⦋1⦌) g
  have hσ : ∀ σ : ⦋0⦌ ⟶ ⦋1⦌, σ = SimplexCategory.δ 1 ∨ σ = SimplexCategory.δ 0 := by
    intro σ
    rcases Fin.exists_fin_two.1 ⟨σ.toOrderHom 0, rfl⟩ with h | h
    · refine Or.inl (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun j => ?_)))
      obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) j 0
      exact h.trans (by decide)
    · refine Or.inr (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun j => ?_)))
      obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) j 0
      exact h.trans (by decide)
  let x₀ : (ball.{u} atomPoint).obj (op (atomSimplex 0)) := ⟨𝟙 _⟩
  rcases hσ (simplexFunctor.preimage (X := ⦋0⦌) (Y := ⦋1⦌) g) with h | h
  · have e : (coprod.inl ≫ intervalBoundaryι.{u}).app (op (atomSimplex 0)) x₀ =
        intervalSource.app (op (atomSimplex 0)) x₀ :=
      congrArg (fun k : ball.{u} atomPoint ⟶ ball.{u} (atomSimplex 1) =>
        k.app (op (atomSimplex 0)) x₀) (coprod.inl_desc _ _)
    exact ⟨(coprod.inl : ball.{u} atomPoint ⟶ intervalBoundary).app _ x₀,
      e.trans (congrArg ULift.up ((Category.id_comp _).trans
          ((congrArg simplexFunctor.map h).symm.trans hg)))⟩
  · have e : (coprod.inr ≫ intervalBoundaryι.{u}).app (op (atomSimplex 0)) x₀ =
        intervalTarget.app (op (atomSimplex 0)) x₀ :=
      congrArg (fun k : ball.{u} atomPoint ⟶ ball.{u} (atomSimplex 1) =>
        k.app (op (atomSimplex 0)) x₀) (coprod.inr_desc _ _)
    exact ⟨(coprod.inr : ball.{u} atomPoint ⟶ intervalBoundary).app _ x₀,
      e.trans (congrArg ULift.up ((Category.id_comp _).trans
          ((congrArg simplexFunctor.map h).symm.trans hg)))⟩

instance mono_intervalBoundaryι : Mono intervalBoundaryι.{u} :=
  have := isTerminalBallAtomPoint.{u}.mono_from intervalSource
  have := isTerminalBallAtomPoint.{u}.mono_from intervalTarget
  FunctorToTypes.mono_coprodDesc_of_disjoint _ _ fun U =>
    Set.disjoint_range_iff.2 (intervalSource_app_ne U)

theorem grayTensor_coprod_hom_ext (C : DiagSet.{u}) {A B Z : DiagSet.{u}}
    {φ ψ : grayTensor C (A ⨿ B) ⟶ Z}
    (h₁ : (grayTensorLeft C).map coprod.inl ≫ φ = (grayTensorLeft C).map coprod.inl ≫ ψ)
    (h₂ : (grayTensorLeft C).map coprod.inr ≫ φ = (grayTensorLeft C).map coprod.inr ≫ ψ) :
    φ = ψ :=
  (isColimitOfPreserves (grayTensorLeft C) (coprodIsCoprod A B)).hom_ext (by
    rintro ⟨⟨⟩⟩
    · exact h₁
    · exact h₂)

theorem grayTensor_sigma_hom_ext (T : DiagSet.{u}) {ι : Type} (Z : ι → DiagSet.{u})
    {Y : DiagSet.{u}}
    {φ ψ : grayTensor T (∐ Z) ⟶ Y}
    (h : ∀ k, (grayTensorLeft T).map (Sigma.ι Z k) ≫ φ = (grayTensorLeft T).map (Sigma.ι Z k) ≫ ψ) :
    φ = ψ :=
  (isColimitOfPreserves (grayTensorLeft T) (colimit.isColimit (Discrete.functor Z))).hom_ext
    fun ⟨k⟩ => h k

theorem homEquiv_comp_grayHomRestrict {A B T Z : DiagSet.{u}} (i : A ⟶ B)
    (F : grayTensor T B ⟶ Z) :
    (grayTensorRightAdjunction B).homEquiv T Z F ≫ (grayHomRestrict i).app Z =
      (grayTensorRightAdjunction A).homEquiv T Z ((grayTensorLeft T).map i ≫ F) :=
  NatTrans.ext (funext fun U => ConcreteCategory.hom_ext _ _ fun t =>
    (grayHomRightCellEquiv A Z U.unop).injective <| by
      rw [NatTrans.comp_app, ConcreteCategory.comp_apply]
      refine (grayHomRightCellEquiv_grayHomRestrict i Z U.unop _).trans ?_
      refine Eq.trans ?_ (grayHomRightCellEquiv_homEquiv_app A T Z _ U.unop t).symm
      rw [grayHomRightCellEquiv_homEquiv_app, ← Category.assoc,
        grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc])

theorem homEquiv_ball {B Z : DiagSet.{u}} {U : Atom} (F : grayTensor (ball.{u} U) B ⟶ Z) :
    (grayTensorRightAdjunction B).homEquiv _ Z F =
      uliftYonedaEquiv.symm ((grayHomRightCellEquiv B Z U).symm F) := by
  rw [Equiv.eq_symm_apply, Equiv.eq_symm_apply, ← Category.id_comp
    ((grayTensorRightAdjunction B).homEquiv _ Z F), uliftYonedaEquiv_comp,
    grayHomRightCellEquiv_homEquiv_app, Equiv.symm_apply_apply, CategoryTheory.Functor.map_id,
    Category.id_comp]

theorem isFixedEnds_iff_restrict (x y : X.Vertex) {C : DiagSet.{u}}
    (F : grayTensor C (ball.{u} (atomSimplex 1)) ⟶ X) :
    IsFixedEnds x y F ↔ (grayTensorLeft C).map intervalBoundaryι ≫ F =
      grayTensorSnd C intervalBoundary ≫ coprod.desc (vertexHom x)
        (vertexHom y) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine grayTensor_coprod_hom_ext C ?_ ?_
    · rw [← Category.assoc, ← Functor.map_comp, coprod.inl_desc, h₁, ← Category.assoc,
        grayTensorLeft_map_grayTensorSnd, Category.assoc, coprod.inl_desc]
    · rw [← Category.assoc, ← Functor.map_comp, coprod.inr_desc, h₂, ← Category.assoc,
        grayTensorLeft_map_grayTensorSnd, Category.assoc, coprod.inr_desc]
  · intro h
    constructor
    · have e := congrArg ((grayTensorLeft C).map coprod.inl ≫ ·) h
      simp only [← Category.assoc, ← Functor.map_comp, coprod.inl_desc,
        grayTensorLeft_map_grayTensorSnd] at e
      rwa [Category.assoc, coprod.inl_desc] at e
    · have e := congrArg ((grayTensorLeft C).map coprod.inr ≫ ·) h
      simp only [← Category.assoc, ← Functor.map_comp, coprod.inr_desc,
        grayTensorLeft_map_grayTensorSnd] at e
      rwa [Category.assoc, coprod.inr_desc] at e

noncomputable def DiagSet.endpointsPoint (x y : X.Vertex) :
    ball.{u} atomPoint ⟶ (grayHomRight intervalBoundary.{u}).obj X :=
  uliftYonedaEquiv.symm ((grayHomRightCellEquiv _ X atomPoint).symm
    (grayTensorSnd _ _ ≫ coprod.desc (vertexHom x) (vertexHom y)))

theorem DiagSet.grayHomRightCellEquiv_endpointsPoint (x y : X.Vertex)
    (U : Atom) (p : diagram (ball.{u} atomPoint) U) :
    grayHomRightCellEquiv _ X U ((X.endpointsPoint x y).app (op U) p) =
      grayTensorSnd _ _ ≫ coprod.desc (vertexHom x) (vertexHom y) := by
  refine (grayHomRightCellEquiv_map intervalBoundary X p.down _).trans ?_
  rw [Equiv.apply_symm_apply, ← Category.assoc, grayTensorRight_map_grayTensorSnd]

theorem DiagSet.endpointsPoint_eq_homEquiv (x y : X.Vertex) :
    X.endpointsPoint x y = (grayTensorRightAdjunction _).homEquiv _ X
      (grayTensorSnd _ _ ≫ coprod.desc (vertexHom x) (vertexHom y)) :=
  (homEquiv_ball _).symm

private theorem mem_mappingSpace_iff_restrict (x y : X.Vertex) {U : Atom}
    (F : diagram ((grayHomRight (ball.{u} (atomSimplex 1))).obj X) U)
    (p : diagram (ball.{u} atomPoint) U) :
    F ∈ (X.mappingSpace x y).obj (op U) ↔
      ((grayHomRestrict intervalBoundaryι).app X).app (op U) F =
        (X.endpointsPoint x y).app (op U) p := by
  rw [DiagSet.mem_mappingSpace_iff, isFixedEnds_iff_restrict,
    ← (grayHomRightCellEquiv _ X U).injective.eq_iff, grayHomRightCellEquiv_grayHomRestrict,
    DiagSet.grayHomRightCellEquiv_endpointsPoint]

theorem DiagSet.isPullback_mappingSpace (x y : X.Vertex) :
    IsPullback (X.mappingSpace x y).ι (isTerminalBallAtomPoint.from _)
      ((grayHomRestrict intervalBoundaryι).app X) (X.endpointsPoint x y) := by
  have w : (X.mappingSpace x y).ι ≫ (grayHomRestrict intervalBoundaryι).app X =
      isTerminalBallAtomPoint.from _ ≫ X.endpointsPoint x y :=
    NatTrans.ext (funext fun U => ConcreteCategory.hom_ext _ _ fun F =>
      (mem_mappingSpace_iff_restrict x y F.1 _).1 F.2)
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w
    (fun s => Subfunctor.lift s.fst ?_) (fun s => Subfunctor.lift_ι _ _)
    (fun s => isTerminalBallAtomPoint.hom_ext _ _) fun s m h _ =>
      (cancel_mono (X.mappingSpace x y).ι).1 (h.trans (Subfunctor.lift_ι _ _).symm))
  rintro ⟨U⟩ _ ⟨t, rfl⟩
  exact (mem_mappingSpace_iff_restrict x y _ (s.snd.app _ t)).2
    (ConcreteCategory.congr_hom (congr_app s.condition (op U)) t)

theorem DiagSet.isFibrant_mappingSpace_of_fibration (x y : X.Vertex)
    [HomotopicalAlgebra.Fibration ((DiagSet.toInfty 1).map
      ((grayHomRestrict intervalBoundaryι).app X))] :
    HomotopicalAlgebra.IsFibrant ((DiagSet.toInfty 1).obj (X.mappingSpace x y).toFunctor) := by
  have h : IsPullback (C := DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map (X.mappingSpace x y).ι)
      ((DiagSet.toInfty 1).map (isTerminalBallAtomPoint.from _))
      ((DiagSet.toInfty 1).map ((grayHomRestrict intervalBoundaryι).app X))
      ((DiagSet.toInfty 1).map (X.endpointsPoint x y)) :=
    X.isPullback_mappingSpace x y
  have hT : IsTerminal (C := DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).obj (ball atomPoint)) :=
    isTerminalBallAtomPoint
  rw [HomotopicalAlgebra.isFibrant_iff_of_isTerminal
    ((DiagSet.toInfty 1).map (isTerminalBallAtomPoint.from _)) hT,
    HomotopicalAlgebra.fibration_iff]
  exact MorphismProperty.of_isPullback h
    ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)

@[reassoc]
theorem DiagSet.endpointsPoint_comp_grayHomRight_map {X Y : DiagSet.{u}} (f : X ⟶ Y)
    (x y : X.Vertex) :
    X.endpointsPoint x y ≫ (grayHomRight intervalBoundary).map f =
      Y.endpointsPoint (x.map f) (y.map f) := by
  rw [DiagSet.endpointsPoint_eq_homEquiv, DiagSet.endpointsPoint_eq_homEquiv,
    ← Adjunction.homEquiv_naturality_right, Category.assoc, coprod.desc_comp, vertexHom_comp,
    vertexHom_comp]

instance mono_toSSet_map_mappingSpace_ι {Y : DiagSet.{u}} (p q : Y.Vertex) :
    Mono (DiagSet.toSSet.map (Y.mappingSpace p q).ι) :=
  have := Functor.preservesMonomorphisms_of_adjunction sSetDiagSetAdj.{u}
  inferInstance

theorem DiagSet.mappingSpaceVerticesEquiv_map_mappingSpaceMap (f : X ⟶ Y) (x y : X.Vertex)
    (v : DiagSet.Vertex (X.mappingSpace x y).toFunctor) :
    Y.mappingSpaceVerticesEquiv _ _ (v.map (X.mappingSpaceMap f x y)) =
      (X.mappingSpaceVerticesEquiv x y v).map f :=
  Y.edgeEquivSSet.injective ((DiagSet.mappingSpaceVerticesEquiv_map f x y v).trans
    (DiagSet.edgeEquivSSet_map _ f).symm)

private noncomputable def simplexEdgeHom (s : diagram X (atomSimplex 1)) :
    ball.{u} (atomSimplex 1) ⟶ X :=
  (uliftYonedaEquiv (X := atomSimplex 1) (F := X)).symm s

private theorem intervalSource_comp_simplexEdgeHom {x y : X.Vertex}
    (e : SSet.Edge (X.vertexEquivSSet x) (X.vertexEquivSSet y)) :
    intervalSource ≫ simplexEdgeHom e.edge = vertexHom x :=
  (uliftYonedaEquiv_symm_map (F := X) (simplexHom (SimplexCategory.δ 1).toOrderHom).op
    e.edge).symm.trans (congrArg vertexHom e.src_eq)

private theorem intervalTarget_comp_simplexEdgeHom {x y : X.Vertex}
    (e : SSet.Edge (X.vertexEquivSSet x) (X.vertexEquivSSet y)) :
    intervalTarget ≫ simplexEdgeHom e.edge = vertexHom y :=
  (uliftYonedaEquiv_symm_map (F := X) (simplexHom (SimplexCategory.δ 0).toOrderHom).op
    e.edge).symm.trans (congrArg vertexHom e.tgt_eq)

private theorem simplexEdgeHom_id (x : X.Vertex) :
    simplexEdgeHom (SSet.Edge.id (X.vertexEquivSSet x)).edge =
      isTerminalBallAtomPoint.from _ ≫ vertexHom x :=
  (uliftYonedaEquiv_symm_map (F := X) (simplexHom (SimplexCategory.σ 0).toOrderHom).op
    (X.vertexEquivSSet x)).trans
    (congrArg (· ≫ vertexHom x) (isTerminalBallAtomPoint.hom_ext _ _))

noncomputable def edgeHom {x y : X.Vertex} (e : X.Edge x y) :
    ball.{u} (atomSimplex 1) ⟶ X :=
  simplexEdgeHom (X.edgeEquivSSet e).edge

noncomputable def edgeOfHom {x y : X.Vertex}
    (f : ball.{u} (atomSimplex 1) ⟶ X) (h₀ : intervalSource ≫ f = vertexHom x)
    (h₁ : intervalTarget ≫ f = vertexHom y) : X.Edge x y :=
  X.edgeEquivSSet.symm (SSet.Edge.mk (uliftYonedaEquiv f : diagram X (atomSimplex 1))
    ((uliftYonedaEquiv_naturality (F := X) f (simplexHom (SimplexCategory.δ 1).toOrderHom).op).trans
      ((congrArg uliftYonedaEquiv h₀).trans (Equiv.apply_symm_apply _ _)))
    ((uliftYonedaEquiv_naturality (F := X) f (simplexHom (SimplexCategory.δ 0).toOrderHom).op).trans
      ((congrArg uliftYonedaEquiv h₁).trans (Equiv.apply_symm_apply _ _))))

@[simp] theorem edgeHom_edgeOfHom {x y : X.Vertex}
    (f : ball.{u} (atomSimplex 1) ⟶ X) (h₀ : intervalSource ≫ f = vertexHom x)
    (h₁ : intervalTarget ≫ f = vertexHom y) : edgeHom (edgeOfHom f h₀ h₁) = f := by
  rw [edgeHom, edgeOfHom, Equiv.apply_symm_apply]
  exact Equiv.symm_apply_apply _ _

theorem intervalSource_comp_edgeHom {x y : X.Vertex} (e : X.Edge x y) :
    intervalSource ≫ edgeHom e = vertexHom x :=
  intervalSource_comp_simplexEdgeHom (X.edgeEquivSSet e)

theorem intervalTarget_comp_edgeHom {x y : X.Vertex} (e : X.Edge x y) :
    intervalTarget ≫ edgeHom e = vertexHom y :=
  intervalTarget_comp_simplexEdgeHom (X.edgeEquivSSet e)

theorem edgeHom_id (x : X.Vertex) :
    edgeHom (DiagSet.Edge.id x) = isTerminalBallAtomPoint.from _ ≫ vertexHom x := by
  rw [edgeHom, DiagSet.edgeEquivSSet_id, simplexEdgeHom_id]

theorem edgeHom_map {x y : X.Vertex} (e : X.Edge x y) (f : X ⟶ Y) :
    edgeHom (e.map f) = edgeHom e ≫ f := by
  rw [edgeHom, DiagSet.edgeEquivSSet_map]
  exact (uliftYonedaEquiv_symm_comp (C := Atom) (X := op (atomSimplex 1))
    (X.edgeEquivSSet e).edge f).symm

theorem cell_eq_of_edgeHom_eq {x y x' y' : X.Vertex} (e : X.Edge x y) (e' : X.Edge x' y')
    (h : edgeHom e = edgeHom e') : e.cell = e'.cell := by
  have hs : X.map atomSimplexOneIsoGlobe.hom.op e.cell =
      X.map atomSimplexOneIsoGlobe.hom.op e'.cell :=
    (uliftYonedaEquiv (X := atomSimplex 1) (F := X)).symm.injective h
  have hi := congrArg (X.map atomSimplexOneIsoGlobe.inv.op) hs
  simpa only [← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id,
    Functor.map_id_apply] using hi

theorem edgeHom_injective {x y : X.Vertex} :
    Function.Injective (edgeHom (X := X) (x := x) (y := y)) := by
  intro e e' h
  apply X.edgeEquivSSet.injective
  exact SSet.Edge.ext ((uliftYonedaEquiv (X := atomSimplex 1) (F := X)).symm.injective h)

noncomputable def globeIntervalEnd (α : Bool) :
    ball.{u} atomPoint ⟶ ball.{u} (atomGlobe 1) :=
  uliftYoneda.map (atomGlobeVertex α)

noncomputable def intervalIsoGlobe :
    ball.{u} (atomSimplex 1) ≅ ball.{u} (atomGlobe 1) :=
  uliftYoneda.mapIso atomSimplexOneIsoGlobe

theorem intervalEnd_comp_intervalIsoGlobe (α : Bool) :
    cond α intervalTarget.{u} intervalSource.{u} ≫ intervalIsoGlobe.{u}.hom =
      globeIntervalEnd.{u} α := by
  have h (β : Bool) :
      uliftYoneda.{u}.map
        (simplexHom (SimplexCategory.δ (cond β 0 1 : Fin 2)).toOrderHom) ≫
        uliftYoneda.map atomSimplexOneIsoGlobe.hom =
      uliftYoneda.map (atomGlobeVertex β) :=
    (uliftYoneda.map_comp _ _).symm.trans
      (congrArg uliftYoneda.map (simplexHom_δ_comp_atomSimplexOneIsoGlobe_hom β))
  cases α with
  | false => exact h false
  | true => exact h true

noncomputable def globeEdgeHom {x y : X.Vertex} (e : X.Edge x y) :
    ball.{u} (atomGlobe 1) ⟶ X :=
  uliftYonedaEquiv.symm e.cell

theorem globeIntervalEnd_comp_globeEdgeHom {x y : X.Vertex} (e : X.Edge x y)
    (α : Bool) : globeIntervalEnd α ≫ globeEdgeHom e = vertexHom (cond α y x) := by
  cases α <;> exact (uliftYonedaEquiv_symm_map (F := X) _ e.cell).symm.trans
    (congrArg vertexHom (by first | exact e.src_eq | exact e.tgt_eq))

theorem intervalIsoGlobe_hom_comp_globeEdgeHom {x y : X.Vertex} (e : X.Edge x y) :
    intervalIsoGlobe.hom ≫ globeEdgeHom e = edgeHom e :=
  (uliftYonedaEquiv_symm_map (F := X) atomSimplexOneIsoGlobe.hom.op e.cell).symm

end Atoms.Diagrammatic
