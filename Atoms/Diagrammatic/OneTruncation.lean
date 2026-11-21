import Atoms.Diagrammatic.NativeOneTruncation
import Atoms.Diagrammatic.SimplicialSeedQuotient
import Atoms.ForMathlib.CategoryTheory.Comma.Arrow

open CategoryTheory Simplicial Opposite
open Atoms.Shape Atoms.Diagrammatic.PastingDiagram
open scoped Atoms.Diagrammatic.SimplicialSeedQuotient

universe u

namespace Atoms.Diagrammatic

variable {X Y Z : DiagSet.{u}}

def categoricalNerve : Cat.{u, u} ⥤ DiagSet.{u} where
  obj C :=
    { obj U := OneTruncation (ball.{u} U.unop) ⥤ C
      map g := ↾fun F => (oneTruncation.map (uliftYoneda.map g.unop)).toFunctor ⋙ F
      map_id U := by
        ext F
        change (oneTruncation.map (uliftYoneda.map (𝟙 U.unop))).toFunctor ⋙ F = F
        rw [uliftYoneda.map_id, oneTruncation.map_id]
        rfl
      map_comp g h := by
        ext F
        change (oneTruncation.map (uliftYoneda.map (h.unop ≫ g.unop))).toFunctor ⋙ F =
          (oneTruncation.map (uliftYoneda.map h.unop)).toFunctor ⋙
            (oneTruncation.map (uliftYoneda.map g.unop)).toFunctor ⋙ F
        rw [uliftYoneda.map_comp, oneTruncation.map_comp]
        rfl }
  map G := { app U := ↾fun F => F ⋙ G.toFunctor }

theorem categoricalNerve_obj_obj (C : Cat.{u, u}) (U : Atom) :
    (categoricalNerve.obj C).obj (op U) = (OneTruncation (ball.{u} U) ⥤ C) :=
  rfl

private def taut (U : Atom) : diagram (ball.{u} U) U := uliftYonedaEquiv (𝟙 (ball.{u} U))

namespace OneTruncation

private noncomputable def vertexMap {k n : ℕ}
    (c : (DiagSet.toSSet.obj (ball.{u} (atomSimplex n))) _⦋k⦌) : ⦋k⦌ ⟶ ⦋n⦌ :=
  simplexFunctor.preimage c.down

private theorem map_vertexMap {k n : ℕ}
    (c : (DiagSet.toSSet.obj (ball.{u} (atomSimplex n))) _⦋k⦌) :
    simplexFunctor.map (vertexMap c) = c.down :=
  simplexFunctor.map_preimage _

private theorem vertexMap_injective {k n : ℕ} {c c' :
    (DiagSet.toSSet.obj (ball.{u} (atomSimplex n))) _⦋k⦌} (h : vertexMap c = vertexMap c') :
    c = c' :=
  ULift.ext _ _ ((map_vertexMap c).symm.trans ((congrArg simplexFunctor.map h).trans
    (map_vertexMap c')))

private theorem vertexMap_map {k m n : ℕ} (g : ⦋k⦌ ⟶ ⦋m⦌)
    (c : (DiagSet.toSSet.obj (ball.{u} (atomSimplex n))) _⦋m⦌) :
    vertexMap ((DiagSet.toSSet.obj (ball.{u} (atomSimplex n))).map g.op c) =
      g ≫ vertexMap c :=
  simplexFunctor.map_injective ((map_vertexMap _).trans (by
    rw [Functor.map_comp, map_vertexMap]
    rfl))

private theorem vertexMap_comp {k m n : ℕ} (g : ⦋m⦌ ⟶ ⦋n⦌)
    (c : (DiagSet.toSSet.obj (ball.{u} (atomSimplex m))) _⦋k⦌) :
    vertexMap (ULift.up (c.down ≫ simplexFunctor.map g) :
      (DiagSet.toSSet.obj (ball.{u} (atomSimplex n))) _⦋k⦌) = vertexMap c ≫ g :=
  simplexFunctor.map_injective ((map_vertexMap _).trans (by
    rw [Functor.map_comp, map_vertexMap]
    rfl))

private theorem vertexMap_taut (n : ℕ) :
    vertexMap (n := n) (taut.{u} (atomSimplex n)) = 𝟙 _ :=
  simplexFunctor.map_injective ((map_vertexMap _).trans (simplexFunctor.map_id _).symm)

private theorem vertexMap_le {n : ℕ}
    {x y : (DiagSet.toSSet.obj (ball.{u} (atomSimplex n))) _⦋0⦌} (e : SSet.Edge x y) :
    (vertexMap x).toOrderHom 0 ≤ (vertexMap y).toOrderHom 0 := by
  rw [(congrArg vertexMap e.src_eq).symm.trans (vertexMap_map _ _),
    (congrArg vertexMap e.tgt_eq).symm.trans (vertexMap_map _ _)]
  exact (vertexMap e.edge).toOrderHom.monotone (by decide)

noncomputable def toFin (n : ℕ) : OneTruncation (ball.{u} (atomSimplex n)) ⥤ Fin (n + 1) :=
  Interpretation.lift ⟨fun x =>
    (vertexMap (k := 0) (x : (DiagSet.toSSet.obj (ball.{u} (atomSimplex n))) _⦋0⦌)).toOrderHom 0,
    fun e => homOfLE (vertexMap_le ((ball.{u} (atomSimplex n)).edgeEquivSSet e))⟩
    ⟨fun _ => Subsingleton.elim _ _, by intros; exact Subsingleton.elim _ _⟩

private theorem functor_ext_of_subsingleton {D : Type*} [Category* D]
    [∀ a b : D, Subsingleton (a ⟶ b)] {F G : OneTruncation X ⥤ D}
    (h : ∀ x, F.obj (mk x) = G.obj (mk x)) : F = G :=
  functor_ext fun x y _ => Arrow.ext (h x) (h y) (Subsingleton.elim _ _)

theorem oneTruncation_map_comp_toFin {m n : ℕ} (g : ⦋m⦌ ⟶ ⦋n⦌) :
    (oneTruncation.map (uliftYoneda.map (simplexFunctor.map g))).toFunctor ⋙ toFin.{u} n =
      toFin.{u} m ⋙ (SimplexCategory.toCat.map g).toFunctor :=
  functor_ext_of_subsingleton fun x =>
    congrArg (fun φ : ⦋0⦌ ⟶ ⦋n⦌ => φ.toOrderHom 0) (vertexMap_comp g x)

end OneTruncation

section Adjunction

variable {C : Cat.{u, u}}

private theorem map_down_taut_map {m n : ℕ} (g : ⦋m⦌ ⟶ ⦋n⦌) (c : (DiagSet.toSSet.obj X) _⦋n⦌) :
    X.map (((DiagSet.toSSet.obj (ball.{u} (atomSimplex n))).map g.op
      (taut (atomSimplex n) : (DiagSet.toSSet.obj (ball.{u} (atomSimplex n))) _⦋n⦌)).down).op c =
      (DiagSet.toSSet.obj X).map g.op c := by
  change X.map (simplexFunctor.map g ≫ 𝟙 _).op c = X.map (simplexFunctor.map g).op c
  rw [Category.comp_id]

private theorem app_map (F : X ⟶ categoricalNerve.obj C) {U V : Atom} (g : U ⟶ V)
    (c : diagram X V) :
    (F.app (op U) (X.map g.op c) : OneTruncation (ball.{u} U) ⥤ C) =
      (oneTruncation.map (uliftYoneda.map g)).toFunctor ⋙
        (F.app (op V) c : OneTruncation (ball.{u} V) ⥤ C) :=
  NatTrans.naturality_apply F g.op c

private def vertexObj (F : X ⟶ categoricalNerve.obj C) (x : (DiagSet.toSSet.obj X) _⦋0⦌) : C :=
  (F.app (op (atomSimplex 0)) x : OneTruncation (ball.{u} (atomSimplex 0)) ⥤ C).obj
    (OneTruncation.mk (taut (atomSimplex 0)))

private theorem obj_mk_eq_vertexObj (F : X ⟶ categoricalNerve.obj C) {U : Atom} (c : diagram X U)
    (v : (DiagSet.toSSet.obj (ball.{u} U)) _⦋0⦌) :
    (F.app (op U) c : OneTruncation (ball.{u} U) ⥤ C).obj (OneTruncation.mk v) =
      vertexObj F (X.map (v.down : atomSimplex 0 ⟶ U).op c) := by
  refine Eq.trans ?_ (congrArg (fun G : OneTruncation (ball.{u} (atomSimplex 0)) ⥤ C =>
    G.obj (OneTruncation.mk (taut (atomSimplex 0)))) (app_map F v.down c)).symm
  change _ = (F.app (op U) c : OneTruncation (ball.{u} U) ⥤ C).obj
    (OneTruncation.mk (ULift.up (𝟙 _ ≫ v.down)))
  rw [Category.id_comp]
  rfl

private def tautEdge : SSet.Edge
    ((DiagSet.toSSet.obj (ball.{u} (atomSimplex 1))).δ 1 (taut (atomSimplex 1)))
    ((DiagSet.toSSet.obj (ball.{u} (atomSimplex 1))).δ 0 (taut (atomSimplex 1))) :=
  SSet.Edge.mk' (X := DiagSet.toSSet.obj (ball.{u} (atomSimplex 1))) (taut (atomSimplex 1))

private noncomputable def edgeMap (F : X ⟶ categoricalNerve.obj C)
    {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y) : vertexObj F x ⟶ vertexObj F y :=
  eqToHom ((congrArg (vertexObj F) ((map_down_taut_map (SimplexCategory.δ 1) _).trans
      e.src_eq)).symm.trans (obj_mk_eq_vertexObj F (e.edge : diagram X (atomSimplex 1))
        ((DiagSet.toSSet.obj (ball.{u} (atomSimplex 1))).δ 1 (taut (atomSimplex 1)))).symm) ≫
    (F.app (op (atomSimplex 1)) e.edge : OneTruncation (ball.{u} (atomSimplex 1)) ⥤ C).map
      (OneTruncation.homMk tautEdge) ≫
    eqToHom ((obj_mk_eq_vertexObj F (e.edge : diagram X (atomSimplex 1))
        ((DiagSet.toSSet.obj (ball.{u} (atomSimplex 1))).δ 0 (taut (atomSimplex 1)))).trans
      (congrArg (vertexObj F) ((map_down_taut_map (SimplexCategory.δ 0) _).trans e.tgt_eq)))

private theorem arrowMk_map_homMk_eq_edgeMap (F : X ⟶ categoricalNerve.obj C) {U : Atom}
    (c : diagram X U) {a b : (DiagSet.toSSet.obj (ball.{u} U)) _⦋0⦌} (t : SSet.Edge a b)
    {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y)
    (h : X.map (t.edge.down : atomSimplex 1 ⟶ U).op c = e.edge) :
    Arrow.mk ((F.app (op U) c : OneTruncation (ball.{u} U) ⥤ C).map (OneTruncation.homMk t)) =
      Arrow.mk (edgeMap F e) := by
  have he : Arrow.mk (edgeMap F e) = Arrow.mk
      ((F.app (op (atomSimplex 1)) e.edge : OneTruncation (ball.{u} (atomSimplex 1)) ⥤ C).map
        (OneTruncation.homMk tautEdge)) :=
    (Arrow.arrow_mk_eqToHom_comp _ _).trans (Arrow.arrow_mk_comp_eqToHom _ _)
  rw [he, ← h]
  refine Eq.trans ?_ (congrArg (fun G : OneTruncation (ball.{u} (atomSimplex 1)) ⥤ C =>
    Arrow.mk (G.map (OneTruncation.homMk tautEdge))) (app_map F t.edge.down c)).symm
  have ht : Arrow.mk (OneTruncation.homMk t) = Arrow.mk
      ((oneTruncation.map (uliftYoneda.map t.edge.down)).toFunctor.map
        (OneTruncation.homMk tautEdge)) := by
    refine Eq.trans ?_ (congrArg Arrow.mk (oneTruncation_map_map_homMk _ _)).symm
    refine OneTruncation.arrowMk_homMk_eq _ _ ?_
    change t.edge = ULift.up (𝟙 _ ≫ t.edge.down)
    rw [Category.id_comp]
    rfl
  exact congrArg (F.app (op U) c : OneTruncation (ball.{u} U) ⥤ C).mapArrow.obj ht

private theorem arrowMk_edgeMap (F : X ⟶ categoricalNerve.obj C) {x y : (DiagSet.toSSet.obj X) _⦋0⦌}
    (e : SSet.Edge x y) :
    Arrow.mk (edgeMap F e) = Arrow.mk
      ((F.app (op (atomSimplex 1)) e.edge : OneTruncation (ball.{u} (atomSimplex 1)) ⥤ C).map
        (OneTruncation.homMk tautEdge)) :=
  (Arrow.arrow_mk_eqToHom_comp _ _).trans (Arrow.arrow_mk_comp_eqToHom _ _)

private theorem edgeMap_id (F : X ⟶ categoricalNerve.obj C) (x : (DiagSet.toSSet.obj X) _⦋0⦌) :
    edgeMap F (SSet.Edge.id x) = 𝟙 _ := by
  have h := arrowMk_map_homMk_eq_edgeMap F (x : diagram X (atomSimplex 0))
    (SSet.Edge.id (X := DiagSet.toSSet.obj (ball.{u} (atomSimplex 0))) (taut (atomSimplex 0)))
    (SSet.Edge.id x) (map_down_taut_map (SimplexCategory.σ 0) x)
  refine (Arrow.mk_inj _ _).1 (h.symm.trans (congrArg Arrow.mk ?_))
  exact ((F.app (op (atomSimplex 0)) x : OneTruncation (ball.{u} (atomSimplex 0)) ⥤ C).congr_map
    (OneTruncation.homMk_id _)).trans (CategoryTheory.Functor.map_id _ _)

private noncomputable def nerveInterpretation (F : X ⟶ categoricalNerve.obj C) :
    OneTruncation.Interpretation X C where
  obj x := vertexObj F x
  map e := edgeMap F (X.edgeEquivSSet e)

private theorem freeMap_comp_freeLift (F : X ⟶ categoricalNerve.obj C) {U : Atom}
    (c : diagram X U) :
    OneTruncation.freeMap (uliftYonedaEquiv.symm c) ⋙ (nerveInterpretation F).freeLift =
      OneTruncation.quotientFunctor (ball.{u} U) ⋙
        (F.app (op U) c : OneTruncation (ball.{u} U) ⥤ C) :=
  OneTruncation.Free.functor_ext fun _ _ t =>
    (congrArg Arrow.mk ((congrArg (nerveInterpretation F).freeLift.map
      (OneTruncation.freeMap_edge _ t)).trans
        (((nerveInterpretation F).freeLift_map_edge _).trans (congrArg (edgeMap F)
          (DiagSet.edgeEquivSSet_map t (uliftYonedaEquiv.symm c)))))).trans
      ((arrowMk_map_homMk_eq_edgeMap F c _ _ rfl).symm.trans (congrArg Arrow.mk
        (congrArg (F.app (op U) c : OneTruncation (ball.{u} U) ⥤ C).map
          (OneTruncation.homMk_edgeEquivSSet t))))

private theorem nerveInterpretation_respects (F : X ⟶ categoricalNerve.obj C) :
    (nerveInterpretation F).Respects where
  unit x := (congrArg (edgeMap F) (DiagSet.edgeEquivSSet_id x)).trans (edgeMap_id F x)
  boundary {V} hV c _ _ _ _ hf hg := by
    refine OneTruncation.map_eq_map_of_isComposite_boundary _ hV c (fun hf' hg' => ?_) hf hg
    have e := congrArg (F.app (op V) c : OneTruncation (ball.{u} V) ⥤ C).map
      (OneTruncation.boundary_eq hV _ hf' hg')
    change (_ ⋙ (nerveInterpretation F).freeLift).map _ =
      (_ ⋙ (nerveInterpretation F).freeLift).map _
    rw [Functor.congr_hom (freeMap_comp_freeLift F c),
      Functor.congr_hom (freeMap_comp_freeLift F c)]
    exact congrArg (_ ≫ · ≫ _) e

private noncomputable def homEquivInvFun (F : X ⟶ categoricalNerve.obj C) :
    oneTruncation.obj X ⟶ C :=
  Cat.Hom.ofFunctor ((nerveInterpretation F).lift (nerveInterpretation_respects F))

private def homEquivToFun (G : oneTruncation.obj X ⟶ C) : X ⟶ categoricalNerve.obj C where
  app U := ↾fun c => (oneTruncation.map (uliftYonedaEquiv.symm c)).toFunctor ⋙ G.toFunctor
  naturality U V g := by
    ext c
    change (oneTruncation.map (uliftYonedaEquiv.symm (X.map g c))).toFunctor ⋙ G.toFunctor =
      (oneTruncation.map (uliftYoneda.map g.unop)).toFunctor ⋙
        (oneTruncation.map (uliftYonedaEquiv.symm c)).toFunctor ⋙ G.toFunctor
    rw [uliftYonedaEquiv_symm_map, oneTruncation.map_comp]
    rfl

private theorem arrowMk_homEquivInvFun_map_homMk (F : X ⟶ categoricalNerve.obj C)
    {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y) :
    Arrow.mk ((homEquivInvFun F).toFunctor.map (OneTruncation.homMk e)) =
      Arrow.mk ((F.app (op (atomSimplex 1)) e.edge :
        OneTruncation (ball.{u} (atomSimplex 1)) ⥤ C).map (OneTruncation.homMk tautEdge)) :=
  (congrArg Arrow.mk (((nerveInterpretation F).lift_map_globeHomMk
    (nerveInterpretation_respects F) _).trans
      (congrArg (edgeMap F) (Equiv.apply_symm_apply _ e)))).trans (arrowMk_edgeMap F e)

private theorem homEquivInvFun_homEquivToFun (G : oneTruncation.obj X ⟶ C) :
    homEquivInvFun (homEquivToFun G) = G := by
  refine Cat.Hom.ext (OneTruncation.functor_ext fun x y e => ?_)
  have ht : Arrow.mk ((oneTruncation.map (uliftYonedaEquiv.symm
      (e.edge : diagram X (atomSimplex 1)))).toFunctor.map (OneTruncation.homMk tautEdge)) =
      Arrow.mk (OneTruncation.homMk e) := by
    refine (congrArg Arrow.mk (oneTruncation_map_map_homMk _ _)).trans
      (OneTruncation.arrowMk_homMk_eq _ _ ?_)
    exact Functor.map_id_apply X (op (atomSimplex 1)) (e.edge : diagram X (atomSimplex 1))
  exact (arrowMk_homEquivInvFun_map_homMk _ e).trans (congrArg G.toFunctor.mapArrow.obj ht)

private theorem homEquivToFun_homEquivInvFun (F : X ⟶ categoricalNerve.obj C) :
    homEquivToFun (homEquivInvFun F) = F := by
  ext U c
  change (oneTruncation.map (uliftYonedaEquiv.symm c)).toFunctor ⋙
    (homEquivInvFun F).toFunctor = (F.app U c : OneTruncation (ball.{u} U.unop) ⥤ C)
  refine CategoryTheory.Quotient.lift_unique' _ _ _ ?_
  exact (congrArg (· ⋙ (homEquivInvFun F).toFunctor)
    (quotientFunctor_comp_oneTruncation_map (uliftYonedaEquiv.symm (c : diagram X U.unop)))).trans
    ((congrArg (OneTruncation.freeMap (uliftYonedaEquiv.symm (c : diagram X U.unop)) ⋙ ·)
      ((nerveInterpretation F).quotientFunctor_comp_lift (nerveInterpretation_respects F))).trans
        (freeMap_comp_freeLift F c))

noncomputable def oneTruncationAdjunction : oneTruncation.{u} ⊣ categoricalNerve.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv X C :=
        { toFun := homEquivToFun
          invFun := homEquivInvFun
          left_inv := homEquivInvFun_homEquivToFun
          right_inv := homEquivToFun_homEquivInvFun }
      homEquiv_naturality_left_symm f g := by
        refine Cat.Hom.ext (OneTruncation.functor_ext fun x y e => ?_)
        refine (arrowMk_homEquivInvFun_map_homMk _ e).trans ?_
        refine (arrowMk_homEquivInvFun_map_homMk g (e.map (DiagSet.toSSet.map f))).symm.trans ?_
        exact congrArg Arrow.mk
          (congrArg (homEquivInvFun g).toFunctor.map (oneTruncation_map_map_homMk f e).symm)
      homEquiv_naturality_right f g := rfl }

private theorem toFin_obj_mk_δ_taut (i : Fin 2) :
    (OneTruncation.toFin.{u} 1).obj (OneTruncation.mk
      ((DiagSet.toSSet.obj (ball.{u} (atomSimplex 1))).δ i (taut (atomSimplex 1)))) =
      (SimplexCategory.δ i).toOrderHom 0 :=
  congrArg (fun φ : ⦋0⦌ ⟶ ⦋1⦌ => φ.toOrderHom 0) ((OneTruncation.vertexMap_map _ _).trans
    ((congrArg _ (OneTruncation.vertexMap_taut 1)).trans (Category.comp_id _)))

private theorem arrowMk_map_fin_two {D : Type*} [Category* D] (A : ComposableArrows D 1)
    {a b : Fin 2}
    (φ : a ⟶ b) (ha : a = 0) (hb : b = 1) : Arrow.mk (A.map φ) = Arrow.mk (A.map' 0 1) := by
  subst ha hb
  rfl

theorem arrowMk_map_toFin_map_tautEdge {D : Type*} [Category* D]
    (A : ComposableArrows D 1) :
    Arrow.mk (A.map ((OneTruncation.toFin.{u} 1).map (OneTruncation.homMk tautEdge))) =
      Arrow.mk (A.map' 0 1) :=
  arrowMk_map_fin_two A _ (toFin_obj_mk_δ_taut 1) (toFin_obj_mk_δ_taut 0)

private theorem eq_δ_taut_of_vertex (v : (DiagSet.toSSet.obj (ball.{u} (atomSimplex 1))) _⦋0⦌) :
    v = (DiagSet.toSSet.obj (ball.{u} (atomSimplex 1))).δ 1 (taut (atomSimplex 1)) ∨
      v = (DiagSet.toSSet.obj (ball.{u} (atomSimplex 1))).δ 0 (taut (atomSimplex 1)) := by
  have hδ : ∀ i : Fin 2, OneTruncation.vertexMap
      ((DiagSet.toSSet.obj (ball.{u} (atomSimplex 1))).δ i (taut (atomSimplex 1))) =
        SimplexCategory.δ i := fun i =>
    (OneTruncation.vertexMap_map _ _).trans
      ((congrArg _ (OneTruncation.vertexMap_taut 1)).trans (Category.comp_id _))
  have hv : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  rcases hv ((OneTruncation.vertexMap v).toOrderHom 0) with h | h
  · refine Or.inl (OneTruncation.vertexMap_injective ((hδ 1).symm ▸ ?_))
    refine (SimplexCategory.eq_const_of_zero _).trans ?_
    rw [h]
    exact (SimplexCategory.eq_const_of_zero (SimplexCategory.δ 1)).symm
  · refine Or.inr (OneTruncation.vertexMap_injective ((hδ 0).symm ▸ ?_))
    refine (SimplexCategory.eq_const_of_zero _).trans ?_
    rw [h]
    exact (SimplexCategory.eq_const_of_zero (SimplexCategory.δ 0)).symm

private theorem eq_taut_or_eq_σ (t : (DiagSet.toSSet.obj (ball.{u} (atomSimplex 1))) _⦋1⦌) :
    t = taut (atomSimplex 1) ∨
      t = (DiagSet.toSSet.obj (ball.{u} (atomSimplex 1))).σ 0
        ((DiagSet.toSSet.obj (ball.{u} (atomSimplex 1))).δ 1 t) := by
  have key : ∀ g : ⦋1⦌ ⟶ ⦋1⦌, g = 𝟙 _ ∨ g = SimplexCategory.σ 0 ≫ SimplexCategory.δ 1 ≫ g := by
    intro g
    have hm := g.toOrderHom.monotone (show (0 : Fin 2) ≤ 1 by decide)
    have hv : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    rcases hv (g.toOrderHom 0) with h0 | h0 <;> rcases hv (g.toOrderHom 1) with h1 | h1
    · refine Or.inr ?_
      ext j
      fin_cases j
      · rfl
      · exact congrArg Fin.val (h1.trans h0.symm)
    · refine Or.inl ?_
      ext j
      fin_cases j
      · exact congrArg Fin.val h0
      · exact congrArg Fin.val h1
    · rw [h0, h1] at hm
      exact absurd hm (by decide)
    · refine Or.inr ?_
      ext j
      fin_cases j
      · rfl
      · exact congrArg Fin.val (h1.trans h0.symm)
  rcases key (OneTruncation.vertexMap t) with h | h
  · exact Or.inl (OneTruncation.vertexMap_injective (h.trans (OneTruncation.vertexMap_taut 1).symm))
  · exact Or.inr (OneTruncation.vertexMap_injective (h.trans
      ((OneTruncation.vertexMap_map _ _).trans
        (congrArg _ (OneTruncation.vertexMap_map _ _))).symm))

noncomputable def nerveToCategoricalNerve (C : Cat.{u, u}) :
    nerve C ⟶ DiagSet.toSSet.obj (categoricalNerve.obj C) where
  app n := ↾fun A => OneTruncation.toFin n.unop.len ⋙ A
  naturality m n g := by
    ext A
    exact (congrArg (· ⋙ A)
      (OneTruncation.oneTruncation_map_comp_toFin (m := n.unop.len) (n := m.unop.len) g.unop)).symm

@[simp]
theorem nerveToCategoricalNerve_app (C : Cat.{u, u}) (n : SimplexCategoryᵒᵖ)
    (A : (nerve C).obj n) :
    (nerveToCategoricalNerve C).app n A = OneTruncation.toFin n.unop.len ⋙ A :=
  rfl

noncomputable def counitInv (C : Cat.{u, u}) :
    C ⥤ OneTruncation (categoricalNerve.obj C) where
  obj c := OneTruncation.mk ((nerveToCategoricalNerve C).app _ (nerveEquiv.symm c))
  map f := OneTruncation.homMk ((nerve.edgeMk f).map (nerveToCategoricalNerve C))
  map_id c := by
    have h : (nerve.edgeMk (𝟙 c)).map (nerveToCategoricalNerve C) = SSet.Edge.id _ :=
      (congrArg (SSet.Edge.map · _) (nerve.edgeMk_id c)).trans (SSet.Edge.map_id _ _)
    exact (congrArg OneTruncation.homMk h).trans (OneTruncation.homMk_id _)
  map_comp f g := by
    obtain ⟨h⟩ := (nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl
    exact (OneTruncation.homMk_comp_homMk (h.map (nerveToCategoricalNerve C))).symm

theorem oneTruncationAdjunction_counit_app_obj_mk (C : Cat.{u, u})
    (x : (DiagSet.toSSet.obj (categoricalNerve.obj C)) _⦋0⦌) :
    (oneTruncationAdjunction.counit.app C).toFunctor.obj (OneTruncation.mk x) =
      (x : OneTruncation (ball.{u} (atomSimplex 0)) ⥤ C).obj (OneTruncation.mk
        (uliftYonedaEquiv (𝟙 (ball.{u} (atomSimplex 0))) :
          diagram (ball.{u} (atomSimplex 0)) (atomSimplex 0))) :=
  rfl

theorem arrowMk_oneTruncationAdjunction_counit_app_map_homMk (C : Cat.{u, u})
    {x y : (DiagSet.toSSet.obj (categoricalNerve.obj C)) _⦋0⦌} (e : SSet.Edge x y) :
    Arrow.mk ((oneTruncationAdjunction.counit.app C).toFunctor.map (OneTruncation.homMk e)) =
      Arrow.mk ((e.edge : OneTruncation (ball.{u} (atomSimplex 1)) ⥤ C).map
        (OneTruncation.homMk (SSet.Edge.mk' (X := DiagSet.toSSet.obj (ball.{u} (atomSimplex 1)))
          (uliftYonedaEquiv (𝟙 (ball.{u} (atomSimplex 1))) :
            diagram (ball.{u} (atomSimplex 1)) (atomSimplex 1))))) :=
  arrowMk_homEquivInvFun_map_homMk (𝟙 _) e

private theorem counitInv_comp_counit (C : Cat.{u, u}) :
    counitInv C ⋙ (oneTruncationAdjunction.counit.app C).toFunctor = 𝟭 C :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun c d f => by
    obtain ⟨_, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).1
      ((arrowMk_oneTruncationAdjunction_counit_app_map_homMk C
        ((nerve.edgeMk f).map (nerveToCategoricalNerve C))).trans
        (arrowMk_map_toFin_map_tautEdge (ComposableArrows.mk₁ f)))
    exact h

theorem toFin_comp_mk₁ (F : OneTruncation (ball.{u} (atomSimplex 1)) ⥤ C) :
    OneTruncation.toFin 1 ⋙ ComposableArrows.mk₁ (F.map (OneTruncation.homMk tautEdge)) = F := by
  have hobj : ∀ v, (OneTruncation.toFin 1 ⋙ ComposableArrows.mk₁
      (F.map (OneTruncation.homMk tautEdge))).obj (OneTruncation.mk v) =
        F.obj (OneTruncation.mk v) := by
    intro v
    rcases eq_δ_taut_of_vertex v with rfl | rfl
    · change (ComposableArrows.mk₁ (F.map (OneTruncation.homMk tautEdge))).obj
        ((OneTruncation.toFin 1).obj _) = _
      rw [toFin_obj_mk_δ_taut]
      rfl
    · change (ComposableArrows.mk₁ (F.map (OneTruncation.homMk tautEdge))).obj
        ((OneTruncation.toFin 1).obj _) = _
      rw [toFin_obj_mk_δ_taut]
      rfl
  refine OneTruncation.functor_ext fun a b t => ?_
  rcases eq_taut_or_eq_σ t.edge with h | h
  · have ht := OneTruncation.arrowMk_homMk_eq t tautEdge h
    have h₁ : Arrow.mk ((OneTruncation.toFin 1 ⋙ ComposableArrows.mk₁
        (F.map (OneTruncation.homMk tautEdge))).map (OneTruncation.homMk t)) =
        Arrow.mk ((OneTruncation.toFin 1 ⋙ ComposableArrows.mk₁
          (F.map (OneTruncation.homMk tautEdge))).map (OneTruncation.homMk tautEdge)) :=
      congrArg (Functor.mapArrow _).obj ht
    have h₂ : Arrow.mk (F.map (OneTruncation.homMk t)) =
        Arrow.mk (F.map (OneTruncation.homMk tautEdge)) :=
      congrArg F.mapArrow.obj ht
    rw [h₁, h₂]
    exact arrowMk_map_toFin_map_tautEdge (ComposableArrows.mk₁ _)
  · have ht : Arrow.mk (OneTruncation.homMk t) = Arrow.mk (𝟙 (OneTruncation.mk a)) :=
      (OneTruncation.arrowMk_homMk_eq t (SSet.Edge.id a) (h.trans (by rw [t.src_eq]; rfl))).trans
        (congrArg Arrow.mk (OneTruncation.homMk_id a))
    have h₁ : Arrow.mk ((OneTruncation.toFin 1 ⋙ ComposableArrows.mk₁
        (F.map (OneTruncation.homMk tautEdge))).map (OneTruncation.homMk t)) =
        Arrow.mk ((OneTruncation.toFin 1 ⋙ ComposableArrows.mk₁
          (F.map (OneTruncation.homMk tautEdge))).map (𝟙 (OneTruncation.mk a))) :=
      congrArg (Functor.mapArrow _).obj ht
    have h₂ : Arrow.mk (F.map (OneTruncation.homMk t)) =
        Arrow.mk (F.map (𝟙 (OneTruncation.mk a))) :=
      congrArg F.mapArrow.obj ht
    rw [h₁, h₂, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact congrArg (fun z => Arrow.mk (𝟙 z)) (hobj a)

private theorem counit_comp_counitInv (C : Cat.{u, u}) :
    (oneTruncationAdjunction.counit.app C).toFunctor ⋙ counitInv C = 𝟭 _ :=
  OneTruncation.functor_ext fun _ _ e =>
    (congrArg (counitInv C).mapArrow.obj
      (arrowMk_oneTruncationAdjunction_counit_app_map_homMk C e)).trans
      (OneTruncation.arrowMk_homMk_eq _ e (toFin_comp_mk₁ _))

instance isIso_oneTruncationAdjunction_counit : IsIso oneTruncationAdjunction.{u}.counit :=
  have (C : Cat.{u, u}) : IsIso (oneTruncationAdjunction.counit.app C) :=
    ⟨(counitInv C).toCatHom, Cat.Hom.ext (counit_comp_counitInv C),
      Cat.Hom.ext (counitInv_comp_counit C)⟩
  NatIso.isIso_of_isIso_app _

noncomputable def categoricalNerveFullyFaithful : categoricalNerve.{u}.FullyFaithful :=
  oneTruncationAdjunction.fullyFaithfulROfIsIsoCounit

instance full_categoricalNerve : categoricalNerve.{u}.Full :=
  categoricalNerveFullyFaithful.full

instance faithful_categoricalNerve : categoricalNerve.{u}.Faithful :=
  categoricalNerveFullyFaithful.faithful

noncomputable instance reflectiveCategoricalNerve : Reflective categoricalNerve.{u} where
  L := oneTruncation
  adj := oneTruncationAdjunction

end Adjunction

namespace SimplicialSeedQuotient

noncomputable def freeToHomotopyCategory (X : DiagSet.{u}) :
    OneTruncation.Free X ⥤ SSet.Truncated.HomotopyCategory tr₂[X] :=
  Paths.lift
    { obj := fun x => SSet.Truncated.HomotopyCategory.mk (V := tr₂[X]) x.cell
      map := fun e => SSet.Truncated.HomotopyCategory.homMk (X.edgeEquivSSet e).toTruncated }

theorem freeToHomotopyCategory_map_edge {x y : X.Vertex} (e : X.Edge x y) :
    (freeToHomotopyCategory X).map (OneTruncation.edge e) =
      SSet.Truncated.HomotopyCategory.homMk (X.edgeEquivSSet e).toTruncated :=
  Category.id_comp _

theorem isComposite_freeToHomotopyCategory_map {a : PastingDiagram X} {x y : X.Vertex}
    {p : OneTruncation.point x ⟶ OneTruncation.point y} (hp : Diagrammatic.IsComposite a p) :
    IsComposite a ((freeToHomotopyCategory X).map p) := by
  induction hp with
  | edge e =>
    rw [freeToHomotopyCategory_map_edge]
    exact (IsComposite.edge (X.edgeEquivSSet e)).equiv
      (equiv_ofCell_map_iso atomSimplexOneIsoGlobe e.cell)
  | paste h _ _ hf hg =>
    rw [Functor.map_comp]
    exact IsComposite.paste h hf hg
  | equiv h _ hp => exact hp.equiv h

theorem freeMap_comp_freeToHomotopyCategory (f : X ⟶ Y) :
    OneTruncation.freeMap f ⋙ freeToHomotopyCategory Y = freeToHomotopyCategory X ⋙ hmap[f] :=
  OneTruncation.Free.functor_ext fun _ _ e => congrArg Arrow.mk
    (((congrArg (freeToHomotopyCategory Y).map (OneTruncation.freeMap_edge f e)).trans
      ((freeToHomotopyCategory_map_edge (e.map f)).trans
        (congrArg (fun t => SSet.Truncated.HomotopyCategory.homMk t.toTruncated)
          (DiagSet.edgeEquivSSet_map e f)))).trans
      (congrArg hmap[f].map (freeToHomotopyCategory_map_edge e)).symm)

theorem map_eq_of_oneTruncationRel {a b : OneTruncation.Free X} {p q : a ⟶ b}
    (h : OneTruncation.Rel X p q) :
    (freeToHomotopyCategory X ⋙ quotientFunctor X).map p =
      (freeToHomotopyCategory X ⋙ quotientFunctor X).map q := by
  induction h with
  | unit x =>
    change (quotientFunctor X).map ((freeToHomotopyCategory X).map (OneTruncation.edge _)) =
      (quotientFunctor X).map ((freeToHomotopyCategory X).map (𝟙 _))
    exact congrArg (quotientFunctor X).map ((freeToHomotopyCategory_map_edge _).trans
      ((congrArg (fun t => SSet.Truncated.HomotopyCategory.homMk t.toTruncated)
        (DiagSet.edgeEquivSSet_id x)).trans ((SSet.Truncated.HomotopyCategory.homMk_id _).trans
          ((freeToHomotopyCategory X).map_id _).symm)))
  | @boundary V hV c x y f g hf hg =>
    refine OneTruncation.map_eq_map_of_isComposite_boundary _ hV c (fun hf' hg' => ?_) hf hg
    have e := CategoryTheory.Quotient.sound _ (Rel.boundary hV c
      (isComposite_freeToHomotopyCategory_map hf') (isComposite_freeToHomotopyCategory_map hg'))
    change (quotientFunctor X).map
        ((OneTruncation.freeMap (uliftYonedaEquiv.symm c) ⋙ freeToHomotopyCategory X).map _) =
      (quotientFunctor X).map
        ((OneTruncation.freeMap (uliftYonedaEquiv.symm c) ⋙ freeToHomotopyCategory X).map _)
    rw [Functor.congr_hom (freeMap_comp_freeToHomotopyCategory _),
      Functor.congr_hom (freeMap_comp_freeToHomotopyCategory _), Functor.map_comp,
      Functor.map_comp, Functor.map_comp, Functor.map_comp]
    exact congrArg (_ ≫ · ≫ _) e

noncomputable def ofOneTruncation (X : DiagSet.{u}) : OneTruncation X ⥤ SimplicialSeedQuotient X :=
  CategoryTheory.Quotient.lift _ (freeToHomotopyCategory X ⋙ quotientFunctor X)
    fun _ _ _ _ h => map_eq_of_oneTruncationRel h

theorem ofOneTruncation_obj_mk (x : (DiagSet.toSSet.obj X) _⦋0⦌) :
    (ofOneTruncation X).obj (OneTruncation.mk x) = mk x :=
  rfl

theorem ofOneTruncation_map_globeHomMk {x y : X.Vertex} (e : X.Edge x y) :
    (ofOneTruncation X).map (OneTruncation.globeHomMk e) = homMk (X.edgeEquivSSet e) :=
  congrArg (quotientFunctor X).map (freeToHomotopyCategory_map_edge e)

theorem ofOneTruncation_map_homMk {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y) :
    (ofOneTruncation X).map (OneTruncation.homMk e) = homMk e :=
  (ofOneTruncation_map_globeHomMk _).trans (congrArg homMk (Equiv.apply_symm_apply _ e))

private noncomputable def homotopyCategoryToOneTruncation (X : DiagSet.{u}) :
    SSet.Truncated.HomotopyCategory tr₂[X] ⥤ OneTruncation X :=
  SSet.Truncated.HomotopyCategory.lift (fun x => OneTruncation.mk x)
    (fun e => OneTruncation.homMk (SSet.Edge.ofTruncated e)) (fun x => OneTruncation.homMk_id x)
    (fun σ => OneTruncation.homMk_comp_homMk (SSet.Edge.CompStruct.ofTruncated σ))

private theorem homotopyCategoryToOneTruncation_map_homMk {x y : (DiagSet.toSSet.obj X) _⦋0⦌}
    (e : SSet.Edge x y) :
    (homotopyCategoryToOneTruncation X).map
      (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) = OneTruncation.homMk e :=
  SSet.Truncated.HomotopyCategory.lift_map_homMk (V := tr₂[X]) (fun x => OneTruncation.mk x)
    (fun e => OneTruncation.homMk (SSet.Edge.ofTruncated e)) (fun x => OneTruncation.homMk_id x)
    (fun σ => OneTruncation.homMk_comp_homMk (SSet.Edge.CompStruct.ofTruncated σ)) e.toTruncated

private theorem exists_isComposite_of_isComposite {a : PastingDiagram X}
    {x y : (DiagSet.toSSet.obj X) _⦋0⦌}
    {φ : SSet.Truncated.HomotopyCategory.mk (V := tr₂[X]) x ⟶
      SSet.Truncated.HomotopyCategory.mk y} (h : IsComposite a φ) :
    ∃ p : OneTruncation.point x ⟶ OneTruncation.point y, Diagrammatic.IsComposite a p ∧
      (homotopyCategoryToOneTruncation X).map φ = (OneTruncation.quotientFunctor X).map p := by
  induction h with
  | edge e =>
    exact ⟨_, OneTruncation.isComposite_simplex_edge e,
      homotopyCategoryToOneTruncation_map_homMk e⟩
  | paste h _ _ hu hv =>
    obtain ⟨p, hp, ep⟩ := hu
    obtain ⟨q, hq, eq⟩ := hv
    exact ⟨p ≫ q, Diagrammatic.IsComposite.paste h hp hq,
      ((homotopyCategoryToOneTruncation X).map_comp _ _).trans
        ((congrArg₂ (· ≫ ·) ep eq).trans ((OneTruncation.quotientFunctor X).map_comp p q).symm)⟩
  | equiv h _ hu =>
    obtain ⟨p, hp, ep⟩ := hu
    exact ⟨p, hp.equiv h, ep⟩

private theorem hmap_comp_homotopyCategoryToOneTruncation (f : X ⟶ Y) :
    hmap[f] ⋙ homotopyCategoryToOneTruncation Y =
      homotopyCategoryToOneTruncation X ⋙ (oneTruncation.map f).toFunctor :=
  SSet.Truncated.HomotopyCategory.functor_ext_of_arrowMk fun _ _ e => congrArg Arrow.mk
    ((homotopyCategoryToOneTruncation_map_homMk (e.map (DiagSet.toSSet.map f))).trans
      ((congrArg (oneTruncation.map f).toFunctor.map
        (homotopyCategoryToOneTruncation_map_homMk e)).trans
          (oneTruncation_map_map_homMk f e)).symm)

private theorem homotopyCategoryToOneTruncation_map_eq_of_rel
    {a b : SSet.Truncated.HomotopyCategory tr₂[X]} (φ ψ : a ⟶ b) (h : Rel X φ ψ) :
    (homotopyCategoryToOneTruncation X).map φ = (homotopyCategoryToOneTruncation X).map ψ := by
  induction h with
  | @boundary V hV c x y φ ψ hφ hψ =>
    obtain ⟨p, hp, ep⟩ := exists_isComposite_of_isComposite hφ
    obtain ⟨q, hq, eq⟩ := exists_isComposite_of_isComposite hψ
    have e := ep.trans ((OneTruncation.boundary_eq hV _ hp hq).trans eq.symm)
    change (hmap[uliftYonedaEquiv.symm c] ⋙ homotopyCategoryToOneTruncation X).map φ =
      (hmap[uliftYonedaEquiv.symm c] ⋙ homotopyCategoryToOneTruncation X).map ψ
    rw [Functor.congr_hom (hmap_comp_homotopyCategoryToOneTruncation _),
      Functor.congr_hom (hmap_comp_homotopyCategoryToOneTruncation _)]
    exact congrArg (_ ≫ · ≫ _)
      (congrArg (oneTruncation.map (uliftYonedaEquiv.symm c)).toFunctor.map e)

noncomputable def toOneTruncation (X : DiagSet.{u}) : SimplicialSeedQuotient X ⥤ OneTruncation X :=
  lift (homotopyCategoryToOneTruncation X) fun _ _ => homotopyCategoryToOneTruncation_map_eq_of_rel

theorem toOneTruncation_obj_mk (x : (DiagSet.toSSet.obj X) _⦋0⦌) :
    (toOneTruncation X).obj (mk x) = OneTruncation.mk x :=
  rfl

theorem toOneTruncation_map_homMk {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y) :
    (toOneTruncation X).map (homMk e) = OneTruncation.homMk e :=
  (lift_map_homMk _ (fun _ _ => homotopyCategoryToOneTruncation_map_eq_of_rel) e).trans
    (homotopyCategoryToOneTruncation_map_homMk e)

theorem ofOneTruncation_comp_toOneTruncation (X : DiagSet.{u}) :
    ofOneTruncation X ⋙ toOneTruncation X = 𝟭 (OneTruncation X) :=
  OneTruncation.functor_ext fun _ _ e => congrArg Arrow.mk
    ((congrArg (toOneTruncation X).map (ofOneTruncation_map_homMk e)).trans
      (toOneTruncation_map_homMk e))

theorem toOneTruncation_comp_ofOneTruncation (X : DiagSet.{u}) :
    toOneTruncation X ⋙ ofOneTruncation X = 𝟭 (SimplicialSeedQuotient X) :=
  functor_ext fun _ _ e => congrArg Arrow.mk
    ((congrArg (ofOneTruncation X).map (toOneTruncation_map_homMk e)).trans
      (ofOneTruncation_map_homMk e))

theorem ofOneTruncation_naturality (f : X ⟶ Y) :
    (oneTruncation.map f).toFunctor ⋙ ofOneTruncation Y = ofOneTruncation X ⋙ map f :=
  OneTruncation.functor_ext fun _ _ e => congrArg Arrow.mk
    (((congrArg (ofOneTruncation Y).map (oneTruncation_map_map_homMk f e)).trans
      (ofOneTruncation_map_homMk _)).trans
        ((congrArg (map f).map (ofOneTruncation_map_homMk e)).trans (map_map_homMk f e)).symm)

theorem toOneTruncation_naturality (f : X ⟶ Y) :
    map f ⋙ toOneTruncation Y = toOneTruncation X ⋙ (oneTruncation.map f).toFunctor :=
  functor_ext fun _ _ e => congrArg Arrow.mk
    (((congrArg (toOneTruncation Y).map (map_map_homMk f e)).trans
      (toOneTruncation_map_homMk _)).trans
        ((congrArg (oneTruncation.map f).toFunctor.map (toOneTruncation_map_homMk e)).trans
          (oneTruncation_map_map_homMk f e)).symm)

end SimplicialSeedQuotient

noncomputable def nativeOneTruncationComparison (X : DiagSet.{u}) :
    OneTruncation X ≌ SimplicialSeedQuotient X :=
  CategoryTheory.Equivalence.mk (SimplicialSeedQuotient.ofOneTruncation X)
    (SimplicialSeedQuotient.toOneTruncation X)
    (eqToIso (SimplicialSeedQuotient.ofOneTruncation_comp_toOneTruncation X).symm)
    (eqToIso (SimplicialSeedQuotient.toOneTruncation_comp_ofOneTruncation X))

theorem nativeOneTruncationComparison_functor (X : DiagSet.{u}) :
    (nativeOneTruncationComparison X).functor = SimplicialSeedQuotient.ofOneTruncation X :=
  rfl

theorem nativeOneTruncationComparison_inverse (X : DiagSet.{u}) :
    (nativeOneTruncationComparison X).inverse = SimplicialSeedQuotient.toOneTruncation X :=
  rfl

noncomputable def OneTruncation.toHomotopyCategory (hX : IsInftyCategory 1 X) :
    OneTruncation X ⥤ HomotopyCategory X hX.1 :=
  (nativeOneTruncationComparison X).functor ⋙ SimplicialSeedQuotient.toHomotopyCategory hX

theorem OneTruncation.toHomotopyCategory_obj_mk (hX : IsInftyCategory 1 X)
    (x : (DiagSet.toSSet.obj X) _⦋0⦌) :
    (OneTruncation.toHomotopyCategory hX).obj (OneTruncation.mk x) = ⟨x⟩ :=
  rfl

theorem OneTruncation.toHomotopyCategory_obj_mk_vertex (hX : IsInftyCategory 1 X)
    (x : X.Vertex) :
    (OneTruncation.toHomotopyCategory hX).obj (OneTruncation.mk x) = ⟨x⟩ :=
  rfl

theorem OneTruncation.toHomotopyCategory_map_globeHomMk (hX : IsInftyCategory 1 X)
    {x y : X.Vertex} (e : X.Edge x y) :
    (OneTruncation.toHomotopyCategory hX).map (OneTruncation.globeHomMk e) =
      HomotopyCategory.homMk hX.1 e := by
  exact (congrArg (SimplicialSeedQuotient.toHomotopyCategory hX).map
    (SimplicialSeedQuotient.ofOneTruncation_map_globeHomMk e)).trans
      ((SimplicialSeedQuotient.toHomotopyCategory_map_homMk hX _).trans
        (congrArg (HomotopyCategory.homMk hX.1) (Equiv.symm_apply_apply _ e)))

theorem OneTruncation.toHomotopyCategory_map_homMk (hX : IsInftyCategory 1 X)
    {x y : X.Vertex} (e : SSet.Edge (X.vertexEquivSSet x) (X.vertexEquivSSet y)) :
    (OneTruncation.toHomotopyCategory hX).map (OneTruncation.homMk e) =
      HomotopyCategory.homMk hX.1 (X.edgeEquivSSet.symm e) :=
  OneTruncation.toHomotopyCategory_map_globeHomMk hX (X.edgeEquivSSet.symm e)

theorem isEquivalence_toHomotopyCategory (hX : IsInftyCategory 1 X) :
    (OneTruncation.toHomotopyCategory hX).IsEquivalence := by
  have := SimplicialSeedQuotient.isEquivalence_toHomotopyCategory hX
  exact Functor.isEquivalence_trans (nativeOneTruncationComparison X).functor
    (SimplicialSeedQuotient.toHomotopyCategory hX)

theorem OneTruncation.toHomotopyCategory_naturality (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (f : X ⟶ Y) :
    (oneTruncation.map f).toFunctor ⋙ OneTruncation.toHomotopyCategory hY =
      OneTruncation.toHomotopyCategory hX ⋙ homotopyFunctor hX.1 hY.1 f :=
  OneTruncation.functor_ext fun x y e => congrArg Arrow.mk
    ((((congrArg (OneTruncation.toHomotopyCategory hY).map (oneTruncation_map_map_homMk f e)).trans
      (OneTruncation.toHomotopyCategory_map_homMk hY (x := (X.vertexEquivSSet.symm x).map f)
        (y := (X.vertexEquivSSet.symm y).map f) _)).trans
      (congrArg (HomotopyCategory.homMk hY.1) (DiagSet.edgeEquivSSet_symm_map
        (x := X.vertexEquivSSet.symm x) (y := X.vertexEquivSSet.symm y) e f))).trans
      (congrArg (homotopyFunctor hX.1 hY.1 f).map
        (OneTruncation.toHomotopyCategory_map_homMk hX e)).symm)

end Atoms.Diagrammatic
