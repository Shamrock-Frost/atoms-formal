import Atoms.Diagrammatic.Adjunction.Transformation
import Atoms.Diagrammatic.OneTruncationProduct

open CategoryTheory Limits Simplicial Opposite
open Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {X X' Y Y' : DiagSet.{u}}

private theorem Atom.grayTensorSnd_eq_or_grayTensorFst_eq {U V : Atom}
    (f : atomSimplex 1 ⟶ Atom.grayTensor U V) :
    (∃ v : atomPoint ⟶ V, f ≫ Atom.grayTensorSnd U V = toAtomPoint _ ≫ v) ∨
      ∃ w : atomPoint ⟶ U, f ≫ Atom.grayTensorFst U V = toAtomPoint _ ≫ w := by
  obtain ⟨W, p, i, hp, hi, rfl⟩ := exists_collapse_inclusion_factorization f
  obtain ⟨A, B, a, b, e, -, -, rfl⟩ := Atom.exists_iso_comp_grayTensorMap_of_isInclusionHom i hi
  have hW := dimension_le_of_isCollapseHom p hp
  rw [dimension_atomSimplex, Atom.dimension_eq_of_iso e, Atom.dimension_grayTensor] at hW
  rcases (by omega : B.dimension = 0 ∨ A.dimension = 0) with hB | hA
  · have := isIso_toAtomPoint_of_dimension_eq_zero hB
    refine Or.inl ⟨inv (toAtomPoint B) ≫ b, ?_⟩
    rw [Subsingleton.elim (toAtomPoint _) (p ≫ e.hom ≫ Atom.grayTensorSnd A B ≫ toAtomPoint B)]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, Atom.grayTensorMap_comp_grayTensorSnd]
  · have := isIso_toAtomPoint_of_dimension_eq_zero hA
    refine Or.inr ⟨inv (toAtomPoint A) ≫ a, ?_⟩
    rw [Subsingleton.elim (toAtomPoint _) (p ≫ e.hom ≫ Atom.grayTensorFst A B ≫ toAtomPoint A)]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, Atom.grayTensorMap_comp_grayTensorFst]

private theorem grayTensorLeft_map_grayTensorFst (A : DiagSet.{u}) {B B' : DiagSet.{u}}
    (g : B ⟶ B') : (grayTensorLeft A).map g ≫ grayTensorFst A B' = grayTensorFst A B := by
  rw [grayTensorLeft_map_eq, grayTensorBifunctor_map_grayTensorFst, Category.comp_id]

private noncomputable def sectFst (X : DiagSet.{u}) (c : ball.{u} atomPoint ⟶ Y) :
    X ⟶ grayTensor X Y :=
  inv (grayTensorFst X (ball.{u} atomPoint)) ≫ (grayTensorLeft X).map c

private noncomputable def sectSnd (Y : DiagSet.{u}) (c : ball.{u} atomPoint ⟶ X) :
    Y ⟶ grayTensor X Y :=
  inv (grayTensorSnd (ball.{u} atomPoint) Y) ≫ (grayTensorRight Y).map c

private theorem sectFst_comp_grayTensorFst (X : DiagSet.{u}) (c : ball.{u} atomPoint ⟶ Y) :
    sectFst X c ≫ grayTensorFst X Y = 𝟙 X := by
  rw [sectFst, Category.assoc, grayTensorLeft_map_grayTensorFst, IsIso.inv_hom_id]

private theorem sectFst_comp_grayTensorSnd (X : DiagSet.{u}) (c : ball.{u} atomPoint ⟶ Y) :
    sectFst X c ≫ grayTensorSnd X Y = isTerminalBallAtomPoint.from X ≫ c := by
  rw [sectFst, Category.assoc, grayTensorLeft_map_grayTensorSnd, ← Category.assoc,
    isTerminalBallAtomPoint.hom_ext (_ ≫ _) (isTerminalBallAtomPoint.from X)]

private theorem sectSnd_comp_grayTensorSnd (Y : DiagSet.{u}) (c : ball.{u} atomPoint ⟶ X) :
    sectSnd Y c ≫ grayTensorSnd X Y = 𝟙 Y := by
  rw [sectSnd, Category.assoc, grayTensorRight_map_grayTensorSnd, IsIso.inv_hom_id]

private theorem sectSnd_comp_grayTensorFst (Y : DiagSet.{u}) (c : ball.{u} atomPoint ⟶ X) :
    sectSnd Y c ≫ grayTensorFst X Y = isTerminalBallAtomPoint.from Y ≫ c := by
  rw [sectSnd, Category.assoc, grayTensorRight_map_grayTensorFst, ← Category.assoc,
    isTerminalBallAtomPoint.hom_ext (_ ≫ _) (isTerminalBallAtomPoint.from Y)]

private theorem inv_comp_grayTensorBifunctor_map_comp_map {Z Z' A B A' B' : DiagSet.{u}}
    {π : grayTensor A B ⟶ Z} {π' : grayTensor A' B' ⟶ Z'} [IsIso π] [IsIso π'] {k : Z ⟶ Z'}
    {a₀ : A ⟶ A'} {b₀ : B ⟶ B'}
    (hπ : grayTensorBifunctor.map ((a₀, b₀) : (A, B) ⟶ (A', B')) ≫ π' = π ≫ k)
    {p : A ⟶ X} {q : B ⟶ Y} {p' : A' ⟶ X'} {q' : B' ⟶ Y'} {a : X ⟶ X'} {b : Y ⟶ Y'}
    (h₁ : p ≫ a = a₀ ≫ p') (h₂ : q ≫ b = b₀ ≫ q') :
    (inv π ≫ grayTensorBifunctor.map ((p, q) : (A, B) ⟶ (X, Y))) ≫
        grayTensorBifunctor.map ((a, b) : (X, Y) ⟶ (X', Y')) =
      k ≫ inv π' ≫ grayTensorBifunctor.map ((p', q') : (A', B') ⟶ (X', Y')) := by
  have h : inv π ≫ grayTensorBifunctor.map ((a₀, b₀) : (A, B) ⟶ (A', B')) = k ≫ inv π' := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, hπ]
  have h' : ((p, q) : (A, B) ⟶ (X, Y)) ≫ ((a, b) : (X, Y) ⟶ (X', Y')) =
      ((a₀, b₀) : (A, B) ⟶ (A', B')) ≫ ((p', q') : (A', B') ⟶ (X', Y')) :=
    CategoryTheory.Prod.hom_ext h₁ h₂
  rw [Category.assoc, ← Functor.map_comp, h', Functor.map_comp, reassoc_of% h]

private theorem sectFst_comp_map (a : X ⟶ X') (b : Y ⟶ Y') (c : ball.{u} atomPoint ⟶ Y) :
    sectFst X c ≫ grayTensorBifunctor.map ((a, b) : (X, Y) ⟶ (X', Y')) =
      a ≫ sectFst X' (c ≫ b) :=
  inv_comp_grayTensorBifunctor_map_comp_map
    (grayTensorBifunctor_map_grayTensorFst a (𝟙 (ball.{u} atomPoint)))
    ((Category.id_comp a).trans (Category.comp_id a).symm) (Category.id_comp (c ≫ b)).symm

private theorem sectSnd_comp_map (a : X ⟶ X') (b : Y ⟶ Y') (c : ball.{u} atomPoint ⟶ X) :
    sectSnd Y c ≫ grayTensorBifunctor.map ((a, b) : (X, Y) ⟶ (X', Y')) =
      b ≫ sectSnd Y' (c ≫ a) :=
  inv_comp_grayTensorBifunctor_map_comp_map
    (grayTensorBifunctor_map_grayTensorSnd (𝟙 (ball.{u} atomPoint)) b)
    (Category.id_comp (c ≫ a)).symm ((Category.id_comp b).trans (Category.comp_id b).symm)

private theorem sectSnd_id (Y : DiagSet.{u}) :
    sectSnd Y (𝟙 (ball.{u} atomPoint)) = inv (grayTensorSnd (ball.{u} atomPoint) Y) :=
  (congrArg (inv (grayTensorSnd (ball.{u} atomPoint) Y) ≫ ·)
    ((grayTensorRight Y).map_id _)).trans (Category.comp_id _)

noncomputable def grayTensorVertex (x : X.Vertex) (y : Y.Vertex) :
    (grayTensor X Y).Vertex :=
  uliftYonedaEquiv (X := atomPoint) (F := grayTensor X Y)
    (inv (grayTensorFst (ball.{u} atomPoint) (ball.{u} atomPoint)) ≫
      grayTensorBifunctor.map ((vertexHom x, vertexHom y) :
        (ball.{u} atomPoint, ball.{u} atomPoint) ⟶ (X, Y)))

private theorem sectSnd_app_vertex (x : (DiagSet.toSSet.obj X) _⦋0⦌)
    (y : (DiagSet.toSSet.obj Y) _⦋0⦌) :
    (DiagSet.toSSet.map (sectSnd Y (vertexHom x))).app _ y = grayTensorVertex x y := by
  refine vertexHom_injective ((vertexHom_comp y (sectSnd Y (vertexHom x))).symm.trans ?_)
  have h := sectSnd_comp_map (vertexHom x) (vertexHom y) (𝟙 _)
  rw [Category.id_comp, sectSnd_id, IsIso.inv_eq_inv.2
    (isTerminalBallAtomPoint.hom_ext (grayTensorSnd _ _) (grayTensorFst _ _))] at h
  dsimp only [grayTensorVertex]
  rw [vertexHom_uliftYonedaEquiv, h]

private theorem grayTensor_ball_hom_ext {T : DiagSet.{u}} {U V : Atom}
    {g g' : T ⟶ grayTensor (ball.{u} U) (ball.{u} V)}
    (h₁ : g ≫ grayTensorFst _ _ = g' ≫ grayTensorFst _ _)
    (h₂ : g ≫ grayTensorSnd _ _ = g' ≫ grayTensorSnd _ _) : g = g' :=
  (cancel_mono (grayTensorToProd (ball.{u} U) (ball.{u} V))).1 (prod.hom_ext
    (by simpa only [grayTensorToProd, Category.assoc, prod.lift_fst] using h₁)
    (by simpa only [grayTensorToProd, Category.assoc, prod.lift_snd] using h₂))

private theorem eq_comp_comp_of_ball {I U V : Atom} {A B : DiagSet.{u}}
    {π : grayTensor (ball.{u} U) (ball.{u} V) ⟶ A} {π' : grayTensor (ball.{u} U) (ball.{u} V) ⟶ B}
    (hext : ∀ g g' : ball.{u} I ⟶ grayTensor (ball.{u} U) (ball.{u} V),
      g ≫ π = g' ≫ π → g ≫ π' = g' ≫ π' → g = g')
    {s : A ⟶ grayTensor (ball.{u} U) (ball.{u} V)} {c : ball.{u} atomPoint ⟶ B}
    (hs : s ≫ π = 𝟙 A) (hs' : s ≫ π' = isTerminalBallAtomPoint.from A ≫ c)
    (g : ball.{u} I ⟶ grayTensor (ball.{u} U) (ball.{u} V))
    (h : g ≫ π' = isTerminalBallAtomPoint.from _ ≫ c) : g = (g ≫ π) ≫ s := by
  refine hext _ _ (by simp only [Category.assoc, hs, Category.comp_id]) ?_
  simp only [Category.assoc, hs', h]
  exact (congrArg (· ≫ c) (isTerminalBallAtomPoint.hom_ext _
    (g ≫ π ≫ isTerminalBallAtomPoint.from A))).trans (by simp only [Category.assoc])

private theorem eq_comp_sectFst_of_ball {I U V : Atom}
    (g : ball.{u} I ⟶ grayTensor (ball.{u} U) (ball.{u} V)) (c : ball.{u} atomPoint ⟶ ball.{u} V)
    (h : g ≫ grayTensorSnd _ _ = isTerminalBallAtomPoint.from _ ≫ c) :
    g = (g ≫ grayTensorFst _ _) ≫ sectFst _ c :=
  eq_comp_comp_of_ball (fun _ _ => grayTensor_ball_hom_ext) (sectFst_comp_grayTensorFst _ c)
    (sectFst_comp_grayTensorSnd _ c) g h

private theorem eq_comp_sectSnd_of_ball {I U V : Atom}
    (g : ball.{u} I ⟶ grayTensor (ball.{u} U) (ball.{u} V)) (c : ball.{u} atomPoint ⟶ ball.{u} U)
    (h : g ≫ grayTensorFst _ _ = isTerminalBallAtomPoint.from _ ≫ c) :
    g = (g ≫ grayTensorSnd _ _) ≫ sectSnd _ c :=
  eq_comp_comp_of_ball (fun _ _ h₁ h₂ => grayTensor_ball_hom_ext h₂ h₁)
    (sectSnd_comp_grayTensorSnd _ c) (sectSnd_comp_grayTensorFst _ c) g h

private theorem uliftYonedaEquiv_symm_grayTensorCell {U V : Atom} (x : diagram X U)
    (y : diagram Y V) :
    uliftYonedaEquiv.symm (grayTensorCell x y) = (grayTensorBallIso U V).inv ≫
      grayTensorBifunctor.map ((uliftYonedaEquiv.symm x, uliftYonedaEquiv.symm y) :
        (ball.{u} U, ball.{u} V) ⟶ (X, Y)) := by
  have h₀ : uliftYonedaEquiv (grayTensorBallIso.{u} U V).inv =
      grayTensorCell (X := ball.{u} U) (Y := ball.{u} V) (ULift.up (𝟙 U) : diagram (ball.{u} U) U)
        (ULift.up (𝟙 V) : diagram (ball.{u} V) V) :=
    Equiv.apply_symm_apply _ _
  rw [Equiv.symm_apply_eq, uliftYonedaEquiv_comp, h₀]
  refine Eq.trans ?_ (grayTensorCell_naturality _ _ _ _).symm
  exact congrArg₂ grayTensorCell
    ((Equiv.apply_symm_apply uliftYonedaEquiv x).symm.trans (uliftYonedaEquiv_apply _))
    ((Equiv.apply_symm_apply uliftYonedaEquiv y).symm.trans (uliftYonedaEquiv_apply _))

private theorem exists_edge_eq (s : (DiagSet.toSSet.obj (grayTensor X Y)) _⦋1⦌) :
    (∃ (y : (DiagSet.toSSet.obj Y) _⦋0⦌) (t : (DiagSet.toSSet.obj X) _⦋1⦌),
      s = (DiagSet.toSSet.map (sectFst X (vertexHom y))).app _ t) ∨
    ∃ (x : (DiagSet.toSSet.obj X) _⦋0⦌) (t : (DiagSet.toSSet.obj Y) _⦋1⦌),
      s = (DiagSet.toSSet.map (sectSnd Y (vertexHom x))).app _ t := by
  obtain ⟨U, V, x, y, f, hs⟩ := exists_eq_map_grayTensorCell (T := atomSimplex 1) s
  have key : (uliftYonedaEquiv (X := atomSimplex 1) (F := grayTensor X Y)).symm s =
      (uliftYoneda.map f ≫ (grayTensorBallIso U V).inv) ≫
        grayTensorBifunctor.map ((uliftYonedaEquiv.symm x, uliftYonedaEquiv.symm y) :
          (ball.{u} U, ball.{u} V) ⟶ (X, Y)) := by
    rw [hs, uliftYonedaEquiv_symm_map, uliftYonedaEquiv_symm_grayTensorCell, Category.assoc]
    rfl
  rcases Atom.grayTensorSnd_eq_or_grayTensorFst_eq f with ⟨v, hv⟩ | ⟨w, hw⟩
  · have hg := eq_comp_sectFst_of_ball (uliftYoneda.map f ≫ (grayTensorBallIso U V).inv)
      (uliftYoneda.map v) (by
        have hv' : f ≫ Atom.grayTensorMap (toAtomPoint U) (𝟙 V) ≫
            (Atom.grayTensorLeftUnitor V).hom = toAtomPoint _ ≫ v := hv
        rw [grayTensorSnd_ball, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, hv',
          Functor.map_comp]
        exact congrArg (· ≫ _) (isTerminalBallAtomPoint.hom_ext _ _))
    rw [hg, Category.assoc, sectFst_comp_map, ← Category.assoc] at key
    refine Or.inl ⟨uliftYonedaEquiv (X := atomPoint) (uliftYoneda.map v ≫ uliftYonedaEquiv.symm y),
      uliftYonedaEquiv (X := atomSimplex 1) (((uliftYoneda.map f ≫ (grayTensorBallIso U V).inv) ≫
        grayTensorFst _ _) ≫ uliftYonedaEquiv.symm x), ?_⟩
    rw [vertexHom_uliftYonedaEquiv]
    exact (Equiv.symm_apply_eq _).1 key |>.trans (uliftYonedaEquiv_comp _ _)
  · have hg := eq_comp_sectSnd_of_ball (uliftYoneda.map f ≫ (grayTensorBallIso U V).inv)
      (uliftYoneda.map w) (by
        have hw' : f ≫ Atom.grayTensorMap (𝟙 U) (toAtomPoint V) ≫
            (Atom.grayTensorRightUnitor U).hom = toAtomPoint _ ≫ w := hw
        rw [grayTensorFst_ball, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, hw',
          Functor.map_comp]
        exact congrArg (· ≫ _) (isTerminalBallAtomPoint.hom_ext _ _))
    rw [hg, Category.assoc, sectSnd_comp_map, ← Category.assoc] at key
    refine Or.inr ⟨uliftYonedaEquiv (X := atomPoint) (uliftYoneda.map w ≫ uliftYonedaEquiv.symm x),
      uliftYonedaEquiv (X := atomSimplex 1) (((uliftYoneda.map f ≫ (grayTensorBallIso U V).inv) ≫
        grayTensorSnd _ _) ≫ uliftYonedaEquiv.symm y), ?_⟩
    rw [vertexHom_uliftYonedaEquiv]
    exact (Equiv.symm_apply_eq _).1 key |>.trans (uliftYonedaEquiv_comp _ _)

private theorem arrowMk_map_homMk_of_edge_eq {Z W : DiagSet.{u}}
    (G : OneTruncation W ⥤ OneTruncation W) (s : Z ⟶ W)
    (hs : (oneTruncation.map s).toFunctor ⋙ G = (oneTruncation.map s).toFunctor)
    {w w' : (DiagSet.toSSet.obj W) _⦋0⦌} (e : SSet.Edge w w') (t : (DiagSet.toSSet.obj Z) _⦋1⦌)
    (ht : e.edge = (DiagSet.toSSet.map s).app _ t) :
    Arrow.mk (G.map (OneTruncation.homMk e)) = Arrow.mk (OneTruncation.homMk e) := by
  have h : Arrow.mk (OneTruncation.homMk e) = Arrow.mk ((oneTruncation.map s).toFunctor.map
      (OneTruncation.homMk (SSet.Edge.mk' t))) :=
    (OneTruncation.arrowMk_homMk_eq e ((SSet.Edge.mk' t).map (DiagSet.toSSet.map s))
      (ht.trans (by rw [SSet.Edge.map_edge, SSet.Edge.mk'_edge]))).trans
        (congrArg Arrow.mk (oneTruncation_map_map_homMk _ _).symm)
  exact (congrArg G.mapArrow.obj h).trans ((congrArg (fun H : OneTruncation Z ⥤ OneTruncation W =>
    Arrow.mk (H.map (OneTruncation.homMk (SSet.Edge.mk' t)))) hs).trans h.symm)

private theorem oneTruncation_map_from_comp_vertexHom (Z : DiagSet.{u}) {W : DiagSet.{u}}
    (w : (DiagSet.toSSet.obj W) _⦋0⦌) :
    (oneTruncation.map (isTerminalBallAtomPoint.from Z ≫ vertexHom w)).toFunctor =
      (Functor.const _).obj (OneTruncation.mk w) := by
  rw [Functor.map_comp, Cat.Hom.comp_toFunctor, OneTruncation.isTerminalBall.hom_ext
    (oneTruncation.map _) ((Functor.const _).obj (OneTruncation.mk (X := ball.{u} atomPoint)
      (ULift.up (𝟙 atomPoint)))).toCatHom,
    Functor.toCatHom_toFunctor]
  refine OneTruncation.functor_ext fun _ _ _ =>
    (congrArg Arrow.mk ((oneTruncation.map (vertexHom w)).toFunctor.map_id _)).trans ?_
  exact congrArg (fun a => Arrow.mk (𝟙 a)) (congrArg OneTruncation.mk
    ((uliftYonedaEquiv_apply (vertexHom w)).symm.trans (uliftYonedaEquiv_vertexHom w)))

private theorem prod_functor_ext {D : Type*} [Category* D]
    {F G : OneTruncation X × OneTruncation Y ⥤ D}
    (h₁ : ∀ y : (DiagSet.toSSet.obj Y) _⦋0⦌,
      Prod.sectL _ (OneTruncation.mk y) ⋙ F = Prod.sectL _ (OneTruncation.mk y) ⋙ G)
    (h₂ : ∀ x : (DiagSet.toSSet.obj X) _⦋0⦌,
      Prod.sectR (OneTruncation.mk x) _ ⋙ F = Prod.sectR (OneTruncation.mk x) _ ⋙ G) :
    F = G := by
  have hc : Functor.curry.obj F = Functor.curry.obj G :=
    OneTruncation.functor_ext fun x x' e => arrowMk_eq_of_app _ _ (h₂ x) (h₂ x') fun y =>
      congrArg (fun H => Arrow.mk (H.map (OneTruncation.homMk e))) (h₁ y)
  rw [← Functor.uncurry_obj_curry_obj F, hc, Functor.uncurry_obj_curry_obj]

private theorem sectL_comp_uncurry {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (F : A ⥤ B ⥤ C) (b : B) :
    Prod.sectL A b ⋙ Functor.uncurry.obj F = F ⋙ (evaluation B C).obj b :=
  Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq ((Functor.uncurry_obj_map F _).trans
    ((congrArg _ ((F.obj _).map_id _)).trans (Category.comp_id _)))

private theorem sectR_comp_uncurry {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (F : A ⥤ B ⥤ C) (a : A) : Prod.sectR a B ⋙ Functor.uncurry.obj F = F.obj a :=
  Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq ((Functor.uncurry_obj_map F _).trans
    ((congrArg (· ≫ _) (congrArg (fun φ => NatTrans.app φ _) (F.map_id _))).trans
      (Category.id_comp _)))

private theorem arrowMk_homFunctor_map_homMk_app {Z : DiagSet.{u}}
    {v w : (DiagSet.toSSet.obj ((grayHomRight Y).obj Z)) _⦋0⦌} (ε : SSet.Edge v w)
    (y : (DiagSet.toSSet.obj Y) _⦋0⦌) :
    Arrow.mk (((homFunctor Y Z).map (OneTruncation.homMk ε)).app (OneTruncation.mk y)) =
      Arrow.mk (OneTruncation.homMk (ε.map (DiagSet.toSSet.map (grayHomEval y Z)))) := by
  obtain ⟨F, rfl⟩ : ∃ F, DiagSet.vertexEquivSSet _ (diagramVertex F) = v :=
    ⟨_, (diagramVertexEquiv_apply _).symm.trans (Equiv.apply_symm_apply _ v)⟩
  obtain ⟨G, rfl⟩ : ∃ G, DiagSet.vertexEquivSSet _ (diagramVertex G) = w :=
    ⟨_, (diagramVertexEquiv_apply _).symm.trans (Equiv.apply_symm_apply _ w)⟩
  have h {F₁ F₂ G₁ G₂ : OneTruncation Y ⥤ OneTruncation Z} (h₁ : F₁ = F₂) (α : F₂ ⟶ G₁)
      (h₂ : G₁ = G₂) : Arrow.mk ((eqToHom h₁ ≫ α ≫ eqToHom h₂).app (OneTruncation.mk y)) =
        Arrow.mk (α.app (OneTruncation.mk y)) := by
    subst h₁ h₂
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have hmap := homFunctor_map_globeHomMk (F := F) (G := G)
    (((grayHomRight Y).obj Z).edgeEquivSSet.symm ε)
  exact ((congrArg (fun φ => Arrow.mk (NatTrans.app φ (OneTruncation.mk y)))
    ((congrArg (homFunctor Y Z).map (OneTruncation.homMk_eq_globeHomMk ε)).trans
      hmap)).trans (h _ _ _)).trans (by
      refine (congrArg Arrow.mk (Transformation.toOneTruncation_app_mk _ y)).trans
        ((OneTruncation.arrowMk_globeHomMk_eq _ _
          ?_).trans (congrArg Arrow.mk (OneTruncation.homMk_eq_globeHomMk
            (ε.map (DiagSet.toSSet.map (grayHomEval y Z)))).symm))
      exact (Transformation.cell_app _ y).trans
        (congrArg DiagSet.Edge.cell (Z.edgeEquivSSet.injective
        ((DiagSet.edgeEquivSSet_map _ _).trans
          ((congrArg (fun e => e.map (DiagSet.toSSet.map (grayHomEval y Z)))
            (Equiv.apply_symm_apply _ ε)).trans
              (Equiv.apply_symm_apply _ _).symm)))))

private theorem unit_app_vertex (x : (DiagSet.toSSet.obj X) _⦋0⦌) :
    (DiagSet.toSSet.map ((grayTensorRightAdjunction Y).unit.app X)).app _ x =
      diagramVertex (sectSnd Y (vertexHom x)) := by
  refine vertexHom_injective
    ((vertexHom_comp x ((grayTensorRightAdjunction Y).unit.app X)).symm.trans ?_)
  rw [vertexHom_diagramVertex, sectSnd, IsIso.hom_inv_id_assoc,
    ← Category.comp_id ((grayTensorRight Y).map (vertexHom x)),
    Adjunction.homEquiv_naturality_left]
  exact congrArg (vertexHom x ≫ ·) ((grayTensorRightAdjunction Y).homEquiv_id X).symm

private theorem unit_app_comp_grayHomEval (y : (DiagSet.toSSet.obj Y) _⦋0⦌) :
    (grayTensorRightAdjunction Y).unit.app X ≫ grayHomEval y (grayTensor X Y) =
      sectFst X (vertexHom y) :=
  ((congrArg (· ≫ grayHomEval y (grayTensor X Y))
    ((grayTensorRightAdjunction Y).homEquiv_id X).symm).trans
      (homEquiv_comp_grayHomEval (T := X) y (𝟙 (grayTensor X Y)))).trans
        (congrArg (inv (grayTensorFst X (ball.{u} atomPoint)) ≫ ·) (Category.comp_id _))

noncomputable def oneTruncationGrayTensorFunctor (X Y : DiagSet.{u}) :
    OneTruncation (grayTensor X Y) ⥤ OneTruncation X × OneTruncation Y :=
  (oneTruncation.map (grayTensorFst X Y)).toFunctor.prod'
    (oneTruncation.map (grayTensorSnd X Y)).toFunctor

noncomputable def oneTruncationGrayTensorInverse (X Y : DiagSet.{u}) :
    OneTruncation X × OneTruncation Y ⥤ OneTruncation (grayTensor X Y) :=
  Functor.uncurry.obj ((oneTruncation.map ((grayTensorRightAdjunction Y).unit.app X)).toFunctor ⋙
    homFunctor Y (grayTensor X Y))

private theorem sectL_comp_inverse (y : (DiagSet.toSSet.obj Y) _⦋0⦌) :
    Prod.sectL _ (OneTruncation.mk y) ⋙ oneTruncationGrayTensorInverse X Y =
      (oneTruncation.map (sectFst X (vertexHom y))).toFunctor := by
  rw [oneTruncationGrayTensorInverse, sectL_comp_uncurry]
  refine OneTruncation.functor_ext fun x x' e => ?_
  have hu := (congrArg (fun φ => Arrow.mk (NatTrans.app ((homFunctor Y (grayTensor X Y)).map φ)
    (OneTruncation.mk y))) (oneTruncation_map_map_homMk ((grayTensorRightAdjunction Y).unit.app X)
      e)).trans (arrowMk_homFunctor_map_homMk_app
        (e.map (DiagSet.toSSet.map ((grayTensorRightAdjunction Y).unit.app X))) y)
  have hs := (OneTruncation.arrowMk_homMk_eq
    ((e.map (DiagSet.toSSet.map ((grayTensorRightAdjunction Y).unit.app X))).map
      (DiagSet.toSSet.map (grayHomEval y (grayTensor X Y))))
    (e.map (DiagSet.toSSet.map (sectFst X (vertexHom y))))
    (congrArg (fun f => (DiagSet.toSSet.map f).app _ e.edge) (unit_app_comp_grayHomEval y))).trans
      (congrArg Arrow.mk (oneTruncation_map_map_homMk (sectFst X (vertexHom y)) e).symm)
  exact hu.trans hs

private theorem sectR_comp_inverse (x : (DiagSet.toSSet.obj X) _⦋0⦌) :
    Prod.sectR (OneTruncation.mk x) _ ⋙ oneTruncationGrayTensorInverse X Y =
      (oneTruncation.map (sectSnd Y (vertexHom x))).toFunctor := by
  rw [oneTruncationGrayTensorInverse, sectR_comp_uncurry]
  exact (congrArg (homFunctor Y (grayTensor X Y)).obj (oneTruncation_map_obj_mk _ x)).trans
    ((congrArg (fun v => (homFunctor Y (grayTensor X Y)).obj (OneTruncation.mk v))
      (unit_app_vertex x)).trans (homFunctor_obj_mk _))

private theorem oneTruncation_map_comp_functor {Z : DiagSet.{u}} (s : Z ⟶ grayTensor X Y) :
    (oneTruncation.map s).toFunctor ⋙ oneTruncationGrayTensorFunctor X Y =
      (oneTruncation.map (s ≫ grayTensorFst X Y)).toFunctor.prod'
        (oneTruncation.map (s ≫ grayTensorSnd X Y)).toFunctor := by
  rw [Functor.map_comp, Functor.map_comp, Cat.Hom.comp_toFunctor, Cat.Hom.comp_toFunctor]
  rfl

private theorem sectFst_comp_functor (y : (DiagSet.toSSet.obj Y) _⦋0⦌) :
    (oneTruncation.map (sectFst X (vertexHom y))).toFunctor ⋙ oneTruncationGrayTensorFunctor X Y =
      Prod.sectL _ (OneTruncation.mk y) := by
  rw [oneTruncation_map_comp_functor, sectFst_comp_grayTensorFst, sectFst_comp_grayTensorSnd,
    oneTruncation_map_from_comp_vertexHom, CategoryTheory.Functor.map_id, Cat.Hom.id_toFunctor]
  rfl

private theorem sectSnd_comp_functor (x : (DiagSet.toSSet.obj X) _⦋0⦌) :
    (oneTruncation.map (sectSnd Y (vertexHom x))).toFunctor ⋙ oneTruncationGrayTensorFunctor X Y =
      Prod.sectR (OneTruncation.mk x) _ := by
  rw [oneTruncation_map_comp_functor, sectSnd_comp_grayTensorFst, sectSnd_comp_grayTensorSnd,
    oneTruncation_map_from_comp_vertexHom, CategoryTheory.Functor.map_id, Cat.Hom.id_toFunctor]
  rfl

theorem oneTruncationGrayTensorInverse_obj_mk (X Y : DiagSet.{u})
    (x : X.Vertex) (y : Y.Vertex) :
    (oneTruncationGrayTensorInverse X Y).obj (OneTruncation.mk x, OneTruncation.mk y) =
      OneTruncation.mk (grayTensorVertex x y) :=
  (Functor.congr_obj (sectR_comp_inverse x) (OneTruncation.mk y)).trans
    (congrArg OneTruncation.mk (sectSnd_app_vertex x y))

theorem oneTruncationGrayTensorFunctor_comp_inverse (X Y : DiagSet.{u}) :
    oneTruncationGrayTensorFunctor X Y ⋙ oneTruncationGrayTensorInverse X Y = 𝟭 _ :=
  OneTruncation.functor_ext fun _ _ e => by
    rcases exists_edge_eq e.edge with ⟨y, t, ht⟩ | ⟨x, t, ht⟩
    · exact arrowMk_map_homMk_of_edge_eq
        (oneTruncationGrayTensorFunctor X Y ⋙ oneTruncationGrayTensorInverse X Y) (sectFst X _)
        ((congrArg (· ⋙ oneTruncationGrayTensorInverse X Y) (sectFst_comp_functor y)).trans
          (sectL_comp_inverse y)) e t ht
    · exact arrowMk_map_homMk_of_edge_eq
        (oneTruncationGrayTensorFunctor X Y ⋙ oneTruncationGrayTensorInverse X Y) (sectSnd Y _)
        ((congrArg (· ⋙ oneTruncationGrayTensorInverse X Y) (sectSnd_comp_functor x)).trans
          (sectR_comp_inverse x)) e t ht

theorem oneTruncationGrayTensorInverse_comp_functor (X Y : DiagSet.{u}) :
    oneTruncationGrayTensorInverse X Y ⋙ oneTruncationGrayTensorFunctor X Y = 𝟭 _ :=
  prod_functor_ext
    (fun y => (congrArg (· ⋙ oneTruncationGrayTensorFunctor X Y) (sectL_comp_inverse y)).trans
      (sectFst_comp_functor y))
    fun x => (congrArg (· ⋙ oneTruncationGrayTensorFunctor X Y) (sectR_comp_inverse x)).trans
      (sectSnd_comp_functor x)

noncomputable def oneTruncationGrayTensorIso (X Y : DiagSet.{u}) :
    oneTruncation.obj (grayTensor X Y) ≅ Cat.of (OneTruncation X × OneTruncation Y) where
  hom := (oneTruncationGrayTensorFunctor X Y).toCatHom
  inv := (oneTruncationGrayTensorInverse X Y).toCatHom
  hom_inv_id := Cat.Hom.ext (oneTruncationGrayTensorFunctor_comp_inverse X Y)
  inv_hom_id := Cat.Hom.ext (oneTruncationGrayTensorInverse_comp_functor X Y)

theorem oneTruncationGrayTensorIso_hom (X Y : DiagSet.{u}) :
    (oneTruncationGrayTensorIso X Y).hom.toFunctor = oneTruncationGrayTensorFunctor X Y :=
  rfl

theorem oneTruncationGrayTensorIso_inv (X Y : DiagSet.{u}) :
    (oneTruncationGrayTensorIso X Y).inv.toFunctor = oneTruncationGrayTensorInverse X Y :=
  rfl

theorem oneTruncationGrayTensorFunctor_naturality (f : X ⟶ X') (g : Y ⟶ Y') :
    (oneTruncation.map (grayTensorBifunctor.map ((f, g) : (X, Y) ⟶ (X', Y')))).toFunctor ⋙
        oneTruncationGrayTensorFunctor X' Y' =
      oneTruncationGrayTensorFunctor X Y ⋙
        (oneTruncation.map f).toFunctor.prod (oneTruncation.map g).toFunctor := by
  rw [oneTruncation_map_comp_functor, grayTensorBifunctor_map_grayTensorFst,
    grayTensorBifunctor_map_grayTensorSnd, Functor.map_comp, Functor.map_comp,
    Cat.Hom.comp_toFunctor, Cat.Hom.comp_toFunctor]
  rfl

end Atoms.Diagrammatic
