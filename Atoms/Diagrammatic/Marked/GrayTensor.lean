import Atoms.Diagrammatic.GrayTensor.Functor
import Atoms.Diagrammatic.Marked.Basic
import Atoms.Homotopical.Marked.Cellular
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

open CategoryTheory Limits Opposite Atoms.Shape Atoms.Homotopical

universe w w' u

namespace Atoms.Diagrammatic

def tensorMask (pseudo : Bool) (X Y : MarkedDiagSet.{u}) (U V : Atom)
    (x : diagram X.underlying U) (y : diagram Y.underlying V) : Prop :=
  x ∈ X.marked U ∨ y ∈ Y.marked V ∨
    (pseudo = true ∧ 0 < U.dimension ∧ 0 < V.dimension)

def tensorMarked (pseudo : Bool) (X Y : MarkedDiagSet.{u}) (T : Atom)
    (z : diagram (grayTensor X.underlying Y.underlying) T) : Prop :=
  IsDegenerate (grayTensor X.underlying Y.underlying) z ∨
    ∃ (U V : Atom) (x : diagram X.underlying U) (y : diagram Y.underlying V)
      (e : T ≅ Atom.grayTensor U V),
      tensorMask pseudo X Y U V x y ∧
      z = (grayTensor X.underlying Y.underlying).map e.hom.op (grayTensorCell x y)

private theorem pos_of_tensorMask {pseudo : Bool} {X Y : MarkedDiagSet.{u}} {U V : Atom}
    {x : diagram X.underlying U} {y : diagram Y.underlying V} (h : tensorMask pseudo X Y U V x y) :
    0 < (Atom.grayTensor U V).dimension := by
  rw [Atom.dimension_grayTensor]
  rcases h with hx | hy | ⟨-, hU, -⟩
  · have : 0 < U.dimension := X.markable U x hx
    omega
  · have : 0 < V.dimension := Y.markable V y hy
    omega
  · omega

def tensorMarking (pseudo : Bool) (X Y : MarkedDiagSet.{u}) :
    MarkedPresheaf.Marking atomMarking (grayTensor X.underlying Y.underlying) where
  marked T := {z | tensorMarked pseudo X Y T z}
  markable := by
    rintro T z (hz | ⟨U, V, x, y, e, hm, -⟩)
    · exact dimension_pos_of_isDegenerate hz
    · change 0 < T.dimension
      rw [Atom.dimension_eq_of_iso e]
      exact pos_of_tensorMask hm
  degenerate := fun _ b p hp y => Or.inl ⟨b, p, y, hp.1, hp.2, rfl⟩
  transport := by
    intro a b e z
    refine (or_congr (isDegenerate_map_iso_iff e z).symm ⟨?_, ?_⟩)
    · rintro ⟨U, V, x, y, e', hm, rfl⟩
      exact ⟨U, V, x, y, e ≪≫ e', hm, (Functor.map_comp_apply _ _ _ _).symm⟩
    · rintro ⟨U, V, x, y, e', hm, hz⟩
      refine ⟨U, V, x, y, e.symm ≪≫ e', hm, ?_⟩
      rw [Iso.trans_hom, op_comp, Functor.map_comp_apply, ← hz, ← Functor.map_comp_apply,
        ← op_comp, Iso.symm_hom, e.inv_hom_id, op_id, Functor.map_id_apply]

noncomputable def markedTensor (pseudo : Bool) (X Y : MarkedDiagSet.{u}) : MarkedDiagSet.{u} :=
  MarkedPresheaf.ofMarking _ (tensorMarking pseudo X Y)

@[simp] theorem mem_marked_markedTensor (pseudo : Bool) (X Y : MarkedDiagSet.{u}) (T : Atom)
    (z : diagram (grayTensor X.underlying Y.underlying) T) :
    z ∈ (markedTensor pseudo X Y).marked T ↔ tensorMarked pseudo X Y T z :=
  MarkedPresheaf.mem_marked_ofMarking _ _ _ _

theorem forget_obj_markedTensor (pseudo : Bool) (X Y : MarkedDiagSet.{u}) :
    MarkedPresheaf.forget.obj (markedTensor pseudo X Y) =
      grayTensor (MarkedPresheaf.forget.obj X) (MarkedPresheaf.forget.obj Y) :=
  rfl

private theorem tensorMarked_map {pseudo pseudo' : Bool} {X Y X' Y' : MarkedDiagSet.{u}}
    (f : X.underlying ⟶ X'.underlying) (g : Y.underlying ⟶ Y'.underlying)
    (hfg : ∀ (U V : Atom) (x : diagram X.underlying U) (y : diagram Y.underlying V),
      tensorMask pseudo X Y U V x y →
        tensorMask pseudo' X' Y' U V (f.app (op U) x) (g.app (op V) y))
    {T : Atom} {z : diagram (grayTensor X.underlying Y.underlying) T}
    (hz : tensorMarked pseudo X Y T z) :
    tensorMarked pseudo' X' Y' T ((grayTensorBifunctor.map (f, g)).app (op T) z) := by
  rcases hz with hz | ⟨U, V, x, y, e, hm, rfl⟩
  · exact Or.inl (isDegenerate_app _ hz)
  · refine Or.inr ⟨U, V, f.app (op U) x, g.app (op V) y, e, hfg U V x y hm, ?_⟩
    exact (NatTrans.naturality_apply (grayTensorBifunctor.map (X := (X.underlying, Y.underlying))
      (Y := (X'.underlying, Y'.underlying)) (f, g)) e.hom.op (grayTensorCell x y)).trans
      (congrArg _ (grayTensorCell_naturality f g x y))

noncomputable def markedTensorMap (pseudo : Bool) {X Y X' Y' : MarkedDiagSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') : markedTensor pseudo X Y ⟶ markedTensor pseudo X' Y' :=
  MarkedPresheaf.homMk
    (grayTensorBifunctor.map (MarkedPresheaf.forget.map f, MarkedPresheaf.forget.map g))
    (by
      intro T z hz
      exact (mem_marked_markedTensor pseudo X' Y' T _).2
        (tensorMarked_map (X := X) (Y := Y) (X' := X') (Y' := Y') (MarkedPresheaf.forget.map f)
          (MarkedPresheaf.forget.map g) (fun U V x y => Or.imp (MarkedPresheaf.map_mem_marked f)
            (Or.imp_left (MarkedPresheaf.map_mem_marked g)))
          ((mem_marked_markedTensor pseudo X Y T z).1 hz)))

@[simp] theorem forget_map_markedTensorMap (pseudo : Bool) {X Y X' Y' : MarkedDiagSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    MarkedPresheaf.forget.map (markedTensorMap pseudo f g) =
      grayTensorBifunctor.map (MarkedPresheaf.forget.map f, MarkedPresheaf.forget.map g) :=
  rfl

theorem forget_map_markedTensorMap_app (pseudo : Bool) {X Y X' Y' : MarkedDiagSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') {T U V : Atom} (k : T ⟶ Atom.grayTensor U V)
    (x : diagram X.underlying U) (y : diagram Y.underlying V) :
    (MarkedPresheaf.forget.map (markedTensorMap pseudo f g)).app (op T)
        ((grayTensor X.underlying Y.underlying).map k.op (grayTensorCell x y)) =
      (grayTensor X'.underlying Y'.underlying).map k.op
        (grayTensorCell ((MarkedPresheaf.forget.map f).app (op U) x)
          ((MarkedPresheaf.forget.map g).app (op V) y)) :=
  (NatTrans.naturality_apply (grayTensorBifunctor.map (X := (X.underlying, Y.underlying))
    (Y := (X'.underlying, Y'.underlying)) (MarkedPresheaf.forget.map f,
      MarkedPresheaf.forget.map g)) k.op (grayTensorCell x y)).trans
    (congrArg _ (grayTensorCell_naturality _ _ x y))

noncomputable def markedTensorBifunctor (pseudo : Bool) :
    MarkedDiagSet.{u} × MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u} where
  obj X := markedTensor pseudo X.1 X.2
  map f := markedTensorMap pseudo f.1 f.2
  map_id X := MarkedPresheaf.hom_ext (by
    simp only [markedTensorMap, prod_id_fst, prod_id_snd]
    exact grayTensorBifunctor.map_id _)
  map_comp f g := MarkedPresheaf.hom_ext (by
    simp only [markedTensorMap, prod_comp_fst, prod_comp_snd, Functor.map_comp]
    exact grayTensorBifunctor.map_comp (X := (_, _)) (Y := (_, _)) (Z := (_, _))
      (MarkedPresheaf.forget.map f.1, MarkedPresheaf.forget.map f.2)
      (MarkedPresheaf.forget.map g.1, MarkedPresheaf.forget.map g.2))

noncomputable abbrev tensorRight (pseudo : Bool) (X : MarkedDiagSet.{u}) :=
  (Functor.curry.obj (markedTensorBifunctor pseudo)).flip.obj X

noncomputable abbrev tensorLeft (pseudo : Bool) (X : MarkedDiagSet.{u}) :=
  (Functor.curry.obj (markedTensorBifunctor pseudo)).obj X

noncomputable def grayToPseudo (X Y : MarkedDiagSet.{u}) :
    markedTensor false X Y ⟶ markedTensor true X Y :=
  MarkedPresheaf.homMk (𝟙 _) (by
    intro T z hz
    refine (mem_marked_markedTensor _ _ _ _ _).2
      (((mem_marked_markedTensor _ _ _ _ _).1 hz).imp_right ?_)
    rintro ⟨U, V, x, y, e, hm, rfl⟩
    exact ⟨U, V, x, y, e, hm.imp_right (Or.imp_right fun h => absurd h.1 Bool.false_ne_true), rfl⟩)

noncomputable abbrev markedGrayTensor (X Y : MarkedDiagSet.{u}) : MarkedDiagSet.{u} :=
  markedTensor false X Y

noncomputable abbrev pseudoGrayTensor (X Y : MarkedDiagSet.{u}) : MarkedDiagSet.{u} :=
  markedTensor true X Y

noncomputable def markedTensorBifunctorCompForgetIso (pseudo : Bool) :
    markedTensorBifunctor pseudo ⋙ MarkedPresheaf.forget ≅
      (MarkedPresheaf.forget.prod MarkedPresheaf.forget) ⋙ grayTensorBifunctor :=
  Iso.refl _

@[simp] theorem forget_map_grayToPseudo (X Y : MarkedDiagSet.{u}) :
    MarkedPresheaf.forget.map (grayToPseudo X Y) = 𝟙 _ :=
  rfl

instance isIso_forget_map_grayToPseudo (X Y : MarkedDiagSet.{u}) :
    IsIso (MarkedPresheaf.forget.map (grayToPseudo X Y)) :=
  ⟨⟨𝟙 _, (Category.comp_id _).trans (forget_map_grayToPseudo X Y),
    (Category.id_comp _).trans (forget_map_grayToPseudo X Y)⟩⟩

@[reassoc] theorem grayToPseudo_naturality {X Y X' Y' : MarkedDiagSet.{u}} (f : X ⟶ X')
    (g : Y ⟶ Y') :
    markedTensorMap false f g ≫ grayToPseudo X' Y' = grayToPseudo X Y ≫ markedTensorMap true f g :=
  MarkedPresheaf.hom_ext ((MarkedPresheaf.forget.map_comp _ _).trans
    ((Category.comp_id _).trans ((Category.id_comp _).symm.trans
      (MarkedPresheaf.forget.map_comp (grayToPseudo X Y) (markedTensorMap true f g)).symm)))

private theorem not_isIso_grayTensorMap {U V U' V' : Atom} {p : U ⟶ U'} {q : V ⟶ V'}
    (hp : IsCollapseHom p) (hq : IsCollapseHom q) (h : ¬ IsIso p ∨ ¬ IsIso q) :
    ¬ IsIso (Atom.grayTensorMap p q) := by
  intro hpq
  have hd := Atom.dimension_eq_of_iso (asIso (Atom.grayTensorMap p q))
  rw [Atom.dimension_grayTensor, Atom.dimension_grayTensor] at hd
  have h₁ := dimension_le_of_isCollapseHom p hp
  have h₂ := dimension_le_of_isCollapseHom q hq
  rcases h with h | h
  · exact h (isIso_of_isCollapseHom_of_dimension_eq p hp (by omega))
  · exact h (isIso_of_isCollapseHom_of_dimension_eq q hq (by omega))

theorem isDegenerate_grayTensorCell {X Y : DiagSet.{u}} {U V : Atom} {x : diagram X U}
    {y : diagram Y V} (h : IsDegenerate X x ∨ IsDegenerate Y y) :
    IsDegenerate (grayTensor X Y) (grayTensorCell x y) := by
  obtain ⟨U', V', p, q, x', y', hp, hq, hni, rfl, rfl⟩ :
      ∃ (U' V' : Atom) (p : U ⟶ U') (q : V ⟶ V') (x' : diagram X U') (y' : diagram Y V'),
        IsCollapseHom p ∧ IsCollapseHom q ∧ (¬ IsIso p ∨ ¬ IsIso q) ∧
          X.map p.op x' = x ∧ Y.map q.op y' = y := by
    rcases h with ⟨U', p, x', hp, hni, rfl⟩ | ⟨V', q, y', hq, hni, rfl⟩
    · exact ⟨U', V, p, 𝟙 V, x', y, hp, isCollapseHom_of_iso (Iso.refl V), Or.inl hni, rfl,
        by simp⟩
    · exact ⟨U, V', 𝟙 U, q, x, y', isCollapseHom_of_iso (Iso.refl U), hq, Or.inr hni,
        by simp, rfl⟩
  exact ⟨_, Atom.grayTensorMap p q, grayTensorCell x' y',
    Atom.isCollapseHom_grayTensorMap p q hp hq, not_isIso_grayTensorMap hp hq hni,
    (grayTensorCell_restrict p q x' y').symm⟩

theorem tensorMarked_flat_iff (X Y : DiagSet.{u}) (T : Atom) (z : diagram (grayTensor X Y) T) :
    tensorMarked false ((MarkedPresheaf.flat atomMarking).obj X)
      ((MarkedPresheaf.flat atomMarking).obj Y) T z ↔ IsDegenerate (grayTensor X Y) z := by
  refine ⟨?_, Or.inl⟩
  rintro (hz | ⟨U, V, x, y, e, hm, rfl⟩)
  · exact hz
  · refine (isDegenerate_map_iso_iff e _).2 (isDegenerate_grayTensorCell ?_)
    rcases hm with hx | hy | ⟨h, -⟩
    · exact Or.inl ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate X U x).1 hx)
    · exact Or.inr ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate Y V y).1 hy)
    · exact absurd h Bool.false_ne_true

noncomputable def markedTensorFlatIso (X Y : DiagSet.{u}) :
    markedTensor false ((MarkedPresheaf.flat atomMarking).obj X)
      ((MarkedPresheaf.flat atomMarking).obj Y) ≅
      (MarkedPresheaf.flat atomMarking).obj (grayTensor X Y) where
  hom := MarkedPresheaf.homMk (𝟙 (grayTensor X Y)) fun T z hz => by
    have hz' := (tensorMarked_flat_iff X Y T z).1 ((mem_marked_markedTensor _ _ _ T z).1 hz)
    exact (MarkedDiagSet.mem_marked_flat_iff_isDegenerate (grayTensor X Y) T z).2 hz'
  inv := MarkedPresheaf.homMk (𝟙 (grayTensor X Y)) fun T z hz => by
    have hz' := (MarkedDiagSet.mem_marked_flat_iff_isDegenerate (grayTensor X Y) T z).1 hz
    exact (mem_marked_markedTensor false ((MarkedPresheaf.flat atomMarking).obj X)
      ((MarkedPresheaf.flat atomMarking).obj Y) T z).2 ((tensorMarked_flat_iff X Y T z).2 hz')
  hom_inv_id := MarkedPresheaf.hom_ext rfl
  inv_hom_id := MarkedPresheaf.hom_ext rfl

private theorem not_isDegenerate_ball_id (T : Atom) :
    ¬ IsDegenerate (ball.{u} T) (ULift.up (𝟙 T)) := by
  rintro ⟨W, p, ⟨w⟩, hp, hni, h⟩
  let w' : W ⟶ T := w
  have hpw : p ≫ w' = 𝟙 T := congrArg ULift.down h
  have hlt : W.dimension < T.dimension := lt_of_le_of_ne (dimension_le_of_isCollapseHom p hp)
    fun e => hni (isIso_of_isCollapseHom_of_dimension_eq p hp e.symm)
  have htop : w' W.top = T.top := by
    rw [← hp.apply_top, ← ConcreteCategory.comp_apply, hpw, ConcreteCategory.id_apply]
  have hle := (Atom.isMap w').grade_le W.top
  rw [htop, ← T.dimension_eq, ← W.dimension_eq] at hle
  omega

theorem not_isDegenerate_grayTensorCell_ball (U V : Atom) :
    ¬ IsDegenerate (grayTensor (ball.{u} U) (ball.{u} V))
      (grayTensorCell (X := ball.{u} U) (Y := ball.{u} V) (ULift.up (𝟙 U)) (ULift.up (𝟙 V))) := by
  intro h
  have := isDegenerate_app (grayTensorBallIso U V).hom h
  rw [grayTensorBallIso_hom_app_grayTensorCell (𝟙 U) (𝟙 V), Atom.grayTensorMap_id] at this
  exact not_isDegenerate_ball_id _ this

theorem mem_marked_pseudoGrayTensor_flat_ball {U V : Atom} (hU : 0 < U.dimension)
    (hV : 0 < V.dimension) :
    grayTensorCell (X := ball.{u} U) (Y := ball.{u} V) (ULift.up (𝟙 U)) (ULift.up (𝟙 V)) ∈
      (pseudoGrayTensor ((MarkedPresheaf.flat atomMarking).obj (ball.{u} U))
        ((MarkedPresheaf.flat atomMarking).obj (ball.{u} V))).marked (Atom.grayTensor U V) :=
  (mem_marked_markedTensor _ _ _ _ _).2 (Or.inr ⟨U, V, ULift.up (𝟙 U), ULift.up (𝟙 V), Iso.refl _,
    Or.inr (Or.inr ⟨rfl, hU, hV⟩),
    (Functor.map_id_apply (grayTensor (ball.{u} U) (ball.{u} V)) (op (Atom.grayTensor U V))
      _).symm⟩)

private theorem grayTensorBifunctor_map_app_map_grayTensorCell {X Y X' Y' : DiagSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') {T U V : Atom} (k : T ⟶ Atom.grayTensor U V) (x : diagram X U)
    (y : diagram Y V) :
    (grayTensorBifunctor.map (X := (X, Y)) (Y := (X', Y')) (f, g)).app (op T)
        ((grayTensor X Y).map k.op (grayTensorCell x y)) =
      (grayTensor X' Y').map k.op (grayTensorCell (f.app (op U) x) (g.app (op V) y)) :=
  (NatTrans.naturality_apply (grayTensorBifunctor.map (X := (X, Y)) (Y := (X', Y')) (f, g))
    k.op (grayTensorCell x y)).trans (congrArg _ (grayTensorCell_naturality f g x y))

private theorem exists_mem_marked_markedTensor_of_lift (pseudo : Bool) {J : Type*}
    {X Y : J → MarkedDiagSet.{u}} {X' Y' : MarkedDiagSet.{u}} (f : ∀ j, X j ⟶ X')
    (g : ∀ j, Y j ⟶ Y')
    (h : ∀ (U V : Atom) (x' : diagram X'.underlying U) (y' : diagram Y'.underlying V),
      ∃ (j : J) (x : diagram (X j).underlying U) (y : diagram (Y j).underlying V),
        (MarkedPresheaf.forget.map (f j)).app (op U) x = x' ∧
        (MarkedPresheaf.forget.map (g j)).app (op V) y = y' ∧
        (x' ∈ X'.marked U → x ∈ (X j).marked U) ∧ (y' ∈ Y'.marked V → y ∈ (Y j).marked V))
    {T : Atom} {z : diagram (grayTensor X'.underlying Y'.underlying) T}
    (hz : z ∈ (markedTensor pseudo X' Y').marked T) :
    ∃ (j : J) (w : diagram (grayTensor (X j).underlying (Y j).underlying) T),
      w ∈ (markedTensor pseudo (X j) (Y j)).marked T ∧
      (MarkedPresheaf.forget.map (markedTensorMap pseudo (f j) (g j))).app (op T) w = z := by
  rcases (mem_marked_markedTensor _ _ _ _ _).1 hz with
    ⟨W, p, w', hp, hni, rfl⟩ | ⟨U, V, x', y', e, hm, rfl⟩
  · obtain ⟨U, V, x', y', k, rfl⟩ := exists_eq_map_grayTensorCell w'
    obtain ⟨j, x, y, rfl, rfl, -, -⟩ := h U V x' y'
    refine ⟨j, (grayTensor _ _).map (p ≫ k).op (grayTensorCell x y),
      (mem_marked_markedTensor _ _ _ _ _).2 (Or.inl ⟨W, p, _, hp, hni,
        (Functor.map_comp_apply _ _ _ _).symm⟩), ?_⟩
    exact (grayTensorBifunctor_map_app_map_grayTensorCell _ _ _ x y).trans
      (Functor.map_comp_apply _ _ _ _)
  · obtain ⟨j, x, y, rfl, rfl, hx, hy⟩ := h U V x' y'
    exact ⟨j, (grayTensor _ _).map e.hom.op (grayTensorCell x y),
      (mem_marked_markedTensor _ _ _ _ _).2 (Or.inr ⟨U, V, x, y, e, hm.imp hx (Or.imp_left hy),
        rfl⟩), grayTensorBifunctor_map_app_map_grayTensorCell _ _ _ x y⟩

private theorem exists_lift_of_isColimit {J : Type*} [Category J] {K : J ⥤ MarkedDiagSet.{u}}
    {c : Cocone K} (hc : IsColimit c) {V : Atom} (y' : diagram c.pt.underlying V) :
    ∃ (j : J) (y : diagram (K.obj j).underlying V),
      (MarkedPresheaf.forget.map (c.ι.app j)).app (op V) y = y' ∧
        (y' ∈ c.pt.marked V → y ∈ (K.obj j).marked V) := by
  by_cases hy' : y' ∈ c.pt.marked V
  · obtain ⟨j, y, hy, rfl⟩ := MarkedPresheaf.exists_mem_marked_of_isColimit hc hy'
    exact ⟨j, y, rfl, fun _ => hy⟩
  · obtain ⟨j, y, rfl⟩ := MarkedPresheaf.exists_forget_map_eq_of_isColimit hc y'
    exact ⟨j, y, rfl, fun h => absurd h hy'⟩

private noncomputable def tensorLeftCompForgetIso (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    tensorLeft pseudo X ⋙ MarkedPresheaf.forget ≅
      MarkedPresheaf.forget ⋙ grayTensorLeft X.underlying :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun {Y Y'} f =>
    (Category.comp_id _).trans (Eq.trans
      (congrArg (fun a => grayTensorBifunctor.map (X := (X.underlying, Y.underlying))
        (Y := (X.underlying, Y'.underlying)) (a, MarkedPresheaf.forget.map f))
        (MarkedPresheaf.forget.map_id X)) (Category.id_comp _).symm)

instance preservesColimitsOfSize_tensorLeft (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    PreservesColimitsOfSize.{w, w'} (tensorLeft pseudo X) :=
  have : PreservesColimitsOfSize.{w, w'} (tensorLeft pseudo X ⋙ MarkedPresheaf.forget) :=
    preservesColimits_of_natIso (tensorLeftCompForgetIso pseudo X).symm
  ⟨fun {_} _ => ⟨fun {K} => ⟨fun {c} hc => ⟨MarkedPresheaf.isColimitOfForget _
    (isColimitOfPreserves (tensorLeft pseudo X ⋙ MarkedPresheaf.forget) hc)
    fun _ _ hz => exists_mem_marked_markedTensor_of_lift pseudo (X := fun _ => X) (Y := K.obj)
      (X' := X) (Y' := c.pt) (fun _ => 𝟙 X) c.ι.app
      (fun _ _ x' y' => (exists_lift_of_isColimit hc y').imp fun _ ⟨y, hy, hm⟩ =>
        ⟨x', y, rfl, hy, id, hm⟩) hz⟩⟩⟩⟩

private noncomputable def tensorRightUnfolded (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u} where
  obj Y := markedTensor pseudo Y X
  map f := markedTensorMap pseudo f (𝟙 X)
  map_id Y := (markedTensorBifunctor pseudo).map_id (Y, X)
  map_comp f g := (congrArg (fun h => (markedTensorBifunctor pseudo).map (X := (_, X))
      (Y := (_, X)) (f ≫ g, h)) (Category.comp_id (𝟙 X)).symm).trans
    ((markedTensorBifunctor pseudo).map_comp (X := (_, X)) (Y := (_, X)) (Z := (_, X))
      (f, 𝟙 X) (g, 𝟙 X))

private noncomputable def tensorRightUnfoldedCompForgetIso (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    tensorRightUnfolded pseudo X ⋙ MarkedPresheaf.forget ≅
      MarkedPresheaf.forget ⋙ grayTensorRight X.underlying :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun {Y Y'} f =>
    (Category.comp_id _).trans (Eq.trans
      (congrArg (fun a => grayTensorBifunctor.map (X := (Y.underlying, X.underlying))
        (Y := (Y'.underlying, X.underlying)) (MarkedPresheaf.forget.map f, a))
        (MarkedPresheaf.forget.map_id X)) (Category.id_comp _).symm)

private theorem preservesColimitsOfSize_tensorRightUnfolded (pseudo : Bool)
    (X : MarkedDiagSet.{u}) : PreservesColimitsOfSize.{w, w'} (tensorRightUnfolded pseudo X) :=
  have : PreservesColimitsOfSize.{w, w'} (tensorRightUnfolded pseudo X ⋙ MarkedPresheaf.forget) :=
    preservesColimits_of_natIso (tensorRightUnfoldedCompForgetIso pseudo X).symm
  ⟨fun {_} _ => ⟨fun {K} => ⟨fun {c} hc => ⟨MarkedPresheaf.isColimitOfForget _
    (isColimitOfPreserves (tensorRightUnfolded pseudo X ⋙ MarkedPresheaf.forget) hc)
    fun _ _ hz => exists_mem_marked_markedTensor_of_lift pseudo (X := K.obj) (Y := fun _ => X)
      (X' := c.pt) (Y' := X) c.ι.app (fun _ => 𝟙 X)
      (fun _ _ x' y' => (exists_lift_of_isColimit hc x').imp fun _ ⟨x, hx, hm⟩ =>
        ⟨x, y', hx, rfl, hm, id⟩) hz⟩⟩⟩⟩

instance preservesColimitsOfSize_tensorRight (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    PreservesColimitsOfSize.{w, w'} (tensorRight pseudo X) :=
  have := preservesColimitsOfSize_tensorRightUnfolded.{w, w'} pseudo X
  preservesColimits_of_natIso (NatIso.ofComponents (fun _ => Iso.refl _) fun _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm :
      tensorRightUnfolded pseudo X ≅ tensorRight pseudo X)

theorem exists_mem_marked_ι_eq_of_corner (pseudo : Bool) {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}}
    {f₁ : X₁ ⟶ Y₁}
    {f₂ : X₂ ⟶ Y₂} (sq : (Functor.curry.obj (markedTensorBifunctor.{u} pseudo)).PushoutObjObj f₁ f₂)
    {A B : MarkedDiagSet.{u}} (a : A ⟶ Y₁) (b : B ⟶ Y₂) (c : markedTensor pseudo A B ⟶ sq.pt)
    (hc : c ≫ sq.ι = markedTensorMap pseudo a b) {T U V : Atom} (e : T ≅ Atom.grayTensor U V)
    (x : diagram A.underlying U) (y : diagram B.underlying V) (hm : tensorMask pseudo A B U V x y) :
    ∃ w ∈ sq.pt.marked T, (MarkedPresheaf.forget.map sq.ι).app (op T) w =
      (grayTensor Y₁.underlying Y₂.underlying).map e.hom.op
        (grayTensorCell ((MarkedPresheaf.forget.map a).app (op U) x)
          ((MarkedPresheaf.forget.map b).app (op V) y)) := by
  refine ⟨_, MarkedPresheaf.map_mem_marked c ((mem_marked_markedTensor _ _ _ _ _).2
    (Or.inr ⟨U, V, x, y, e, hm, rfl⟩)), ?_⟩
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    ((Functor.map_comp MarkedPresheaf.forget _ _).symm.trans
      (congrArg MarkedPresheaf.forget.map hc)) (op T))
    ((grayTensor A.underlying B.underlying).map e.hom.op (grayTensorCell x y))).trans
      (forget_map_markedTensorMap_app pseudo a b e.hom x y)

end Atoms.Diagrammatic
