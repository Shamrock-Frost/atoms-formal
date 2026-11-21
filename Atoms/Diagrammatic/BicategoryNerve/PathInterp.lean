import Atoms.Diagrammatic.BicategoryNerve.Unit
import Atoms.Diagrammatic.Rewriting.Reading

open CategoryTheory Opposite Order Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape
open CategoryTheory.Bicategory (PathCell pathComp pathComp_mapPath)
open CategoryTheory.FreeBicategory (lift IsStructural)
open scoped CategoryTheory.Bicategory

universe w v u v'

namespace Atoms.Diagrammatic

attribute [local instance high] instFintypeRdc

namespace PastingDiagram

variable {B : Type u} [Bicategory.{w, v} B]

private theorem cancel_iso {C : Type*} [Category C] {X X' Y Y' : C} (e : X' ≅ X) (e' : Y' ≅ Y)
    (φ : X ⟶ Y) : e.inv ≫ (e.hom ≫ φ ≫ e'.inv) ≫ e'.hom = φ := by
  simp

private theorem whisker_nil_eq {V : Type*} [Quiver V] (G : Prefunctor V B) {x y : V}
    {P Q : Quiver.Path x y} (φ : pathComp G P ⟶ pathComp G Q) :
    (Bicategory.pathCompCompIso G P .nil).hom ≫ φ ▷ pathComp G (.nil : Quiver.Path y y) ≫
      (Bicategory.pathCompCompIso G Q .nil).inv = φ := by
  rw [Bicategory.pathCompCompIso_comp_nil, Bicategory.pathCompCompIso_comp_nil]
  simp only [Iso.symm_hom, Iso.symm_inv, Bicategory.pathComp_nil, Bicategory.whiskerRight_id]
  exact cancel_iso _ _ φ

private theorem whisker_nil_left_eq {V : Type*} [Quiver V] (G : Prefunctor V B) {x y : V}
    {P Q : Quiver.Path x y} (φ : pathComp G P ⟶ pathComp G Q) :
    (Bicategory.pathCompCompIso G .nil P).hom ≫ pathComp G (.nil : Quiver.Path x x) ◁ φ ≫
      (Bicategory.pathCompCompIso G .nil Q).inv =
      eqToHom (congrArg (pathComp G) (Quiver.Path.nil_comp P)) ≫ φ ≫
        eqToHom (congrArg (pathComp G) (Quiver.Path.nil_comp Q)).symm := by
  have h₁ : (Bicategory.pathCompCompIso G .nil P).hom =
      eqToHom (congrArg (pathComp G) (Quiver.Path.nil_comp P)) ≫ (λ_ (pathComp G P)).inv :=
    (Iso.eq_comp_inv _).2 (Bicategory.pathCompCompIso_nil_comp G P)
  have h₂ : (Bicategory.pathCompCompIso G .nil Q).inv =
      (λ_ (pathComp G Q)).hom ≫ eqToHom (congrArg (pathComp G) (Quiver.Path.nil_comp Q)).symm := by
    refine Iso.inv_ext ((Category.assoc _ _ _).symm.trans ((congrArg
      (· ≫ eqToHom (congrArg (pathComp G) (Quiver.Path.nil_comp Q)).symm)
      (Bicategory.pathCompCompIso_nil_comp G Q)).trans ?_))
    simp
  rw [h₁, h₂]
  simp

end PastingDiagram

namespace Layered.Signature

variable {S' : Signature.{0}} {S : Signature.{v'}} (fp : S'.Pt → S.Pt) (fe : S'.Ed → S.Ed)
  (hsrc : ∀ e, S.edgeSource (fe e) = fp (S'.edgeSource e))
  (htgt : ∀ e, S.edgeTarget (fe e) = fp (S'.edgeTarget e))

def mapEdge : Edge S'.Pt S'.Ed → Edge S.Pt S.Ed
  | .gen e => .gen (fe e)
  | .unit x => .unit (fp x)

include hsrc in
theorem src_mapEdge : ∀ e, S.src (mapEdge fp fe e) = fp (S'.src e)
  | .gen e => hsrc e
  | .unit _ => rfl

include htgt in
theorem tgt_mapEdge : ∀ e, S.tgt (mapEdge fp fe e) = fp (S'.tgt e)
  | .gen e => htgt e
  | .unit _ => rfl

def pathMap : Prefunctor S'.PathQuiver S.PathQuiver where
  obj x := fp (x : S'.Pt)
  map {x y} (e : {e : Edge S'.Pt S'.Ed // S'.src e = x ∧ S'.tgt e = y}) :=
    (⟨mapEdge fp fe e.1, (src_mapEdge fp fe hsrc e.1).trans (congrArg fp e.2.1),
      (tgt_mapEdge fp fe htgt e.1).trans (congrArg fp e.2.2)⟩ :
        {e : Edge S.Pt S.Ed // S.src e = fp x ∧ S.tgt e = fp y})

def genMap : Prefunctor S'.GenQuiver (FreeBicategory S.GenQuiver) :=
  S'.mkPrefunctor (V := FreeBicategory S.GenQuiver) fp fun e =>
    Quiver.homOfEq (FreeBicategory.Hom.of (B := S.GenQuiver)
      (⟨fe e, rfl, rfl⟩ : {e' : S.Ed // S.edgeSource e' = S.edgeSource (fe e) ∧
        S.edgeTarget e' = S.edgeTarget (fe e)})) (hsrc e) (htgt e)

private theorem lift_map_homOfEq_heq {W V : Type*} [Quiver W] [Quiver V]
    (G : Prefunctor W (FreeBicategory V)) {a b a' b' : FreeBicategory W} (f : a ⟶ b) (ha : a = a')
    (hb : b = b') : (lift G).map (Quiver.homOfEq f ha hb) ≍ (lift G).map f := by
  subst ha hb
  rfl

private theorem lift_map_heq {W : Type*} [Quiver W] {C : Type*} [Bicategory C]
    (G : Prefunctor W C) {a b a' b' : FreeBicategory W} {f : a ⟶ b} {f' : a' ⟶ b'}
    (ha : a = a') (hb : b = b') (h : f ≍ f') : (lift G).map f ≍ (lift G).map f' := by
  subst ha hb
  obtain rfl := eq_of_heq h
  rfl

include hsrc htgt in
theorem pathMap_comp_freePrefunctor :
    pathMap fp fe hsrc htgt ⋙q S.freePrefunctor =
      S'.freePrefunctor ⋙q (lift (genMap fp fe hsrc htgt)).toPrefunctor := by
  refine Prefunctor.hext (fun _ => rfl) fun x y e => ?_
  obtain ⟨_ | z, h⟩ := e
  · obtain ⟨rfl, rfl⟩ := h
    rename_i e
    have key : ∀ {a b a' b' : S.Pt} (p : S.edgeSource (fe e) = a ∧ S.edgeTarget (fe e) = b)
        (p' : S.edgeSource (fe e) = a' ∧ S.edgeTarget (fe e) = b'),
        FreeBicategory.Hom.of (B := S.GenQuiver) (⟨fe e, p⟩ : {e' : S.Ed //
          S.edgeSource e' = a ∧ S.edgeTarget e' = b}) ≍
        FreeBicategory.Hom.of (B := S.GenQuiver) (⟨fe e, p'⟩ : {e' : S.Ed //
          S.edgeSource e' = a' ∧ S.edgeTarget e' = b'}) := by
      rintro _ _ _ _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
      rfl
    have hr : (S'.freePrefunctor ⋙q (lift (genMap fp fe hsrc htgt)).toPrefunctor).map
        (⟨.gen e, rfl, rfl⟩ : {e' : Edge S'.Pt S'.Ed // S'.src e' = S'.edgeSource e ∧
          S'.tgt e' = S'.edgeTarget e}) =
        Quiver.homOfEq (V := FreeBicategory S.GenQuiver) (Quiver.homOfEq
          (V := FreeBicategory S.GenQuiver) (FreeBicategory.Hom.of (B := S.GenQuiver)
          (⟨fe e, rfl, rfl⟩ : {e' : S.Ed // S.edgeSource e' = S.edgeSource (fe e) ∧
            S.edgeTarget e' = S.edgeTarget (fe e)})) (hsrc e) (htgt e))
          (congrArg fp rfl) (congrArg fp rfl) := rfl
    refine (key _ ⟨rfl, rfl⟩).trans ?_
    exact ((Quiver.homOfEq_heq _ _ _).trans (Quiver.homOfEq_heq _ _ _)).symm.trans
      (heq_of_eq hr.symm)
  · obtain ⟨rfl, rfl⟩ := h
    have hl : (pathMap fp fe hsrc htgt ⋙q S.freePrefunctor).map
        (⟨.unit z, rfl, rfl⟩ : {e' : Edge S'.Pt S'.Ed // S'.src e' = z ∧ S'.tgt e' = z}) =
        Quiver.homOfEq (V := FreeBicategory S.GenQuiver) (FreeBicategory.Hom.id (B := S.GenQuiver)
          (fp z)) rfl rfl := rfl
    have hr : (S'.freePrefunctor ⋙q (lift (genMap fp fe hsrc htgt)).toPrefunctor).map
        (⟨.unit z, rfl, rfl⟩ : {e' : Edge S'.Pt S'.Ed // S'.src e' = z ∧ S'.tgt e' = z}) =
        (lift (genMap fp fe hsrc htgt)).map (Quiver.homOfEq (V := FreeBicategory S'.GenQuiver)
          (FreeBicategory.Hom.id (B := S'.GenQuiver) z) rfl rfl) := rfl
    exact (heq_of_eq hl).trans ((heq_of_eq hr).trans
      (lift_map_homOfEq_heq _ _ _ _)).symm.symm

variable [DecidableEq S'.Pt] [DecidableEq S.Pt]

include hsrc htgt in
theorem walk_map : ∀ {x y : S'.Pt} {l : List (Edge S'.Pt S'.Ed)}, S'.walk x l = some y →
    S.walk (fp x) (l.map (mapEdge fp fe)) = some (fp y)
  | _, _, [], h => by
    obtain rfl := Option.some.inj h
    rfl
  | _, _, e :: l, h => by
    obtain ⟨rfl, h'⟩ := S'.walk_cons_eq_some.1 h
    exact S.walk_cons_eq_some.2 ⟨src_mapEdge fp fe hsrc e,
      (tgt_mapEdge fp fe htgt e) ▸ walk_map h'⟩

private theorem comp_path_heq {V : Type*} [Quiver V] {a b c a' b' c' : V} {p : Quiver.Path a b}
    {q : Quiver.Path b c} {p' : Quiver.Path a' b'} {q' : Quiver.Path b' c'} (ha : a = a')
    (hb : b = b') (hc : c = c') (hp : p ≍ p') (hq : q ≍ q') : p.comp q ≍ p'.comp q' := by
  subst ha hb hc
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq hq
  rfl

include hsrc htgt in
theorem toPath_map_heq : ∀ {x y : S'.Pt} {l : List (Edge S'.Pt S'.Ed)} (h : S'.walk x l = some y)
    {z w : S.Pt}, z = fp x → w = fp y → ∀ (h' : S.walk z (l.map (mapEdge fp fe)) = some w),
    S.toPath _ h' ≍ (pathMap fp fe hsrc htgt).mapPath (S'.toPath l h)
  | _, _, [], h, _, _, hz, hw, h' => by
    obtain rfl := Option.some.inj h
    subst hz hw
    rfl
  | x, y, e :: l, h, z, w, hz, hw, h' => by
    obtain ⟨rfl, h₁⟩ := S'.walk_cons_eq_some.1 h
    subst hz hw
    have ih := toPath_map_heq h₁ (tgt_mapEdge fp fe htgt e) rfl (S.walk_cons_eq_some.1 h').2
    refine HEq.trans ?_ (heq_of_eq (Prefunctor.mapPath_comp _ _ _).symm)
    refine comp_path_heq rfl (tgt_mapEdge fp fe htgt e) rfl ?_ ih
    refine HEq.trans ?_ (heq_of_eq (Prefunctor.mapPath_toPath _ _).symm)
    refine PastingDiagram.toPath_heq rfl (tgt_mapEdge fp fe htgt e) ?_
    have key : ∀ {a b a' b' : S.Pt} (p : S.src (mapEdge fp fe e) = a ∧ S.tgt (mapEdge fp fe e) = b)
        (p' : S.src (mapEdge fp fe e) = a' ∧ S.tgt (mapEdge fp fe e) = b'),
        (⟨mapEdge fp fe e, p⟩ : {e' : Edge S.Pt S.Ed // S.src e' = a ∧ S.tgt e' = b}) ≍
          (⟨mapEdge fp fe e, p'⟩ : {e' : Edge S.Pt S.Ed // S.src e' = a' ∧ S.tgt e' = b'}) := by
      rintro _ _ _ _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
      rfl
    exact key _ _

omit [DecidableEq S'.Pt] [DecidableEq S.Pt] in
include htgt hsrc in
theorem cellType_unitor_mapEdge (k : UnitorKind) (e : Edge S'.Pt S'.Ed) :
    S.cellType (.unitor k (mapEdge fp fe e) : Cell S.Pt S.Ed S.Ce) =
      ((S'.cellType (.unitor k e : Cell S'.Pt S'.Ed S'.Ce)).1.map (mapEdge fp fe),
        (S'.cellType (.unitor k e : Cell S'.Pt S'.Ed S'.Ce)).2.map (mapEdge fp fe)) := by
  have hs := src_mapEdge fp fe hsrc e
  have ht := tgt_mapEdge fp fe htgt e
  cases k <;> simp only [cellType, unitPath, UnitorKind.removes, UnitorKind.side, cond_true,
    cond_false, List.map_cons, List.map_nil, hs, ht] <;> rfl

end Layered.Signature

namespace Layered.Signature.PathInterp

variable {B : Type u} [Bicategory.{w, v} B] {S : Signature.{v'}}
  (I : S.PathInterp (bicategoryNerve.{w, v, u} B))

def pointObj (x : S.Pt) : B :=
  (I.point x).1.toPrefunctor.obj atomPoint.top

theorem dimension_edge (e : S.Ed) : (I.edge e).1.dimension = 1 :=
  (I.hasRoundType_edge e).dim_eq.trans (congrArg (· + 1) dimension_atomPoint)

def edgeTop (e : S.Ed) :
    Quiver.Hom (V := EdgeQuiver (I.edge e).1.ogp)
      (vertex (.Iic (I.edge e).1.top) ((I.edge e).1.isRDC _) false)
      (vertex (.Iic (I.edge e).1.top) ((I.edge e).1.isRDC _) true) :=
  ⟨(I.edge e).1.top, ((I.edge e).1.dimension_eq.symm.trans (I.dimension_edge e)),
    boundary_zero_eq_Iic_vertex _ _ false, boundary_zero_eq_Iic_vertex _ _ true⟩

theorem obj_vertex_edge (e : S.Ed) (α : Bool) :
    (I.edge e).2.1.toPrefunctor.obj (vertex (.Iic (I.edge e).1.top) ((I.edge e).1.isRDC _) α) =
      I.pointObj (cond α (S.edgeTarget e) (S.edgeSource e)) := by
  have h := (I.hasRoundType_edge e).equiv_boundary_cond dimension_atomPoint α
  have hv : (I.edge e).1.ogp.boundary ⊤ 0 α =
      .Iic (vertex (.Iic (I.edge e).1.top) ((I.edge e).1.isRDC _) α) := by
    have h0 := boundary_zero_eq_Iic_vertex (P := (I.edge e).1.ogp) (.Iic (I.edge e).1.top)
      ((I.edge e).1.isRDC _) α
    have h1 : (I.edge e).1.ogp.boundary ⊤ 0 α =
        (I.edge e).1.ogp.boundary (.Iic (I.edge e).1.top) 0 α := by rw [Atom.Iic_top]
    exact h1.trans h0
  refine (PastingDiagram.obj_ofCell (I.edge e).2
    (vertex (.Iic (I.edge e).1.top) ((I.edge e).1.isRDC _) α)).symm.trans ?_
  cases α
  · exact PastingDiagram.obj_vertex_of_equiv_boundary _ false h hv
  · exact PastingDiagram.obj_vertex_of_equiv_boundary _ true h hv

def toGenPrefunctor : Prefunctor S.GenQuiver B :=
  S.mkPrefunctor I.pointObj fun e => Quiver.homOfEq ((I.edge e).2.1.toPrefunctor.map (I.edgeTop e))
    (I.obj_vertex_edge e false) (I.obj_vertex_edge e true)

abbrev label : Prefunctor S.PathQuiver B :=
  S.freePrefunctor ⋙q (lift I.toGenPrefunctor).toPrefunctor

theorem nerveComposite_ofEdge_gen (g : S.Ed) (hd : (I.ofEdge (.gen g)).dim ≤ 2) :
    (I.ofEdge (.gen g)).nerveComposite hd =
      ⟨I.pointObj (S.edgeSource g), I.pointObj (S.edgeTarget g),
        Quiver.Hom.toPath (I.label.map (⟨.gen g, rfl, rfl⟩ :
          Quiver.Hom (V := S.PathQuiver) (S.edgeSource g) (S.edgeTarget g))),
        Quiver.Hom.toPath (I.label.map (⟨.gen g, rfl, rfl⟩ :
          Quiver.Hom (V := S.PathQuiver) (S.edgeSource g) (S.edgeTarget g))), 𝟙 _⟩ := by
  have hd₁ : krullDim (LowerSet.Iic (I.edge g).1.top) ≤ 1 := by
    rw [LowerSet.krullDim_Iic, (I.edge g).1.dimension_eq.symm.trans (I.dimension_edge g)]
    rfl
  have hU := (I.edge g).1.isRDC (I.edge g).1.top
  refine (PastingDiagram.nerveComposite_ofCell (I.edge g).2 hd
    (boundary_zero_eq_Iic_vertex _ hU false) (boundary_zero_eq_Iic_vertex _ hU true)
    (isLayerOrder_nil hd₁)).trans ?_
  rw [Labelling.pathCell_of_krullDim_le_one _ _ _ _ _ hd₁, pathOf_Iic_of_grade_eq_one
      ((I.edge g).1.dimension_eq.symm.trans (I.dimension_edge g)), Prefunctor.mapPath_toPath]
  have hm := PastingDiagram.toPath_heq (I.obj_vertex_edge g false) (I.obj_vertex_edge g true)
    (Quiver.homOfEq_heq (I.obj_vertex_edge g false) (I.obj_vertex_edge g true)
      ((I.edge g).2.1.toPrefunctor.map (I.edgeTop g))).symm
  exact PathCell.ext (I.obj_vertex_edge g false) (I.obj_vertex_edge g true) hm hm
    (PastingDiagram.id_pathComp_heq (I.obj_vertex_edge g false) (I.obj_vertex_edge g true) hm)

theorem nerveComposite_ofEdge (e : Edge S.Pt S.Ed) (hd : (I.ofEdge e).dim ≤ 2) :
    (I.ofEdge e).nerveComposite hd =
      ⟨I.pointObj (S.src e), I.pointObj (S.tgt e),
        Quiver.Hom.toPath (I.label.map (⟨e, rfl, rfl⟩ :
          Quiver.Hom (V := S.PathQuiver) (S.src e) (S.tgt e))),
        Quiver.Hom.toPath (I.label.map (⟨e, rfl, rfl⟩ :
          Quiver.Hom (V := S.PathQuiver) (S.src e) (S.tgt e))), 𝟙 _⟩ := by
  cases e with
  | gen g => exact I.nerveComposite_ofEdge_gen g hd
  | unit p => exact PastingDiagram.nerveComposite_unit_ofCell_point (I.point p) hd

variable [DecidableEq S.Pt]

theorem nerveComposite_pathCons {e : Edge S.Pt S.Ed} {p : List (Edge S.Pt S.Ed)} {x y : S.Pt}
    (h : S.walk x (e :: p) = some y) (hd : (I.pathCons e p).dim ≤ 2) :
    (I.pathCons e p).nerveComposite hd =
      ⟨I.pointObj x, I.pointObj y, I.label.mapPath (S.toPath (e :: p) h),
        I.label.mapPath (S.toPath (e :: p) h), 𝟙 _⟩ := by
  induction p generalizing e x with
  | nil =>
    obtain ⟨rfl, h'⟩ := S.walk_cons_eq_some.1 h
    obtain rfl : S.tgt e = y := Option.some.inj h'
    exact I.nerveComposite_ofEdge e hd
  | cons f p ih =>
    obtain ⟨rfl, h'⟩ := S.walk_cons_eq_some.1 h
    obtain ⟨hf, h''⟩ := S.walk_cons_eq_some.1 h'
    have hsq := I.spans_pathCons h''
    rw [hf] at hsq
    have hpst := (I.spans_of_hasRoundType (I.hasRoundType_ofEdge e)).pastable hsq
    have hu : (I.ofEdge e).dim ≤ 2 := (I.dim_ofEdge e).trans_le one_le_two
    have hv : (I.pathCons f p).dim ≤ 2 := (I.dim_pathCons h'').trans_le one_le_two
    have hw : ((I.ofEdge e).paste (I.pathCons f p) 0 hpst).dim ≤ 2 := by
      rw [PastingDiagram.dim_paste, I.dim_ofEdge, I.dim_pathCons h'']
      exact one_le_two
    have hc : I.pathCons e (f :: p) = (I.ofEdge e).paste (I.pathCons f p) 0 hpst :=
      PastingDiagram.pasteOr_of hpst
    refine (PastingDiagram.nerveComposite_congr (PastingDiagram.equiv_of_eq hc) hd hw).trans
      ((PastingDiagram.nerveComposite_pasteAlong_zero _ _ _ _ hu hv hw
      (I.nerveComposite_ofEdge e hu) (ih h' hv)).trans ?_)
    have hP : I.label.mapPath (S.toPath (e :: f :: p) h) =
        (Quiver.Hom.toPath (I.label.map (⟨e, rfl, rfl⟩ :
          Quiver.Hom (V := S.PathQuiver) (S.src e) (S.tgt e)))).comp
          (I.label.mapPath (S.toPath (f :: p) h')) :=
      (Prefunctor.mapPath_comp _ _ _).trans (congrArg (fun q => Quiver.Path.comp q
        (I.label.mapPath (S.toPath (f :: p) h'))) (Prefunctor.mapPath_toPath _ _))
    rw [hP]
    simp only [Bicategory.id_whiskerRight, Bicategory.whiskerLeft_id, Category.id_comp,
      Iso.hom_inv_id]
    rfl

theorem nerveComposite_path {p : List (Edge S.Pt S.Ed)} (hp : p ≠ []) {x y : S.Pt}
    (h : S.pathEnds p = some (x, y)) (hd : (I.path p hp).dim ≤ 2) :
    (I.path p hp).nerveComposite hd =
      ⟨I.pointObj x, I.pointObj y, I.label.mapPath (S.toPath p (S.walk_of_pathEnds h)),
        I.label.mapPath (S.toPath p (S.walk_of_pathEnds h)), 𝟙 _⟩ := by
  obtain _ | ⟨e, p⟩ := p
  · exact absurd rfl hp
  exact I.nerveComposite_pathCons _ hd

theorem nerveComposite_whisker_true {x : PastingDiagram (bicategoryNerve.{w, v, u} B)}
    {a b c : S.Pt} (hx : I.Spans x a b) (hxd : x.dim ≤ 2)
    {P Q : Quiver.Path (V := S.PathQuiver) a b} {φ : pathComp I.label P ⟶ pathComp I.label Q}
    (hφ : x.nerveComposite hxd = PathCell.ofHom I.label P Q φ) {w : List (Edge S.Pt S.Ed)}
    (hw : S.walk b w = some c) (hd : (I.whisker true w x).dim ≤ 2) :
    (I.whisker true w x).nerveComposite hd = PathCell.ofHom I.label
      (P.comp (S.toPath w hw)) (Q.comp (S.toPath w hw))
      ((Bicategory.pathCompCompIso I.label P (S.toPath w hw)).hom ≫
        φ ▷ pathComp I.label (S.toPath w hw) ≫
          (Bicategory.pathCompCompIso I.label Q (S.toPath w hw)).inv) := by
  obtain _ | ⟨f, w⟩ := w
  · obtain rfl : b = c := Option.some.inj hw
    exact hφ.trans (congrArg (PathCell.ofHom I.label P Q) (PastingDiagram.whisker_nil_eq _ φ).symm)
  obtain ⟨hf, hw'⟩ := S.walk_cons_eq_some.1 hw
  have hsp := I.spans_pathCons hw'
  rw [hf] at hsp
  have hp := hx.pastable hsp
  have hc : I.whisker true (f :: w) x = x.paste (I.pathCons f w) 0 hp :=
    PastingDiagram.pasteOr_of hp
  have hv : (I.pathCons f w).dim ≤ 2 := (I.dim_pathCons hw').trans_le one_le_two
  have hw₂ : (x.paste (I.pathCons f w) 0 hp).dim ≤ 2 := hc ▸ hd
  have hy := (I.nerveComposite_pathCons hw hv).trans
    (PathCell.ofHom_id (G := I.label) (S.toPath (f :: w) hw)).symm
  refine (PastingDiagram.nerveComposite_congr (PastingDiagram.equiv_of_eq hc) hd hw₂).trans
    ((PastingDiagram.nerveComposite_pasteAlong_zero _ _ _ _ hxd hv hw₂ hφ hy).trans
      ((PathCell.ofHom_whisker φ (𝟙 _)).trans (congrArg (PathCell.ofHom I.label _ _) ?_)))
  simp only [Bicategory.whiskerLeft_id, Category.comp_id]

theorem nerveComposite_whisker_false {x : PastingDiagram (bicategoryNerve.{w, v, u} B)}
    {a b c : S.Pt} (hx : I.Spans x a b) (hxd : x.dim ≤ 2)
    {P Q : Quiver.Path (V := S.PathQuiver) a b} {φ : pathComp I.label P ⟶ pathComp I.label Q}
    (hφ : x.nerveComposite hxd = PathCell.ofHom I.label P Q φ) {w : List (Edge S.Pt S.Ed)}
    (hw : S.walk c w = some a) (hd : (I.whisker false w x).dim ≤ 2) :
    (I.whisker false w x).nerveComposite hd = PathCell.ofHom I.label
      ((S.toPath w hw).comp P) ((S.toPath w hw).comp Q)
      ((Bicategory.pathCompCompIso I.label (S.toPath w hw) P).hom ≫
        pathComp I.label (S.toPath w hw) ◁ φ ≫
          (Bicategory.pathCompCompIso I.label (S.toPath w hw) Q).inv) := by
  obtain _ | ⟨f, w⟩ := w
  · obtain rfl : c = a := Option.some.inj hw
    refine hφ.trans (Eq.trans ?_ (congrArg (PathCell.ofHom I.label _ _)
      (PastingDiagram.whisker_nil_left_eq _ φ).symm))
    exact (PathCell.ofHom_eqToHom (Quiver.Path.nil_comp P) (Quiver.Path.nil_comp Q).symm φ).symm
  obtain ⟨hf, hw'⟩ := S.walk_cons_eq_some.1 hw
  have hsp := I.spans_pathCons hw'
  rw [hf] at hsp
  have hp := hsp.pastable hx
  have hc : I.whisker false (f :: w) x = (I.pathCons f w).paste x 0 hp :=
    PastingDiagram.pasteOr_of hp
  have hv : (I.pathCons f w).dim ≤ 2 := (I.dim_pathCons hw').trans_le one_le_two
  have hw₂ : ((I.pathCons f w).paste x 0 hp).dim ≤ 2 := hc ▸ hd
  have hy := (I.nerveComposite_pathCons hw hv).trans
    (PathCell.ofHom_id (G := I.label) (S.toPath (f :: w) hw)).symm
  refine (PastingDiagram.nerveComposite_congr (PastingDiagram.equiv_of_eq hc) hd hw₂).trans
    ((PastingDiagram.nerveComposite_pasteAlong_zero _ _ _ _ hv hxd hw₂ hy hφ).trans
      ((PathCell.ofHom_whisker (𝟙 _) φ).trans (congrArg (PathCell.ofHom I.label _ _) ?_)))
  simp only [Bicategory.id_whiskerRight, Category.id_comp]

theorem exists_nerveComposite_unitorDiagram (k : UnitorKind) (e : Edge S.Pt S.Ed)
    (hc : (S.pathEnds (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1).isSome)
    (hs : S.walk ((S.pathEnds (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1).get hc).1
      (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1 =
      some ((S.pathEnds (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1).get hc).2)
    (ht : S.walk ((S.pathEnds (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1).get hc).1
      (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).2 =
      some ((S.pathEnds (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1).get hc).2)
    (hd : (I.unitorDiagram k e).dim ≤ 2) :
    ∃ θ, (I.unitorDiagram k e).nerveComposite hd =
      ⟨I.pointObj ((S.pathEnds (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1).get hc).1,
        I.pointObj ((S.pathEnds (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1).get hc).2,
        I.label.mapPath (S.toPath _ hs), I.label.mapPath (S.toPath _ ht), θ⟩ := by
  have hT := I.hasRoundType_unitorDiagram k e
  have hE : S.pathEnds (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1 =
      some ((S.pathEnds (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1).get hc) :=
    (Option.some_get hc).symm
  have hE' : S.pathEnds (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).2 =
      some ((S.pathEnds (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1).get hc) :=
    S.pathEnds_eq_some_iff.2 ⟨(S.isPath_cellType_unitor_snd k e).ne_nil, ht⟩
  have hb (α : Bool) : ((I.unitorDiagram k e).boundary 1 α).dim ≤ 2 :=
    (I.unitorDiagram k e).shape.dimension_boundary_le 1 α |>.trans one_le_two
  have e₀ : ((I.unitorDiagram k e).boundary 1 false).Equiv
      (I.path _ (S.isPath_cellType_unitor_fst k e).ne_nil) :=
    hT.equiv_boundary_cond (I.dim_path (S.isPath_cellType_unitor_fst k e)) false
  have e₁ : ((I.unitorDiagram k e).boundary 1 true).Equiv
      (I.path _ (S.isPath_cellType_unitor_snd k e).ne_nil) :=
    hT.equiv_boundary_cond (I.dim_path (S.isPath_cellType_unitor_fst k e)) true
  have h₀ := (PastingDiagram.nerveComposite_boundary_one _ hd false (hb false)).symm.trans
    ((PastingDiagram.nerveComposite_congr e₀ (hb false)
      ((I.dim_path (S.isPath_cellType_unitor_fst k e)).trans_le one_le_two)).trans
      (I.nerveComposite_path _ hE _))
  have h₁ := (PastingDiagram.nerveComposite_boundary_one _ hd true (hb true)).symm.trans
    ((PastingDiagram.nerveComposite_congr e₁ (hb true)
      ((I.dim_path (S.isPath_cellType_unitor_snd k e)).trans_le one_le_two)).trans
      (I.nerveComposite_path _ hE' _))
  obtain ⟨ha₀, hb₀, hP₀, -, -⟩ := Bicategory.PathCell.mk.inj h₀
  obtain ⟨-, -, hQ₁, -, -⟩ := Bicategory.PathCell.mk.inj h₁
  exact PastingDiagram.pathCell_exists_eq_mk _ ha₀ hb₀ hP₀ hQ₁

end Layered.Signature.PathInterp

namespace Layered.Signature

variable {S' : Signature.{0}} {S : Signature.{v'}} (fp : S'.Pt → S.Pt) (fe : S'.Ed → S.Ed)
  (hsrc : ∀ e, S.edgeSource (fe e) = fp (S'.edgeSource e))
  (htgt : ∀ e, S.edgeTarget (fe e) = fp (S'.edgeTarget e)) [DecidableEq S'.Pt] [DecidableEq S.Pt]

variable {B : Type u} [Bicategory.{w, v} B]

include hsrc htgt in
theorem heq_unitorReading_of_isStructural {R : OGP.{0}}
    (J : S'.PathInterp (bicategoryNerve.{0, 0, 0} (FreeBicategory (EdgeQuiver R))))
    (F : Prefunctor (EdgeQuiver R) B) {hS : S.WellFormed} (FS : S.BicatInterp hS B)
    (hC : J.toGenPrefunctor ⋙q (lift F).toPrefunctor =
      genMap fp fe hsrc htgt ⋙q (lift FS.toPrefunctor).toPrefunctor)
    (k : UnitorKind) (ε : Edge S'.Pt S'.Ed) {x₁ y₁ : S'.Pt}
    (hs₁ : S'.walk x₁ (S'.cellType (.unitor k ε : Cell S'.Pt S'.Ed S'.Ce)).1 = some y₁)
    (ht₁ : S'.walk x₁ (S'.cellType (.unitor k ε : Cell S'.Pt S'.Ed S'.Ce)).2 = some y₁)
    {e : Edge S.Pt S.Ed} (he : mapEdge fp fe ε = e)
    (hs : S.walk (fp x₁) (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1 = some (fp y₁))
    (ht : S.walk (fp x₁) (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).2 = some (fp y₁))
    {U U' : (lift F).obj (J.toGenPrefunctor.obj x₁) ⟶ (lift F).obj (J.toGenPrefunctor.obj y₁)}
    {ψ : U ⟶ U'}
    (hψ : IsStructural F (pathComp (𝟭q _) (J.label.mapPath (S'.toPath _ hs₁)))
      (pathComp (𝟭q _) (J.label.mapPath (S'.toPath _ ht₁))) ψ) {C : Type _} {θ : C}
    (hθ : θ ≍ ψ) : θ ≍ FS.unitorReading k e hs ht := by
  subst he
  have e₁ {a b : S'.Pt} (T : Quiver.Path (V := S'.PathQuiver) a b) :
      pathComp (𝟭q _) (J.label.mapPath T) =
        (lift J.toGenPrefunctor).map (pathComp S'.freePrefunctor T) :=
    (pathComp_mapPath J.label T).trans (Bicategory.pathComp_comp_lift _ _ T)
  have h₁ := (hψ.congr (e₁ _) (e₁ _)).comp_lift
    (FreeBicategory.homOfNormalizeAuxEq (S'.nf_unitor k ε hs₁ ht₁))
  have hc := cellType_unitor_mapEdge (S := S) fp fe hsrc htgt k ε
  have eX (α : Bool) {l : List (Edge S'.Pt S'.Ed)} (hl : S'.walk x₁ l = some y₁)
      {l' : List (Edge S.Pt S.Ed)} (hl' : S.walk (fp x₁) l' = some (fp y₁))
      (he : l' = l.map (mapEdge fp fe)) :
      pathComp S.freePrefunctor (S.toPath l' hl') =
        (lift (genMap fp fe hsrc htgt)).map (pathComp S'.freePrefunctor (S'.toPath l hl)) := by
    subst he
    rw [eq_of_heq (toPath_map_heq fp fe hsrc htgt hl rfl rfl hl')]
    have h₃ : pathComp (pathMap fp fe hsrc htgt ⋙q S.freePrefunctor) (S'.toPath l hl) =
        pathComp (S'.freePrefunctor ⋙q (lift (genMap fp fe hsrc htgt)).toPrefunctor)
          (S'.toPath l hl) :=
      eq_of_heq (congr_arg_heq (fun G => pathComp G (S'.toPath l hl))
        (pathMap_comp_freePrefunctor fp fe hsrc htgt))
    exact (Bicategory.pathComp_mapPath_comp _ _ _).trans (h₃.trans
      (Bicategory.pathComp_comp_lift _ _ _))
  have h₂ := ((FS.isStructural_unitorReading k (mapEdge fp fe ε) hs ht).congr
    (eX false hs₁ hs (congrArg Prod.fst hc)) (eX true ht₁ ht (congrArg Prod.snd hc))).comp_lift
      (FreeBicategory.homOfNormalizeAuxEq (S'.nf_unitor k ε hs₁ ht₁))
  exact hθ.trans (h₁.heq_of_eq hC h₂)

end Layered.Signature

def Layered.Signature.edgePt {S : Layered.Signature.{v'}} (g : S.Ed) (b : Bool) : S.Pt :=
  cond b (S.edgeTarget g) (S.edgeSource g)

namespace Layered.Signature.PathInterp

section UnitorShapes

open PastingDiagram

variable {S : Signature.{v'}} {X : DiagSet.{u}} (K : S.PathInterp X)

noncomputable abbrev unitorSet (σ : Bool) (e : Edge S.Pt S.Ed) : LowerSet (K.ofEdge e).shape.ogp :=
  unitorSubset (K.ofEdge e) (by rw [K.dim_ofEdge]; exact Nat.one_pos) (K.isRound_ofEdge e) σ
    (Within.refl _)
    (isRewritableSubmolecule_image_refl (isRound_boundary_of_isRound (K.isRound_ofEdge e) _ σ))

noncomputable def edgeUnitorFactorization (σ : Bool) (e : Edge S.Pt S.Ed) :
    DegeneracyFactorization (K.edgeUnitor σ e) where
  target := (K.ofEdge e).shape.rdc
  proj := cylProj _ (K.unitorSet σ e)
  map := (K.ofEdge e).map
  surjective := surjective_cylProj _ _
  dim_lt := by
    have h : krullDim (K.ofEdge e).shape.rdc.obj.toOGP = ((1 : ℕ) : WithBot ℕ∞) :=
      (K.ofEdge e).shape.krullDim_eq_dimension.trans (congrArg _ (K.dim_ofEdge e))
    have h₂ : (K.edgeUnitor σ e).dim = 1 + 1 :=
      (dim_cylDiagram _ _ (unitorSubset_le_bdryFull _ _ _ _ _ _)).trans (by rw [K.dim_ofEdge])
    rw [h, h₂]
    exact_mod_cast (show 1 < 1 + 1 by omega)
  comp_eq := rfl

noncomputable def unitorDomain : UnitorKind → Edge S.Pt S.Ed → MoleculeShape
  | .left, e =>
    (K.edgeUnitor false e).shape.dual (OGP.topDim (K.edgeUnitor false e).shape.dimension)
  | .leftInverse, e => (K.edgeUnitor false e).shape
  | .right, e => (K.edgeUnitor true e).shape
  | .rightInverse, e =>
    (K.edgeUnitor true e).shape.dual (OGP.topDim (K.edgeUnitor true e).shape.dimension)

private theorem topDim_edgeUnitor (σ : Bool) (e : Edge S.Pt S.Ed)
    (x : (K.edgeUnitorFactorization σ e).target.obj.toOGP) :
    OGP.topDim (K.edgeUnitor σ e).shape.dimension (grade ℕ x) = false :=
  decide_eq_false ((K.edgeUnitorFactorization σ e).grade_lt x).ne

noncomputable def unitorMap : (k : UnitorKind) → (e : Edge S.Pt S.Ed) →
    (K.unitorDomain k e).rdc ⟶ (K.ofEdge e).shape.rdc
  | .left, e => MoleculeShape.dualLift (K.edgeUnitorFactorization false e).proj
      (K.topDim_edgeUnitor false e)
  | .leftInverse, e => (K.edgeUnitorFactorization false e).proj
  | .right, e => (K.edgeUnitorFactorization true e).proj
  | .rightInverse, e => MoleculeShape.dualLift (K.edgeUnitorFactorization true e).proj
      (K.topDim_edgeUnitor true e)

theorem equiv_unitorDiagram (k : UnitorKind) (e : Edge S.Pt S.Ed) :
    (K.unitorDiagram k e).Equiv
      ⟨K.unitorDomain k e, realize.map (K.unitorMap k e) ≫ (K.ofEdge e).map⟩ := by
  cases k
  · exact PastingDiagram.equiv_reverse_factorization _ _ (K.edgeUnitorFactorization false e)
      (K.topDim_edgeUnitor false e)
  · exact .refl _
  · exact .refl _
  · exact PastingDiagram.equiv_reverse_factorization _ _ (K.edgeUnitorFactorization true e)
      (K.topDim_edgeUnitor true e)

end UnitorShapes

variable {B : Type u} [Bicategory.{w, v} B] {S : Signature.{v'}} [DecidableEq S.Pt]
  (I : S.PathInterp (bicategoryNerve.{w, v, u} B))

noncomputable def freeEdge (g : S.Ed) :
    edgeSig.PathInterp (bicategoryNerve.{0, 0, 0} (FreeBicategory (EdgeQuiver (I.edge g).1.ogp))) :=
  freeEdgeInterp (I.dimension_edge g)
    (p := fun β => I.point (cond β (S.edgeTarget g) (S.edgeSource g))) fun β => by
      have h := (I.hasRoundType_edge g).equiv_boundary_cond dimension_atomPoint β
      cases β
      · exact h
      · exact h

omit [DecidableEq S.Pt] in
theorem toGenPrefunctor_freeEdge (g : S.Ed) :
    (I.freeEdge g).toGenPrefunctor ⋙q (lift (bicategoryNerveHomEquiv B
      (PastingDiagram.ofCell (I.edge g).2).shape.rdc
        (PastingDiagram.ofCell (I.edge g).2).map).1.toPrefunctor).toPrefunctor =
      genMap (edgePt g) (fun _ => g) (fun _ => rfl) (fun _ => rfl) ⋙q
        (lift I.toGenPrefunctor).toPrefunctor := by
  refine Prefunctor.hext (fun b => ?_) fun b b' d => ?_
  · refine (PastingDiagram.obj_ofCell _ _).trans ?_
    cases b
    · exact I.obj_vertex_edge g false
    · exact I.obj_vertex_edge g true
  · obtain ⟨⟨⟩, h⟩ := d
    obtain ⟨rfl, rfl⟩ := h
    have hF := congr_arg_heq (fun P : Prefunctor (EdgeQuiver (I.edge g).1.ogp) B =>
      P.map (I.edgeTop g)) (toPrefunctor_ofCell (I.edge g).2)
    dsimp only at hF
    have h₁ : (I.freeEdge g).toGenPrefunctor.map (⟨(), rfl, rfl⟩ : {e : Unit //
        edgeSig.edgeSource e = false ∧ edgeSig.edgeTarget e = true}) ≍
        (FreeBicategory.Hom.of (I.edgeTop g) : FreeBicategory.Hom _ _) := by
      dsimp only [toGenPrefunctor, mkPrefunctor]
      exact (Quiver.homOfEq_heq _ _ _).trans ((Quiver.homOfEq_heq _ _ _).trans
        (Labelling.free_map_heq _ _))
    have h₂ : (genMap (S' := edgeSig) (edgePt g) (fun _ => g) (fun _ => rfl)
        (fun _ => rfl)).map (⟨(), rfl, rfl⟩ : Quiver.Hom (V := edgeSig.GenQuiver) false true) ≍
        (FreeBicategory.Hom.of (B := S.GenQuiver) (⟨g, rfl, rfl⟩ : {e : S.Ed //
          S.edgeSource e = S.edgeSource g ∧ S.edgeTarget e = S.edgeTarget g}) :
          FreeBicategory.Hom _ _) := by
      dsimp only [genMap, mkPrefunctor]
      exact (Quiver.homOfEq_heq _ _ _).trans (Quiver.homOfEq_heq _ _ _)
    have h₃ : I.toGenPrefunctor.map (⟨g, rfl, rfl⟩ : {e : S.Ed //
        S.edgeSource e = S.edgeSource g ∧ S.edgeTarget e = S.edgeTarget g}) ≍
        (I.edge g).2.1.toPrefunctor.map (I.edgeTop g) := by
      dsimp only [toGenPrefunctor, mkPrefunctor]
      exact (Quiver.homOfEq_heq _ _ _).trans (Quiver.homOfEq_heq _ _ _)
    have h₄ : (lift I.toGenPrefunctor).map (FreeBicategory.Hom.of (B := S.GenQuiver)
        (⟨g, rfl, rfl⟩ : {e : S.Ed // S.edgeSource e = S.edgeSource g ∧
          S.edgeTarget e = S.edgeTarget g})) =
        I.toGenPrefunctor.map (⟨g, rfl, rfl⟩ : {e : S.Ed // S.edgeSource e = S.edgeSource g ∧
          S.edgeTarget e = S.edgeTarget g}) := rfl
    generalize (bicategoryNerveHomEquiv B (PastingDiagram.ofCell (I.edge g).2).shape.rdc
      (PastingDiagram.ofCell (I.edge g).2).map).1.toPrefunctor = Fp at hF ⊢
    exact (lift_map_heq Fp rfl rfl h₁).trans (hF.trans (h₃.symm.trans ((heq_of_eq h₄).symm.trans
      (lift_map_heq I.toGenPrefunctor rfl rfl h₂.symm))))

omit [DecidableEq S.Pt] in
theorem toGenPrefunctor_freePoint (z : S.Pt) :
    freePointInterp.toGenPrefunctor ⋙q (lift (bicategoryNerveHomEquiv B
      (PastingDiagram.ofCell (I.point z)).shape.rdc
        (PastingDiagram.ofCell (I.point z)).map).1.toPrefunctor).toPrefunctor =
      genMap (S' := pointSig) (fun _ => z) (fun e => Empty.elim e) (fun e => Empty.elim e)
        (fun e => Empty.elim e) ⋙q (lift I.toGenPrefunctor).toPrefunctor :=
  Prefunctor.hext (fun _ => (PastingDiagram.obj_ofCell (I.point z) _).trans
    ((I.point z).1.obj_eq_obj_vertex atomPoint.top).symm) fun _ _ d => Empty.elim d.1

omit [DecidableEq S.Pt] in
theorem toPrefunctor_unit_point (z : S.Pt) :
    (bicategoryNerveHomEquiv B (I.ofEdge (.unit z)).shape.rdc
        (I.ofEdge (.unit z)).map).1.toPrefunctor =
      (bicategoryNerveHomEquiv _ (freePointInterp.ofEdge (.unit ())).shape.rdc
        (freePointInterp.ofEdge (.unit ())).map).1.toPrefunctor ⋙q
        (lift (bicategoryNerveHomEquiv B (PastingDiagram.ofCell (I.point z)).shape.rdc
          (PastingDiagram.ofCell (I.point z)).map).1.toPrefunctor).toPrefunctor := by
  have hB : (bicategoryNerveHomEquiv B (PastingDiagram.ofCell (I.point z)).unit.shape.rdc
      (PastingDiagram.ofCell (I.point z)).unit.map).1 =
      (bicategoryNerveHomEquiv B (PastingDiagram.ofCell (I.point z)).shape.rdc
        (PastingDiagram.ofCell (I.point z)).map).1.comap
        (ConcreteCategory.hom (C := RDCpxDown) (cylProj (PastingDiagram.ofCell (I.point z)).shape
          ((PastingDiagram.ofCell (I.point z)).shape.ogp.bdryFull ⊤)).hom)
        (PastingDiagram.ofCell (I.point z)).unit.shape.rdc.obj.isRDC :=
    bicategoryNerveHomEquiv_comp B _ _
  have hF : (bicategoryNerveHomEquiv _
      (PastingDiagram.ofCell (freePointInterp.point ())).unit.shape.rdc
      (PastingDiagram.ofCell (freePointInterp.point ())).unit.map).1 =
      (bicategoryNerveHomEquiv _ (PastingDiagram.ofCell (freePointInterp.point ())).shape.rdc
        (PastingDiagram.ofCell (freePointInterp.point ())).map).1.comap
        (ConcreteCategory.hom (C := RDCpxDown) (cylProj
          (PastingDiagram.ofCell (I.point z)).shape
          ((PastingDiagram.ofCell (I.point z)).shape.ogp.bdryFull ⊤)).hom)
        (PastingDiagram.ofCell (I.point z)).unit.shape.rdc.obj.isRDC :=
    bicategoryNerveHomEquiv_comp _ _ _
  change (bicategoryNerveHomEquiv B (PastingDiagram.ofCell (I.point z)).unit.shape.rdc
      (PastingDiagram.ofCell (I.point z)).unit.map).1.toPrefunctor =
    (bicategoryNerveHomEquiv _ (PastingDiagram.ofCell (freePointInterp.point ())).unit.shape.rdc
      (PastingDiagram.ofCell (freePointInterp.point ())).unit.map).1.toPrefunctor ⋙q _
  rw [hB]
  have base : (bicategoryNerveHomEquiv B (PastingDiagram.ofCell (I.point z)).shape.rdc
      (PastingDiagram.ofCell (I.point z)).map).1.toPrefunctor =
      (bicategoryNerveHomEquiv _ (PastingDiagram.ofCell (freePointInterp.point ())).shape.rdc
        (PastingDiagram.ofCell (freePointInterp.point ())).map).1.toPrefunctor ⋙q
        (lift (bicategoryNerveHomEquiv B (PastingDiagram.ofCell (I.point z)).shape.rdc
          (PastingDiagram.ofCell (I.point z)).map).1.toPrefunctor).toPrefunctor := by
    rw [toPrefunctor_ofCell (freePointInterp.point ())]
    exact Eq.symm (Labelling.free_comp_lift _ _ (bicategoryNerveHomEquiv B
      (PastingDiagram.ofCell (I.point z)).shape.rdc
        (PastingDiagram.ofCell (I.point z)).map).1.obj_eq_of_boundary_Iic)
  rw [Labelling.comap_toPrefunctor_comp_lift _ _ _ base, ← hF]

end Layered.Signature.PathInterp
end Atoms.Diagrammatic
