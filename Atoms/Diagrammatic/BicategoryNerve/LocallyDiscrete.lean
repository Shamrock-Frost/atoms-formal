import Atoms.Diagrammatic.BicategoryNerve.Equivalence
import Atoms.Diagrammatic.OneTruncation

open CategoryTheory Opposite Order Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape
open Atoms.Diagrammatic.PastingDiagram
open CategoryTheory.Bicategory (PathCell pathComp pathComp_cons)
open scoped CategoryTheory.Bicategory

universe w u

namespace Atoms.Diagrammatic

variable {C : Type u} [Category.{u} C]

namespace LocallyDiscreteNerve

structure Reading (B : Type u) [Bicategory.{w, u} B] (C : Type u) [Category.{u} C] where
  obj : B → C
  map {a b : B} : (a ⟶ b) → (obj a ⟶ obj b)
  map_id (a : B) : map (𝟙 a) = 𝟙 (obj a)
  map_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) = map f ≫ map g

variable {B : Type u} [Bicategory.{w, u} B] (R : Reading B C)

theorem Reading.map_pathComp_comp {a b c : B} (P : Quiver.Path a b) (Q : Quiver.Path b c) :
    R.map (pathComp (𝟭q B) (P.comp Q)) =
      R.map (pathComp (𝟭q B) P) ≫ R.map (pathComp (𝟭q B) Q) := by
  induction Q with
  | nil => exact (Category.comp_id _).symm.trans (congrArg _ (R.map_id _).symm)
  | cons Q e ih =>
    rw [Quiver.Path.comp_cons, pathComp_cons, pathComp_cons, R.map_comp, R.map_comp, ih,
      Category.assoc]

def Reading.toPrefunctor : B ⥤q C where
  obj := R.obj
  map := R.map

theorem Reading.map_pathComp {V : Type*} [Quiver V] (P : V ⥤q B) {x y : V}
    (p : Quiver.Path x y) :
    R.map (pathComp P p) = composePath ((P ⋙q R.toPrefunctor).mapPath p) := by
  induction p with
  | nil => exact R.map_id _
  | cons p e ih => exact (R.map_comp _ _).trans (congrArg (· ≫ R.map (P.map e)) ih)

def obj (x : (bicategoryNerve.{w, u, u} B).Vertex) : C :=
  R.obj (x.1.toPrefunctor.obj atomPoint.top)

theorem nerveComposite_ofCell_point (x : (bicategoryNerve.{w, u, u} B).Vertex)
    (hd : (ofCell x).dim ≤ 2) :
    (ofCell x).nerveComposite hd = ⟨x.1.toPrefunctor.obj atomPoint.top,
      x.1.toPrefunctor.obj atomPoint.top, .nil, .nil, 𝟙 _⟩ := by
  have hd₀ : (ofCell x).dim = 0 := dimension_atomPoint
  have hM : IsMoleculeIn (ofCell x).shape.rdc.obj.toOGP ⊤ := (ofCell x).shape.isMolecule
  obtain ⟨b, hb⟩ := exists_nerveComposite_eq_of_dim_eq_zero (ofCell x) hd hd₀
  have e := congrArg PathCell.src (hb.symm.trans (nerveComposite_of_dim_le_one (ofCell x)
    (hd₀.trans_le zero_le_one) _ (boundary_zero_eq_Iic_vertex _ hM false)
    (boundary_zero_eq_Iic_vertex _ hM true)))
  obtain rfl : b = x.1.toPrefunctor.obj atomPoint.top :=
    e.trans ((obj_ofCell x _).trans (congrArg _ (Subsingleton.elim (α := atomPoint.ogp)
      (h := atomPoint.toMoleculeShape.subsingleton_of_dimension_eq_zero dimension_atomPoint) _ _)))
  exact hb

variable {d : PastingDiagram (bicategoryNerve.{w, u, u} B)}
  {x y : (bicategoryNerve.{w, u, u} B).Vertex}

theorem dim_le_two (h : HasBdry false 0 d (ofCell x) (ofCell y)) : d.dim ≤ 2 :=
  h.dim_h.trans_le one_le_two

theorem exists_path (h : HasBdry false 0 d (ofCell x) (ofCell y)) :
    ∃ P : Quiver.Path (x.1.toPrefunctor.obj atomPoint.top) (y.1.toPrefunctor.obj atomPoint.top),
      d.nerveComposite (dim_le_two h) = ⟨_, _, P, P, 𝟙 _⟩ :=
  exists_nerveComposite_eq_of_hasBdry h _ (h.dim_a.trans_le (Nat.zero_le 2))
    (h.dim_b.trans_le (Nat.zero_le 2)) (nerveComposite_ofCell_point x _)
    (nerveComposite_ofCell_point y _)

noncomputable def compositeHom (h : HasBdry false 0 d (ofCell x) (ofCell y)) :
    obj R x ⟶ obj R y :=
  R.map (pathComp (𝟭q B) (exists_path h).choose)

theorem compositeHom_eq (h : HasBdry false 0 d (ofCell x) (ofCell y))
    {P Q : Quiver.Path (x.1.toPrefunctor.obj atomPoint.top) (y.1.toPrefunctor.obj atomPoint.top)}
    {φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q}
    (hP : d.nerveComposite (dim_le_two h) = ⟨_, _, P, Q, φ⟩) :
    compositeHom R h = R.map (pathComp (𝟭q B) P) := by
  obtain ⟨-, -, hdom, -, -⟩ := PathCell.mk.inj ((exists_path h).choose_spec.symm.trans hP)
  exact congrArg (fun P => R.map (pathComp (𝟭q B) P)) (eq_of_heq hdom)

theorem arrowMk_compositeHom (h : HasBdry false 0 d (ofCell x) (ofCell y))
    {c : PathCell B} (hc : d.nerveComposite (dim_le_two h) = c) :
    Arrow.mk (compositeHom R h) = Arrow.mk (R.map (pathComp (𝟭q B) c.dom)) := by
  subst hc
  rw [compositeHom]
  generalize (exists_path h).choose = P, (exists_path h).choose_spec = hP
  rw [hP]
  rfl

noncomputable def interpretation :
    OneTruncation.Interpretation (bicategoryNerve.{w, u, u} B) C where
  obj := obj R
  map e := compositeHom R (hasBdry_ofCell_edge e)

theorem freeLift_map_eq {f : OneTruncation.point x ⟶ OneTruncation.point y}
    (hf : IsComposite d f) (h : HasBdry false 0 d (ofCell x) (ofCell y)) :
    (interpretation R).freeLift.map f = compositeHom R h := by
  induction hf with
  | edge e => exact OneTruncation.Interpretation.freeLift_map_edge _ e
  | @paste a b hp x y z f g hf hg ihf ihg =>
    obtain ⟨P, hP⟩ := exists_path hf.hasBdry
    obtain ⟨Q, hQ⟩ := exists_path hg.hasBdry
    have hw := nerveComposite_pasteAlong_zero a b hp.1.iso hp.1.map_comm _ _ (dim_le_two h) hP hQ
    rw [Functor.map_comp, ihf hf.hasBdry, ihg hg.hasBdry, compositeHom_eq R _ hP,
      compositeHom_eq R _ hQ, compositeHom_eq R h hw]
    exact (R.map_pathComp_comp P Q).symm
  | equiv he hf ih =>
    obtain ⟨P, hP⟩ := exists_path hf.hasBdry
    rw [ih hf.hasBdry, compositeHom_eq R _ hP,
      compositeHom_eq R h ((nerveComposite_congr he _ _).symm.trans hP)]

theorem map_id (x : (bicategoryNerve.{w, u, u} B).Vertex) :
    (interpretation R).map (DiagSet.Edge.id x) = 𝟙 (obj R x) := by
  have hb := hasBdry_ofCell_edge (DiagSet.Edge.id x)
  have hd : (ofCell x).unit.dim ≤ 2 :=
    (dim_eq_of_equiv (equiv_ofCell_edge_id_unit x)).symm.trans_le (dim_le_two hb)
  have h := (nerveComposite_congr (equiv_ofCell_edge_id_unit x) (dim_le_two hb) hd).trans
    (nerveComposite_unit_ofCell_point x hd)
  exact (compositeHom_eq R hb h).trans ((R.map_comp _ _).trans
    ((congrArg₂ (· ≫ ·) (R.map_id _) (R.map_id _)).trans (Category.id_comp _)))

theorem arrowMk_freeLift_map_boundary {V : Atom} (hV : V.dimension = 2)
    (c : diagram (bicategoryNerve.{w, u, u} B) V) {D : PathCell B}
    (hD : (ofCell c).nerveComposite hV.le = D)
    {f g : OneTruncation.point x ⟶ OneTruncation.point y}
    (hf : IsComposite ((ofCell c).boundary 1 false) f)
    (hg : IsComposite ((ofCell c).boundary 1 true) g) :
    Arrow.mk ((interpretation R).freeLift.map f) = Arrow.mk (R.map (pathComp (𝟭q B) D.dom)) ∧
      Arrow.mk ((interpretation R).freeLift.map g) =
        Arrow.mk (R.map (pathComp (𝟭q B) D.cod)) := by
  have hd : (ofCell c).dim ≤ 2 := hV.le
  have h₁ := nerveComposite_boundary_one (ofCell c) hd false (dim_le_two hf.hasBdry)
  have h₂ := nerveComposite_boundary_one (ofCell c) hd true (dim_le_two hg.hasBdry)
  rw [hD] at h₁ h₂
  have e₁ := arrowMk_compositeHom R hf.hasBdry h₁
  have e₂ := arrowMk_compositeHom R hg.hasBdry h₂
  exact ⟨(congrArg Arrow.mk (freeLift_map_eq R hf hf.hasBdry)).trans e₁,
    (congrArg Arrow.mk (freeLift_map_eq R hg hg.hasBdry)).trans e₂⟩

theorem arrowMk_map_eq_of_val_eq {U : Atom} (ℓ : Labelling B U.ogp U.isRDC)
    {v w v' w' : EdgeQuiver U.ogp} (a : v ⟶ w) (a' : v' ⟶ w') (h : a.1 = a'.1) :
    Arrow.mk (R.map (ℓ.toPrefunctor.map a)) = Arrow.mk (R.map (ℓ.toPrefunctor.map a')) := by
  obtain ⟨a, ha, hv, hw⟩ := a
  obtain ⟨a', ha', hv', hw'⟩ := a'
  obtain rfl : a = a' := h
  obtain rfl : v = v' := LowerSet.Iic_injective (α := U.ogp) (hv.symm.trans hv')
  obtain rfl : w = w' := LowerSet.Iic_injective (α := U.ogp) (hw.symm.trans hw')
  rfl

theorem arrowMk_map_map_eq {U V : Atom} (g : V ⟶ U) (ℓ : diagram (bicategoryNerve.{w, u, u} B) U)
    {s t : EdgeQuiver V.ogp} (e : s ⟶ t) {v w : EdgeQuiver U.ogp} (a : v ⟶ w)
    (h : g e.1 = a.1) :
    Arrow.mk (R.map (((bicategoryNerve.{w, u, u} B).map g.op ℓ :
      diagram (bicategoryNerve.{w, u, u} B) V).1.toPrefunctor.map e)) =
      Arrow.mk (R.map (ℓ.1.toPrefunctor.map a)) := by
  have he : grade ℕ (ConcreteCategory.hom (C := RDCpxDown) g.hom.hom e.1) = 1 :=
    (congrArg (grade ℕ) h).trans a.2.1
  refine Eq.trans ?_ (arrowMk_map_eq_of_val_eq R ℓ.1
    ((ConcreteCategory.hom (C := RDCpxDown) g.hom.hom).mapEdge e he) a h)
  simp only [bicategoryNerve_map, Labelling.comap, Prefunctor.comp_map]
  rw [Map.freePrefunctor_map_of_grade_eq _ e he]
  rfl

theorem arrowMk_compositeHom_edge (e : (bicategoryNerve.{w, u, u} B).Edge x y)
    {s t : EdgeQuiver (atomGlobe 1).ogp} (a : s ⟶ t) (ha : a.1 = (atomGlobe 1).top) :
    Arrow.mk (compositeHom R (hasBdry_ofCell_edge e)) =
      Arrow.mk (R.map (e.cell.1.toPrefunctor.map a)) := by
  obtain ⟨a, hg, hs, ht⟩ := a
  obtain rfl : a = (atomGlobe 1).top := ha
  have hk : krullDim (LowerSet.Iic (atomGlobe 1).top) ≤ 1 := by
    rw [LowerSet.krullDim_Iic, hg]
    rfl
  have hd : (ofCell e.cell).dim ≤ 2 := dim_le_two (hasBdry_ofCell_edge e)
  have h := (nerveComposite_ofCell e.cell hd hs ht (isLayerOrder_nil hk)).trans
    (Labelling.pathCell_of_krullDim_le_one _ ((atomGlobe 1).isRDC _) _ hs ht hk)
  rw [pathOf_Iic_of_grade_eq_one hg ((atomGlobe 1).isRDC _) hk hs ht] at h
  refine (arrowMk_compositeHom R (hasBdry_ofCell_edge e) h).trans ?_
  exact congrArg Arrow.mk ((R.map_comp _ _).trans
    ((congrArg (· ≫ _) (R.map_id _)).trans (Category.id_comp _)))

def reading (C : Type u) [Category.{u} C] : Reading (LocallyDiscrete C) C where
  obj a := a.as
  map f := f.as
  map_id _ := rfl
  map_comp _ _ := rfl

theorem respects : (interpretation (reading C)).Respects where
  unit := map_id (reading C)
  boundary hV c _ _ _ _ hf hg := by
    obtain ⟨e₁, e₂⟩ := arrowMk_freeLift_map_boundary (reading C) hV c rfl hf hg
    generalize (ofCell c).nerveComposite hV.le = D at e₁ e₂
    obtain ⟨s, t, p, q, φ⟩ := D
    exact Arrow.mk_injective _ _ (e₁.trans ((congrArg (fun m => Arrow.mk (Discrete.as m))
      (LocallyDiscrete.eq_of_hom φ)).trans e₂.symm))

end LocallyDiscreteNerve

noncomputable def oneTruncationBicategoryNerveLocallyDiscrete (C : Cat.{u, u}) :
    OneTruncation (bicategoryNerve.{u, u, u} (LocallyDiscrete C)) ⥤ C :=
  (LocallyDiscreteNerve.interpretation (LocallyDiscreteNerve.reading C)).lift
    LocallyDiscreteNerve.respects

theorem IsComposite.map_oneTruncationBicategoryNerveLocallyDiscrete {C : Cat.{u, u}}
    {d : PastingDiagram (bicategoryNerve.{u, u, u} (LocallyDiscrete C))}
    {x y : (bicategoryNerve.{u, u, u} (LocallyDiscrete C)).Vertex}
    {f : OneTruncation.point x ⟶ OneTruncation.point y} (hf : IsComposite d f) (hd : d.dim ≤ 2)
    {P Q : Quiver.Path (x.1.toPrefunctor.obj atomPoint.top) (y.1.toPrefunctor.obj atomPoint.top)}
    {φ : pathComp (𝟭q (LocallyDiscrete C)) P ⟶ pathComp (𝟭q (LocallyDiscrete C)) Q}
    (hP : d.nerveComposite hd = ⟨_, _, P, Q, φ⟩) :
    (oneTruncationBicategoryNerveLocallyDiscrete C).map ((OneTruncation.quotientFunctor _).map f) =
      (pathComp (𝟭q (LocallyDiscrete C)) P).as :=
  (OneTruncation.Interpretation.lift_map_quotientFunctor_map _ _ f).trans
    ((LocallyDiscreteNerve.freeLift_map_eq _ hf hf.hasBdry).trans
      (LocallyDiscreteNerve.compositeHom_eq _ _ hP))

noncomputable def bicategoryNerveLocallyDiscreteToCategoricalNerve (C : Cat.{u, u}) :
    bicategoryNerve.{u, u, u} (LocallyDiscrete C) ⟶ categoricalNerve.obj C :=
  oneTruncationAdjunction.homEquiv _ C
    (Cat.Hom.ofFunctor (oneTruncationBicategoryNerveLocallyDiscrete C))

theorem arrowMk_bicategoryNerveLocallyDiscreteToCategoricalNerve_app_map (C : Cat.{u, u})
    {U : Atom} (ℓ : diagram (bicategoryNerve.{u, u, u} (LocallyDiscrete C)) U)
    {x y : (ball.{u} U).Vertex} (e : (ball.{u} U).Edge x y) {v w : EdgeQuiver U.ogp} (a : v ⟶ w)
    (ha : ULift.down (α := atomGlobe 1 ⟶ U) e.cell (atomGlobe 1).top = a.1) :
    Arrow.mk (((bicategoryNerveLocallyDiscreteToCategoricalNerve C).app (op U) ℓ :
      OneTruncation (ball.{u} U) ⥤ C).map (OneTruncation.globeHomMk e)) =
      Arrow.mk (ℓ.1.toPrefunctor.map a).as := by
  have hg : grade ℕ (atomGlobe 1).top = 1 :=
    (atomGlobe 1).dimension_eq.symm.trans (dimension_atomGlobe 1)
  have h₁ : ((bicategoryNerveLocallyDiscreteToCategoricalNerve C).app (op U) ℓ :
      OneTruncation (ball.{u} U) ⥤ C).map (OneTruncation.globeHomMk e) =
      LocallyDiscreteNerve.compositeHom (LocallyDiscreteNerve.reading C)
        (hasBdry_ofCell_edge (e.map (uliftYonedaEquiv.symm ℓ))) :=
    (congrArg (oneTruncationBicategoryNerveLocallyDiscrete C).map
      (oneTruncation_map_map_globeHomMk (uliftYonedaEquiv.symm ℓ) e)).trans
      (OneTruncation.Interpretation.lift_map_globeHomMk _ _ _)
  refine (congrArg Arrow.mk h₁).trans ((LocallyDiscreteNerve.arrowMk_compositeHom_edge _ _
    (⟨(atomGlobe 1).top, hg, boundary_zero_eq_Iic_vertex _ ((atomGlobe 1).isRDC _) false,
      boundary_zero_eq_Iic_vertex _ ((atomGlobe 1).isRDC _) true⟩ :
        Quiver.Hom (V := EdgeQuiver (atomGlobe 1).ogp) _ _) rfl).trans ?_)
  exact LocallyDiscreteNerve.arrowMk_map_map_eq (LocallyDiscreteNerve.reading C) e.cell.down ℓ _ a
    ha

namespace LocallyDiscreteNerve

theorem heq_of_arrowMk_eq {a b a' b' : LocallyDiscrete C} {f : a ⟶ b} {f' : a' ⟶ b'}
    (ha : a = a') (hb : b = b') (h : Arrow.mk f.as = Arrow.mk f'.as) : f ≍ f' := by
  subst ha hb
  exact heq_of_eq (Discrete.ext (Arrow.mk_injective _ _ h))

end LocallyDiscreteNerve

theorem injective_bicategoryNerveLocallyDiscreteToCategoricalNerve_app (C : Cat.{u, u})
    (U : Atom) :
    Function.Injective ((bicategoryNerveLocallyDiscreteToCategoricalNerve C).app (op U)) := by
  intro ℓ ℓ' h
  have hobj (v : U.ogp) (hv : grade ℕ v = 0) :
      ℓ.1.toPrefunctor.obj v = ℓ'.1.toPrefunctor.obj v := by
    obtain ⟨x, rfl⟩ := exists_point_apply_top hv
    exact LocallyDiscrete.ext (congrArg (fun F : OneTruncation (ball.{u} U) ⥤ C =>
      F.obj (OneTruncation.mk (ULift.up x : (ball.{u} U).Vertex))) h)
  have hobj' (x : U.ogp) : ℓ.1.toPrefunctor.obj x = ℓ'.1.toPrefunctor.obj x :=
    (ℓ.1.obj_eq_obj_vertex x).trans ((hobj _ (grade_eq_zero_of_boundary_zero_eq_Iic
      (boundary_zero_eq_Iic_vertex _ (U.isRDC x) false))).trans (ℓ'.1.obj_eq_obj_vertex x).symm)
  refine Subtype.ext (Labelling.ext_of_locallyDiscrete (Prefunctor.hext hobj' fun v w a => ?_))
  obtain ⟨g, hg⟩ := exists_arrow_apply_top a.2.1
  let e : (ball.{u} U).Edge _ _ := ⟨ULift.up g, rfl, rfl⟩
  exact LocallyDiscreteNerve.heq_of_arrowMk_eq (hobj' v) (hobj' w)
    ((arrowMk_bicategoryNerveLocallyDiscreteToCategoricalNerve_app_map C ℓ e a hg).symm.trans
      ((congrArg (fun F : OneTruncation (ball.{u} U) ⥤ C =>
        Arrow.mk (F.map (OneTruncation.globeHomMk e))) h).trans
        (arrowMk_bicategoryNerveLocallyDiscreteToCategoricalNerve_app_map C ℓ' e a hg)))

namespace LocallyDiscreteNerve

theorem apply_atomGlobeVertex {U : Atom} (g : atomGlobe 1 ⟶ U) (α : Bool) {v : U.ogp}
    (hv : U.ogp.boundary (.Iic (g (atomGlobe 1).top)) 0 α = .Iic v) :
    g (atomGlobeVertex α atomPoint.top) = v :=
  LowerSet.Iic_injective (((ConcreteCategory.hom (C := RDCpxDown) g.hom.hom).boundary_Iic_apply
    (boundary_atomGlobe_one α)).symm.trans hv)

theorem vertex_ext {U : Atom} {p q : (ball.{u} U).Vertex}
    (h : ULift.down (α := atomPoint ⟶ U) p atomPoint.top =
      ULift.down (α := atomPoint ⟶ U) q atomPoint.top) : p = q :=
  ULift.ext _ _ (Atom.hom_ext fun z => by rwa [Subsingleton.elim z atomPoint.top])

noncomputable def pointAt (U : Atom) (x : U.ogp) : (ball.{u} U).Vertex :=
  ULift.up (exists_point_apply_top (grade_eq_zero_of_boundary_zero_eq_Iic
    (boundary_zero_eq_Iic_vertex _ (U.isRDC x) false))).choose

theorem pointAt_apply_top {U : Atom} {x v : U.ogp}
    (hv : U.ogp.boundary (.Iic x) 0 false = .Iic v) :
    ULift.down (α := atomPoint ⟶ U) (pointAt U x) atomPoint.top = v :=
  (exists_point_apply_top (grade_eq_zero_of_boundary_zero_eq_Iic
    (boundary_zero_eq_Iic_vertex _ (U.isRDC x) false))).choose_spec.trans
    (vertex_eq_of_boundary_zero_eq_Iic _ (U.isRDC x) hv)

theorem eq_pointAt {U : Atom} (p : (ball.{u} U).Vertex) {v : U.ogp} (hv : grade ℕ v = 0)
    (h : ULift.down (α := atomPoint ⟶ U) p atomPoint.top = v) : p = pointAt U v :=
  vertex_ext (h.trans (pointAt_apply_top.{u}
    (boundary_Iic_of_isMin (grade_eq_zero_iff.1 hv) 0 false)).symm)

theorem pointAt_eq_of_boundary {U : Atom} {x v : U.ogp}
    (hv : U.ogp.boundary (.Iic x) 0 false = .Iic v) : pointAt.{u} U x = pointAt U v :=
  eq_pointAt _ (grade_eq_zero_of_boundary_zero_eq_Iic hv) (pointAt_apply_top hv)

noncomputable def edgeAt {U : Atom} {v w : EdgeQuiver U.ogp} (a : v ⟶ w) :
    (ball.{u} U).Edge (pointAt U v) (pointAt U w) where
  cell := ULift.up (exists_arrow_apply_top a.2.1).choose
  src_eq := eq_pointAt _ (grade_eq_zero_of_boundary_zero_eq_Iic a.2.2.1)
    (apply_atomGlobeVertex _ false
      (((exists_arrow_apply_top a.2.1).choose_spec ▸ a.2.2.1 :)))
  tgt_eq := eq_pointAt _ (grade_eq_zero_of_boundary_zero_eq_Iic a.2.2.2)
    (apply_atomGlobeVertex _ true
      (((exists_arrow_apply_top a.2.1).choose_spec ▸ a.2.2.2 :)))

theorem arrow_hom_ext {U : Atom} {g g' : atomGlobe 1 ⟶ U}
    (h : g (atomGlobe 1).top = g' (atomGlobe 1).top) : g = g' := by
  refine Atom.hom_ext fun z => ?_
  by_cases hz : z = (atomGlobe 1).top
  · rw [hz, h]
  have hpos : 0 < (atomGlobe 1).dimension := (dimension_atomGlobe 1).symm ▸ one_pos
  have hfull := ((atomGlobe 1).mem_bdryFull_top_iff z).2 hz
  rw [bdryFull, LowerSet.mem_sup_iff, (atomGlobe 1).bdry_top_eq_boundary hpos,
    (atomGlobe 1).bdry_top_eq_boundary hpos, dimension_atomGlobe, ← Atom.Iic_top,
    boundary_atomGlobe_one, boundary_atomGlobe_one, LowerSet.mem_Iic_iff,
    LowerSet.mem_Iic_iff] at hfull
  obtain ⟨α, rfl⟩ : ∃ α, z = atomGlobeVertex α atomPoint.top := by
    rcases hfull with hle | hle
    exacts [⟨false, hle.antisymm (grade_eq_zero_iff.1 (grade_eq_zero_of_boundary_zero_eq_Iic
      (boundary_atomGlobe_one false)) hle)⟩, ⟨true, hle.antisymm (grade_eq_zero_iff.1
      (grade_eq_zero_of_boundary_zero_eq_Iic (boundary_atomGlobe_one true)) hle)⟩]
  exact (apply_atomGlobeVertex g α (boundary_zero_eq_Iic_vertex _ (U.isRDC _) α)).trans
    (apply_atomGlobeVertex g' α (h ▸ boundary_zero_eq_Iic_vertex _ (U.isRDC _) α)).symm

structure LocallyCodiscrete (C : Type u) where
  as : C

instance : CategoryStruct.{u} (LocallyCodiscrete C) where
  Hom a b := a.as ⟶ b.as
  id a := 𝟙 a.as
  comp {a b c} f g := (f : a.as ⟶ b.as) ≫ (g : b.as ⟶ c.as)

instance (a b : LocallyCodiscrete C) : Category.{u} (a ⟶ b) where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

instance : Bicategory.{u, u} (LocallyCodiscrete C) where
  whiskerLeft _ _ _ _ := PUnit.unit
  whiskerRight _ _ := PUnit.unit
  associator _ _ _ := ⟨PUnit.unit, PUnit.unit, rfl, rfl⟩
  leftUnitor _ := ⟨PUnit.unit, PUnit.unit, rfl, rfl⟩
  rightUnitor _ := ⟨PUnit.unit, PUnit.unit, rfl, rfl⟩

def codiscreteReading (C : Type u) [Category.{u} C] : Reading (LocallyCodiscrete C) C where
  obj a := a.as
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def labels {U : Atom} (F : OneTruncation (ball.{u} U) ⥤ C) :
    EdgeQuiver U.ogp ⥤q C where
  obj x := F.obj (OneTruncation.mk (pointAt U x))
  map a := F.map (OneTruncation.globeHomMk (edgeAt a))

section Labels

variable {B : Type u} [Bicategory.{u, u} B] (R : Reading B C) {U : Atom}
  (F : OneTruncation (ball.{u} U) ⥤ C) (s : diagram (bicategoryNerve.{u, u, u} B) U)
  (hs : s.1.toPrefunctor ⋙q R.toPrefunctor = labels F)

include hs

theorem arrowMk_freeLift_map_edgeAt {v w : EdgeQuiver U.ogp} (a : v ⟶ w) :
    Arrow.mk ((interpretation R).freeLift.map ((OneTruncation.freeMap
      (uliftYonedaEquiv.symm s)).map (OneTruncation.edge (edgeAt a)))) =
      Arrow.mk (F.map (OneTruncation.globeHomMk (edgeAt a))) := by
  have hg : grade ℕ (atomGlobe 1).top = 1 :=
    (atomGlobe 1).dimension_eq.symm.trans (dimension_atomGlobe 1)
  refine (congrArg Arrow.mk ((congrArg (interpretation R).freeLift.map
    (OneTruncation.freeMap_edge _ _)).trans
      (OneTruncation.Interpretation.freeLift_map_edge _ _))).trans ?_
  let a₀ : Quiver.Hom (V := EdgeQuiver (atomGlobe 1).ogp) _ _ :=
    ⟨(atomGlobe 1).top, hg, boundary_zero_eq_Iic_vertex _ ((atomGlobe 1).isRDC _) false,
      boundary_zero_eq_Iic_vertex _ ((atomGlobe 1).isRDC _) true⟩
  refine (arrowMk_compositeHom_edge R _ a₀ rfl).trans ?_
  refine (arrowMk_map_map_eq R (edgeAt.{u} a).cell.down s a₀ a
    (exists_arrow_apply_top a.2.1).choose_spec).trans ?_
  exact congrArg (fun P : EdgeQuiver U.ogp ⥤q C => Arrow.mk (P.map a)) hs

theorem arrowMk_freeLift_map_id (q : (ball.{u} U).Vertex) :
    Arrow.mk ((interpretation R).freeLift.map ((OneTruncation.freeMap
      (uliftYonedaEquiv.symm s)).map (OneTruncation.edge (DiagSet.Edge.id q)))) =
      Arrow.mk (F.map (OneTruncation.globeHomMk (DiagSet.Edge.id q))) := by
  have hq : grade ℕ (ULift.down (α := atomPoint ⟶ U) q atomPoint.top) = 0 :=
    Nat.le_zero.1 (((Atom.isMap _).grade_le _).trans
      ((atomPoint.grade_le_dimension _).trans_eq dimension_atomPoint))
  refine (congrArg Arrow.mk ((congrArg (interpretation R).freeLift.map
    (OneTruncation.freeMap_edge _ _)).trans
      (OneTruncation.Interpretation.freeLift_map_edge _ _))).trans ?_
  rw [DiagSet.Edge.map_id, map_id R, OneTruncation.globeHomMk_id, F.map_id]
  exact congrArg (fun a => Arrow.mk (𝟙 a))
    ((congrArg (fun P : EdgeQuiver U.ogp ⥤q C => P.obj _) hs).trans
      (congrArg (fun p => F.obj (OneTruncation.mk p)) (eq_pointAt q hq rfl).symm))

theorem freeMap_comp_freeLift :
    OneTruncation.freeMap (uliftYonedaEquiv.symm s) ⋙ (interpretation R).freeLift =
      OneTruncation.quotientFunctor _ ⋙ F := by
  refine OneTruncation.Free.functor_ext fun x y e => ?_
  have key {x' y' : (ball.{u} U).Vertex} (e' : (ball.{u} U).Edge x' y') (hc : e.cell = e'.cell)
      (h : Arrow.mk ((interpretation R).freeLift.map ((OneTruncation.freeMap
        (uliftYonedaEquiv.symm s)).map (OneTruncation.edge e'))) =
        Arrow.mk (F.map (OneTruncation.globeHomMk e'))) :
      Arrow.mk ((OneTruncation.freeMap (uliftYonedaEquiv.symm s) ⋙
        (interpretation R).freeLift).map (OneTruncation.edge e)) =
        Arrow.mk ((OneTruncation.quotientFunctor _ ⋙ F).map (OneTruncation.edge e)) :=
    (congrArg (Functor.mapArrow _).obj (OneTruncation.arrowMk_edge_eq e e' hc)).trans (h.trans
      (congrArg (Functor.mapArrow (OneTruncation.quotientFunctor _ ⋙ F)).obj
        (OneTruncation.arrowMk_edge_eq e e' hc)).symm)
  by_cases h1 : grade ℕ (ULift.down (α := atomGlobe 1 ⟶ U) e.cell (atomGlobe 1).top) = 1
  · let a : Quiver.Hom (V := EdgeQuiver U.ogp) _ _ :=
      ⟨_, h1, boundary_zero_eq_Iic_vertex _ (U.isRDC _) false,
        boundary_zero_eq_Iic_vertex _ (U.isRDC _) true⟩
    exact key (edgeAt a) (ULift.ext _ _ (arrow_hom_ext
      (exists_arrow_apply_top a.2.1).choose_spec.symm)) (arrowMk_freeLift_map_edgeAt R F s hs a)
  · have h0 : grade ℕ (ULift.down (α := atomGlobe 1 ⟶ U) e.cell (atomGlobe 1).top) = 0 := by
      have h := ((Atom.isMap (ULift.down (α := atomGlobe 1 ⟶ U) e.cell)).grade_le
        (atomGlobe 1).top).trans_eq ((atomGlobe 1).dimension_eq.symm.trans (dimension_atomGlobe 1))
      omega
    obtain ⟨p, hp⟩ := exists_point_apply_top h0
    exact key (DiagSet.Edge.id (ULift.up p : (ball.{u} U).Vertex)) (ULift.ext _ _ (arrow_hom_ext
      (hp.symm.trans (congrArg p (Subsingleton.elim _ _))))) (arrowMk_freeLift_map_id R F s hs _)

end Labels

variable {U : Atom} (F : OneTruncation (ball.{u} U) ⥤ C)

noncomputable def codiscreteCell : diagram (bicategoryNerve.{u, u, u} (LocallyCodiscrete C)) U :=
  ⟨{ toPrefunctor := { obj x := ⟨(labels F).obj x⟩, map a := (labels F).map a }
     obj_eq_of_boundary_Iic _ _ hv := congrArg (fun p => LocallyCodiscrete.mk
       (F.obj (OneTruncation.mk p))) (pointAt_eq_of_boundary hv)
     cell _ _ _ _ _ _ := PUnit.unit }, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩

theorem composePath_labels_boundaryPath {V : Atom} (hV : V.dimension = 2) (ι : V ⟶ U)
    (hι : IsInclusionHom ι) {y : U.ogp} (hy : ι V.top = y) {s t : U.ogp}
    (hs : U.ogp.boundary (.Iic y) 0 false = .Iic s)
    (ht : U.ogp.boundary (.Iic y) 0 true = .Iic t) :
    composePath ((labels F).mapPath (boundaryPath U.ogp U.isRDC y false hs ht)) =
      composePath ((labels F).mapPath (boundaryPath U.ogp U.isRDC y true hs ht)) := by
  subst hy
  have hs' := boundary_zero_eq_Iic_vertex _ (V.isRDC V.top) false
  have ht' := boundary_zero_eq_Iic_vertex _ (V.isRDC V.top) true
  obtain rfl : ι (vertex _ (V.isRDC V.top) false) = s := LowerSet.Iic_injective
    (((ConcreteCategory.hom (C := RDCpxDown) ι.hom.hom).boundary_Iic_apply hs').symm.trans hs)
  obtain rfl : ι (vertex _ (V.isRDC V.top) true) = t := LowerSet.Iic_injective
    (((ConcreteCategory.hom (C := RDCpxDown) ι.hom.hom).boundary_Iic_apply ht').symm.trans ht)
  let c : diagram (ball.{u} U) V := ULift.up ι
  obtain ⟨x, x', f, g, hf, hg, hfg⟩ := OneTruncation.exists_boundary_relation hV c
  have hL := freeMap_comp_freeLift (codiscreteReading C) F (codiscreteCell F) rfl
  have hm (α : Bool) : ((ofCell c).boundary 1 α).mapTo (uliftYonedaEquiv.symm (codiscreteCell F)) =
      (ofCell ((uliftYonedaEquiv.symm (codiscreteCell F)).app _ c)).boundary 1 α := by
    rw [PastingDiagram.ofCell_app, boundary_mapTo]
  obtain ⟨xs, hxs⟩ := exists_isLayerOrder_of_krullDim_le (V.isRDC V.top) (by
    rw [LowerSet.krullDim_Iic, ← V.dimension_eq, hV]
    rfl)
  obtain ⟨e₁, e₂⟩ := arrowMk_freeLift_map_boundary (codiscreteReading C) hV _
    (nerveComposite_ofCell ((uliftYonedaEquiv.symm (codiscreteCell F)).app _ c) hV.le hs' ht' hxs)
    (hm false ▸ hf.map _) (hm true ▸ hg.map _)
  have e := Arrow.mk_injective _ _ (e₁.symm.trans ((congrArg (fun G : OneTruncation.Free _ ⥤ C =>
    Arrow.mk (G.map f)) hL).trans ((congrArg (fun m => Arrow.mk (F.map m)) hfg).trans
    ((congrArg (fun G : OneTruncation.Free _ ⥤ C => Arrow.mk (G.map g)) hL).symm.trans e₂))))
  have key (α : Bool) : (codiscreteReading C).map (pathComp (𝟭q _)
      (((uliftYonedaEquiv.symm (codiscreteCell F)).app _ c).1.toPrefunctor.mapPath
        (boundaryPath V.ogp V.isRDC V.top α hs' ht'))) =
      composePath ((labels F).mapPath (boundaryPath U.ogp U.isRDC (ι V.top) α hs ht)) :=
    (congrArg (fun p => (codiscreteReading C).map (pathComp (𝟭q _) p))
      ((Map.mapPath_freePrefunctor_comp_lift_of_forall
        (ConcreteCategory.hom (C := RDCpxDown) ι.hom.hom) (codiscreteCell F).1.toPrefunctor _
        fun e he => (grade_eq_of_isInclusionHom ι hι e).trans (grade_of_mem_pathEdges _ he)).trans
      (congrArg (codiscreteCell F).1.toPrefunctor.mapPath
        (Map.mapPath_pathOf_boundary _ V.isRDC U.isRDC V.top α _ _)))).trans
      ((congrArg (codiscreteReading C).map
        (Bicategory.pathComp_mapPath (codiscreteCell F).1.toPrefunctor _)).trans
        ((codiscreteReading C).map_pathComp (codiscreteCell F).1.toPrefunctor _))
  exact (key false).symm.trans (e.trans (key true))

noncomputable def discreteLabels : EdgeQuiver U.ogp ⥤q LocallyDiscrete C where
  obj x := ⟨(labels F).obj x⟩
  map a := ⟨(labels F).map a⟩

noncomputable def discreteCell : diagram (bicategoryNerve.{u, u, u} (LocallyDiscrete C)) U :=
  ⟨{ toPrefunctor := discreteLabels F
     obj_eq_of_boundary_Iic _ _ hv := congrArg (fun p => LocallyDiscrete.mk
       (F.obj (OneTruncation.mk p))) (pointAt_eq_of_boundary hv)
     cell y hy _ _ hs ht := eqToHom (Discrete.ext
       (((reading C).map_pathComp (discreteLabels F) _).trans
         ((composePath_labels_boundaryPath F ((Atom.dimension_ofClosure U y).trans hy)
           (Atom.closureIncl U y) (Atom.isInclusionHom_closureIncl U y)
           (Atom.closureIncl_top U y) hs ht).trans
           ((reading C).map_pathComp (discreteLabels F) _).symm))) },
    Labelling.isCommutative_of_locallyDiscrete _⟩

end LocallyDiscreteNerve

theorem bicategoryNerveLocallyDiscreteToCategoricalNerve_app_discreteCell (C : Cat.{u, u})
    {U : Atom} (F : OneTruncation (ball.{u} U) ⥤ C) :
    (bicategoryNerveLocallyDiscreteToCategoricalNerve C).app (op U)
      (LocallyDiscreteNerve.discreteCell F) = F :=
  CategoryTheory.Quotient.lift_unique' _ _ _
    ((congrArg (· ⋙ oneTruncationBicategoryNerveLocallyDiscrete C)
      (quotientFunctor_comp_oneTruncation_map _)).trans
      ((congrArg (OneTruncation.freeMap _ ⋙ ·)
        (OneTruncation.Interpretation.quotientFunctor_comp_lift _
          LocallyDiscreteNerve.respects)).trans
        (LocallyDiscreteNerve.freeMap_comp_freeLift (LocallyDiscreteNerve.reading C) F
          (LocallyDiscreteNerve.discreteCell F) rfl)))

instance isIso_bicategoryNerveLocallyDiscreteToCategoricalNerve (C : Cat.{u, u}) :
    IsIso (bicategoryNerveLocallyDiscreteToCategoricalNerve C) :=
  haveI (U : Atomᵒᵖ) : IsIso ((bicategoryNerveLocallyDiscreteToCategoricalNerve C).app U) :=
    (CategoryTheory.isIso_iff_bijective _).2
      ⟨injective_bicategoryNerveLocallyDiscreteToCategoricalNerve_app C U.unop,
        fun F => ⟨LocallyDiscreteNerve.discreteCell F,
          bicategoryNerveLocallyDiscreteToCategoricalNerve_app_discreteCell C F⟩⟩
  NatIso.isIso_of_isIso_app _

noncomputable def bicategoryNerveLocallyDiscreteIso (C : Cat.{u, u}) :
    bicategoryNerve.{u, u, u} (LocallyDiscrete C) ≅ categoricalNerve.obj C :=
  asIso (bicategoryNerveLocallyDiscreteToCategoricalNerve C)

theorem bicategoryNerveLocallyDiscreteIso_hom_app_obj (C : Cat.{u, u}) {U : Atom}
    (ℓ : diagram (bicategoryNerve.{u, u, u} (LocallyDiscrete C)) U) (x : (ball.{u} U).Vertex) :
    ((bicategoryNerveLocallyDiscreteIso C).hom.app (op U) ℓ :
      OneTruncation (ball.{u} U) ⥤ C).obj (OneTruncation.mk x) =
      (ℓ.1.toPrefunctor.obj (ULift.down (α := atomPoint ⟶ U) x atomPoint.top)).as :=
  rfl

theorem bicategoryNerveLocallyDiscreteIso_hom_app_map (C : Cat.{u, u}) {U : Atom}
    (ℓ : diagram (bicategoryNerve.{u, u, u} (LocallyDiscrete C)) U) {x y : (ball.{u} U).Vertex}
    (e : (ball.{u} U).Edge x y) {v w : EdgeQuiver U.ogp} (a : v ⟶ w)
    (ha : ULift.down (α := atomGlobe 1 ⟶ U) e.cell (atomGlobe 1).top = a.1) :
    Arrow.mk (((bicategoryNerveLocallyDiscreteIso C).hom.app (op U) ℓ :
      OneTruncation (ball.{u} U) ⥤ C).map (OneTruncation.globeHomMk e)) =
      Arrow.mk (ℓ.1.toPrefunctor.map a).as :=
  arrowMk_bicategoryNerveLocallyDiscreteToCategoricalNerve_app_map C ℓ e a ha

end Atoms.Diagrammatic
