import Atoms.Diagrammatic.Localization.Loc
import Atoms.Diagrammatic.Marked.Cylinder

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra
open Atoms.Homotopical Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe w w' u

namespace Atoms.Diagrammatic

private theorem injective_cylAtomIso_inv (U : Atom) : Function.Injective (cylAtomIso U).inv :=
  fun a b h => (Iso.inv_hom_id_apply (cylAtomIso U) a).symm.trans
    ((congrArg (cylAtomIso U).hom h).trans (Iso.inv_hom_id_apply (cylAtomIso U) b))

private theorem fst_eq_of_grayCylinderUnit_eq {P : DiagSet.{u}} {U T : Atom} {a : P.obj (op U)}
    (t : grayCylinder.obj U ⟶ T) {v : (grayCylinderFunctor.obj P).obj (op T)}
    (h : (grayCylinderUnit P).app (op U) a = (grayCylinderFunctor.obj P).map t.op v)
    (z : (grayCylinder.obj U).ogp.carrier) :
    ((cylAtomIso U).inv z).1 = ((grayCylinderSeparator P).app (op T) v (t z)).down := by
  have e : (grayFirstCoordinate P).app (op U) a =
      globeOneSeparator.map t.op ((grayCylinderSeparator P).app (op T) v) :=
    (grayCylinderSeparator_app_grayCylinderUnit_app P (op U) a).symm.trans
      ((congrArg ((grayCylinderSeparator P).app (op (grayCylinder.obj U))) h).trans
        (NatTrans.naturality_apply (grayCylinderSeparator P) t.op v))
  exact congrArg ULift.down (congrFun e z)

private theorem map_grayContraction_eq_of_grayCylinderUnit_eq {P : DiagSet.{u}} {U T : Atom}
    {a : P.obj (op U)} (t : grayCylinder.obj U ⟶ T) {v : (grayCylinderFunctor.obj P).obj (op T)}
    (h : (grayCylinderUnit P).app (op U) a = (grayCylinderFunctor.obj P).map t.op v) :
    P.map (grayContraction.app U).op a =
      P.map t.op ((grayCylinderContraction.app P).app (op T) v) :=
  (grayCylinderContraction_app_app_grayCylinderUnit_app P U a).symm.trans
    ((congrArg ((grayCylinderContraction.app P).app (op (grayCylinder.obj U))) h).trans
      (NatTrans.naturality_apply (grayCylinderContraction.app P) t.op v))

private theorem isDegenerate_of_isDegenerate_grayCylinderUnit {P : DiagSet.{u}} {U : Atom}
    {a : P.obj (op U)}
    (h : IsDegenerate (grayCylinderFunctor.obj P) ((grayCylinderUnit P).app (op U) a)) :
    IsDegenerate P a := by
  refine (isDegenerate_iff_not_isNondegenerate P a).2 fun ha => ?_
  obtain ⟨T, t, v, ht, hni, htv⟩ := h
  have hfst := fst_eq_of_grayCylinderUnit_eq t htv.symm
  obtain ⟨W, s, w, hs, hw, hsw⟩ := Homotopical.EZCategory.exists_isNondegenerate P (op T).unop
    ((grayCylinderContraction.app P).app (op T) v)
  have hcon : P.map (grayContraction.app U).op a = P.map (t ≫ s).op w :=
    (map_grayContraction_eq_of_grayCylinderUnit_eq t htv.symm).trans
      ((congrArg (P.map t.op) hsw.symm).trans (Functor.map_comp_apply P s.op t.op w).symm)
  have := isSplitEpi_of_isCollapseHom t ht
  obtain ⟨e, ⟨he, -⟩, -⟩ := Homotopical.EZCategory.existsUnique_iso_of_isNondegenerate P
    (grayContraction.app U) (t ≫ s) a w
    (isSplitEpi_of_isCollapseHom _ (isCollapseHom_grayContraction_app U)) ha inferInstance hw hcon
  have hc : ∀ z, ((cylAtomIso U).inv z).2 = e.inv (s (t z)) := fun z =>
    congrArg (fun f : grayCylinder.obj U ⟶ U => f z) ((Iso.eq_comp_inv e).2 he)
  refine hni (isIso_of_bijective t ⟨fun z z' hzz' => ?_, ht⟩)
  refine (injective_cylAtomIso_inv U) (Prod.ext ?_ ?_)
  · exact (hfst z).trans ((congrArg (fun y => ((grayCylinderSeparator P).app (op T) v y).down)
      hzz').trans (hfst z').symm)
  · exact (hc z).trans ((congrArg (fun y => e.inv (s y)) hzz').trans (hc z').symm)

private theorem grayEndpoint_comp_comp_grayContraction_inv {U U' : Atom}
    (g : grayCylinder.obj U ≅ grayCylinder.obj U')
    (hg : ∀ z, ((cylAtomIso U').inv (g.hom z)).1 = ((cylAtomIso U).inv z).1) :
    ((grayEndpoint false).app U ≫ g.hom ≫ grayContraction.app U') ≫
      ((grayEndpoint false).app U' ≫ g.inv ≫ grayContraction.app U) = 𝟙 U := by
  refine Atom.hom_ext fun u => ?_
  have hw : ((cylAtomIso U').inv (g.hom ((grayEndpoint false).app U u))).1 =
      SuspCarrier.pole false :=
    (hg _).trans (congrArg Prod.fst (symm_grayEndpoint_apply false U u))
  have hw' : (grayEndpoint false).app U' (grayContraction.app U'
      (g.hom ((grayEndpoint false).app U u))) =
        g.hom ((grayEndpoint false).app U u) := by
    change (cylAtomIso U').hom (SuspCarrier.pole false, ((cylAtomIso U').inv
      (g.hom ((grayEndpoint false).app U u))).2) = _
    rw [← hw]
    exact Iso.inv_hom_id_apply (cylAtomIso U') _
  change grayContraction.app U (g.inv ((grayEndpoint false).app U'
    (grayContraction.app U' (g.hom ((grayEndpoint false).app U u))))) = u
  rw [hw', Iso.hom_inv_id_apply]
  exact congrArg Prod.snd (symm_grayEndpoint_apply false U u)

private theorem exists_iso_of_grayCylinderUnit_eq {P : DiagSet.{u}} {U U' : Atom}
    (g : grayCylinder.obj U ≅ grayCylinder.obj U') {a : P.obj (op U)} {b : P.obj (op U')}
    (h : (grayCylinderUnit P).app (op U) a =
      (grayCylinderFunctor.obj P).map g.hom.op ((grayCylinderUnit P).app (op U') b)) :
    ∃ φ : U ≅ U', grayCylinder.map φ.hom = g.hom ∧ a = P.map φ.hom.op b := by
  have hsep : ∀ z, ((grayCylinderSeparator P).app (op (grayCylinder.obj U'))
      ((grayCylinderUnit P).app (op U') b) z).down = ((cylAtomIso U').inv z).1 := fun z =>
    congrArg ULift.down (congrFun (grayCylinderSeparator_app_grayCylinderUnit_app P (op U') b) z)
  have hg : ∀ z, ((cylAtomIso U').inv (g.hom z)).1 = ((cylAtomIso U).inv z).1 :=
    fun z => ((hsep _).symm.trans (fst_eq_of_grayCylinderUnit_eq g.hom h z).symm)
  have hg' : ∀ z, ((cylAtomIso U).inv (g.symm.hom z)).1 = ((cylAtomIso U').inv z).1 :=
    fun z => (hg (g.inv z)).symm.trans
      (congrArg (fun y => ((cylAtomIso U').inv y).1) (Iso.inv_hom_id_apply g z))
  let φ : U ≅ U' :=
    { hom := (grayEndpoint false).app U ≫ g.hom ≫ grayContraction.app U'
      inv := (grayEndpoint false).app U' ≫ g.inv ≫ grayContraction.app U
      hom_inv_id := grayEndpoint_comp_comp_grayContraction_inv g hg
      inv_hom_id := grayEndpoint_comp_comp_grayContraction_inv g.symm hg' }
  refine ⟨φ, congrArg Iso.hom (Atom.iso_eq (grayCylinder.mapIso φ) g), ?_⟩
  have hcon := map_grayContraction_eq_of_grayCylinderUnit_eq g.hom h
  rw [grayCylinderContraction_app_app_grayCylinderUnit_app, ← Functor.map_comp_apply] at hcon
  have he := congrArg (P.map ((grayEndpoint false).app U).op) hcon
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    grayEndpoint_grayContraction] at he
  exact (Functor.map_id_apply P _ a).symm.trans he

private theorem ιColimitType_eq_of_isColimit {J : Type u} [SmallCategory J] {G : J ⥤ Type u}
    {d : Cocone G} (hd : IsColimit d) {j j' : J} {x : G.obj j} {y : G.obj j'}
    (h : d.ι.app j x = d.ι.app j' y) : G.ιColimitType j x = G.ιColimitType j' y :=
  ((Types.isColimit_iff_coconeTypesIsColimit d).1 ⟨hd⟩).bijective.1 h

private theorem ιColimitType_eq_of_natTrans {J : Type u} [SmallCategory J] {G H : J ⥤ Type u}
    (φ : G ⟶ H) {j j' : J} {x : G.obj j} {y : G.obj j'}
    (h : G.ιColimitType j x = G.ιColimitType j' y) :
    H.ιColimitType j (φ.app j x) = H.ιColimitType j' (φ.app j' y) :=
  congrArg (G.descColimitType
    { pt := H.ColimitType
      ι j x := H.ιColimitType j (φ.app j x)
      ι_naturality f := funext fun x => by
        change H.ιColimitType _ (φ.app _ (G.map f x)) = _
        rw [NatTrans.naturality_apply, Functor.ιColimitType_map] }) h

private theorem isCollapseHom_grayCylinder_map {U W : Atom} (s : U ⟶ W) (hs : IsCollapseHom s) :
    IsCollapseHom (grayCylinder.map s) := fun z => by
  obtain ⟨x, hx⟩ := hs ((cylAtomIso W).inv z).2
  refine ⟨(cylAtomIso U).hom (((cylAtomIso W).inv z).1, x), (injective_cylAtomIso_inv W)
    ((symm_grayCylinder_map_apply s _).trans ?_)⟩
  exact (congrArg (fun w : (grayProduct (globe.{0} 1) U.ogp).carrier => (w.1, s w.2))
    (Iso.hom_inv_id_apply (cylAtomIso U) _)).trans (Prod.ext rfl hx)

private theorem not_isIso_grayCylinder_map {U W : Atom} (s : U ⟶ W) (hs : IsCollapseHom s)
    (hsi : ¬ IsIso s) : ¬ IsIso (grayCylinder.map s) := fun h => by
  have hd := Atom.dimension_eq_of_iso (asIso (grayCylinder.map s))
  rw [dimension_grayCylinder_obj, dimension_grayCylinder_obj] at hd
  exact hsi (isIso_of_isCollapseHom_of_dimension_eq s hs (by omega))

private def GrayMarked (P : DiagSet.{u}) (V : Atom) (v : (grayCylinderFunctor.obj P).obj (op V)) :
    Prop :=
  IsDegenerate _ v ∨ ∃ (U : Atom) (x : P.obj (op U)) (e : V ≅ grayCylinder.obj U),
    v = (grayCylinderFunctor.obj P).map e.hom.op ((grayCylinderUnit P).app (op U) x)

private theorem grayCylinderFunctor_map_app_map_grayCylinderUnit_app {P Q : DiagSet.{u}} (φ : P ⟶ Q)
    {V U : Atom} (e : V ⟶ grayCylinder.obj U) (x : P.obj (op U)) :
    (grayCylinderFunctor.map φ).app (op V)
        ((grayCylinderFunctor.obj P).map e.op ((grayCylinderUnit P).app (op U) x)) =
      (grayCylinderFunctor.obj Q).map e.op ((grayCylinderUnit Q).app (op U) (φ.app _ x)) :=
  (NatTrans.naturality_apply _ _ _).trans
    (congrArg _ (grayCylinderFunctor_map_app_grayCylinderUnit_app _ _ _))

private theorem grayMarked_map {P Q : DiagSet.{u}} (φ : P ⟶ Q) {V : Atom}
    {v : (grayCylinderFunctor.obj P).obj (op V)} (hv : GrayMarked P V v) :
    GrayMarked Q V ((grayCylinderFunctor.map φ).app (op V) v) := by
  rcases hv with h | ⟨U, x, e, rfl⟩
  · exact Or.inl (isDegenerate_app _ h)
  · exact Or.inr ⟨U, φ.app _ x, e,
      grayCylinderFunctor_map_app_map_grayCylinderUnit_app φ e.hom x⟩

variable {J : Type u} [SmallCategory J]

private noncomputable def grayMarkedFunctor (K : J ⥤ DiagSet.{u}) (V : Atom) : J ⥤ Type u where
  obj j := {v // GrayMarked (K.obj j) V v}
  map f := ↾fun v => ⟨(grayCylinderFunctor.map (K.map f)).app (op V) v.1, grayMarked_map _ v.2⟩
  map_id j := by
    ext v
    change (grayCylinderFunctor.map (K.map (𝟙 j))).app (op V) v.1 = v.1
    rw [K.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    ext v
    change (grayCylinderFunctor.map (K.map (f ≫ g))).app (op V) v.1 =
      (grayCylinderFunctor.map (K.map g)).app (op V) ((grayCylinderFunctor.map (K.map f)).app
        (op V) v.1)
    rw [K.map_comp, Functor.map_comp]
    rfl

private noncomputable def grayMarkedCoconeTypes {K : J ⥤ DiagSet.{u}} (c : Cocone K) (V : Atom) :
    (grayMarkedFunctor K V).CoconeTypes where
  pt := {v // GrayMarked c.pt V v}
  ι j v := ⟨(grayCylinderFunctor.map (c.ι.app j)).app (op V) v.1, grayMarked_map _ v.2⟩
  ι_naturality f := funext fun v => Subtype.ext
    ((ConcreteCategory.congr_hom (NatTrans.congr_app
      (grayCylinderFunctor.map_comp (K.map f) (c.ι.app _)) (op V)) v.1).symm.trans
      (congrArg (fun φ => (grayCylinderFunctor.map φ).app (op V) v.1) (c.w f)))

private noncomputable def unitGrayMarked (K : J ⥤ DiagSet.{u}) {V U : Atom}
    (e : V ≅ grayCylinder.obj U) :
    K ⋙ (evaluation _ (Type u)).obj (op U) ⟶ grayMarkedFunctor K V where
  app j := ↾fun x => ⟨(grayCylinderFunctor.obj (K.obj j)).map e.hom.op
    ((grayCylinderUnit (K.obj j)).app (op U) x), Or.inr ⟨U, x, e, rfl⟩⟩
  naturality j j' f := by
    ext x
    exact Subtype.ext
      (grayCylinderFunctor_map_app_map_grayCylinderUnit_app (K.map f) e.hom x).symm

private noncomputable def degGrayMarked (K : J ⥤ DiagSet.{u}) {V W : Atom} (q : V ⟶ W)
    (hq : IsCollapseHom q) (hqi : ¬ IsIso q) :
    (K ⋙ grayCylinderFunctor) ⋙ (evaluation _ (Type u)).obj (op W) ⟶ grayMarkedFunctor K V where
  app j := ↾fun w => ⟨(grayCylinderFunctor.obj (K.obj j)).map q.op w,
    Or.inl ⟨W, q, w, hq, hqi, rfl⟩⟩
  naturality j j' f := by
    ext w
    refine Subtype.ext ?_
    change (grayCylinderFunctor.obj (K.obj j')).map q.op
        ((grayCylinderFunctor.map (K.map f)).app (op W) w) =
      (grayCylinderFunctor.map (K.map f)).app (op V)
        ((grayCylinderFunctor.obj (K.obj j)).map q.op w)
    exact (NatTrans.naturality_apply _ _ _).symm

section Colimit

variable {K : J ⥤ DiagSet.{u}} {c : Cocone K} (hc : IsColimit c)
include hc

private noncomputable def isColimitEvaluation (U : Atom) :
    IsColimit (((evaluation _ (Type u)).obj (op U)).mapCocone c) :=
  isColimitOfPreserves _ hc

private noncomputable def isColimitGrayEvaluation (W : Atom) :
    IsColimit (((evaluation _ (Type u)).obj (op W)).mapCocone (grayCylinderFunctor.mapCocone c)) :=
  isColimitOfPreserves _ (isColimitOfPreserves grayCylinderFunctor hc)

private theorem ιColimitType_unitGrayMarked_eq {V U U' : Atom} (e : V ≅ grayCylinder.obj U)
    (e' : V ≅ grayCylinder.obj U') {j j' : J} (x : (K.obj j).obj (op U))
    (x' : (K.obj j').obj (op U'))
    (h : (grayCylinderFunctor.obj c.pt).map e.hom.op
        ((grayCylinderUnit c.pt).app (op U) ((c.ι.app j).app _ x)) =
      (grayCylinderFunctor.obj c.pt).map e'.hom.op
        ((grayCylinderUnit c.pt).app (op U') ((c.ι.app j').app _ x'))) :
    (grayMarkedFunctor K V).ιColimitType j ((unitGrayMarked K e).app j x) =
      (grayMarkedFunctor K V).ιColimitType j' ((unitGrayMarked K e').app j' x') := by
  have h' := congrArg ((grayCylinderFunctor.obj c.pt).map e.inv.op) h
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    e.inv_hom_id, op_id, Functor.map_id_apply] at h'
  obtain ⟨φ, hφ, hx⟩ := exists_iso_of_grayCylinderUnit_eq (e.symm ≪≫ e') h'
  have hx' : (c.ι.app j).app _ x = (c.ι.app j').app _ ((K.obj j').map φ.hom.op x') :=
    hx.trans (NatTrans.naturality_apply (c.ι.app j') φ.hom.op x').symm
  refine (ιColimitType_eq_of_natTrans (unitGrayMarked K e)
    (ιColimitType_eq_of_isColimit (isColimitEvaluation hc U) hx')).trans
      (congrArg _ (Subtype.ext ?_))
  change (grayCylinderFunctor.obj (K.obj j')).map e.hom.op
      ((grayCylinderUnit (K.obj j')).app (op U) ((K.obj j').map φ.hom.op x')) =
    (grayCylinderFunctor.obj (K.obj j')).map e'.hom.op
      ((grayCylinderUnit (K.obj j')).app (op U') x')
  rw [NatTrans.naturality_apply (grayCylinderUnit (K.obj j')) φ.hom.op x']
  change (grayCylinderFunctor.obj (K.obj j')).map e.hom.op
      ((grayCylinderFunctor.obj (K.obj j')).map (grayCylinder.map φ.hom).op _) = _
  rw [hφ, ← Functor.map_comp_apply, ← op_comp]
  congr 3
  rw [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

private theorem ιColimitType_eq_of_isDegenerate {V W₀ : Atom} {p : V ⟶ W₀} [IsSplitEpi p]
    (hpi : ¬ IsIso p) {z : (grayCylinderFunctor.obj c.pt).obj (op W₀)}
    (hz : Homotopical.EZCategory.IsNondegenerate _ z) {k : J}
    (z' : (grayCylinderFunctor.obj (K.obj k)).obj (op W₀))
    (hz' : (grayCylinderFunctor.map (c.ι.app k)).app _ z' = z) {j : J}
    (v : (grayMarkedFunctor K V).obj j) (hv : IsDegenerate _ v.1)
    (himg : (grayCylinderFunctor.map (c.ι.app j)).app _ v.1 =
      (grayCylinderFunctor.obj c.pt).map p.op z) :
    (grayMarkedFunctor K V).ιColimitType j v =
      (grayMarkedFunctor K V).ιColimitType k
        ((degGrayMarked K p (isCollapseHom_of_isSplitEpi p) hpi).app k z') := by
  obtain ⟨W, q, n, hq, hqi, hqn⟩ := hv
  change (grayCylinderFunctor.obj (K.obj j)).obj (op W) at n
  obtain ⟨W₁, r, z₁, hr, hz₁, hrz⟩ := Homotopical.EZCategory.exists_isNondegenerate
    (grayCylinderFunctor.obj c.pt) (op W).unop ((grayCylinderFunctor.map (c.ι.app j)).app (op W) n)
  have := isSplitEpi_of_isCollapseHom q hq
  have heq : (grayCylinderFunctor.obj c.pt).map p.op z =
      (grayCylinderFunctor.obj c.pt).map (q ≫ r).op z₁ :=
    himg.symm.trans ((congrArg _ hqn.symm).trans
      ((NatTrans.naturality_apply (grayCylinderFunctor.map (c.ι.app j)) q.op n).trans
      ((congrArg _ hrz.symm).trans
        (Functor.map_comp_apply (grayCylinderFunctor.obj c.pt) r.op q.op z₁).symm)))
  obtain ⟨e, ⟨he, hez⟩, -⟩ := Homotopical.EZCategory.existsUnique_iso_of_isNondegenerate _ p
    (q ≫ r) z z₁ inferInstance hz inferInstance hz₁ heq
  have hlift : (grayCylinderFunctor.map (c.ι.app j)).app (op W) n =
      (grayCylinderFunctor.map (c.ι.app k)).app (op W)
        ((grayCylinderFunctor.obj (K.obj k)).map (r ≫ e.inv).op z') := by
    have h : (r ≫ e.inv) ≫ e.hom = r := by rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    exact hrz.symm.trans (Eq.symm ((NatTrans.naturality_apply _ _ _).trans ((congrArg _ hz').trans
      ((congrArg _ hez.symm).trans ((Functor.map_comp_apply _ _ _ _).symm.trans
        (congrArg (fun t : W ⟶ W₁ => (grayCylinderFunctor.obj c.pt).map t.op z₁) h))))))
  refine (congrArg ((grayMarkedFunctor K V).ιColimitType j)
    (Subtype.ext hqn.symm : v = (degGrayMarked K q hq hqi).app j n)).trans
    ((ιColimitType_eq_of_natTrans (degGrayMarked K q hq hqi)
      (ιColimitType_eq_of_isColimit (isColimitGrayEvaluation hc W) hlift)).trans
        (congrArg _ (Subtype.ext ?_)))
  have h : q ≫ r ≫ e.inv = p := by
    rw [← Category.assoc, ← he, Category.assoc, e.hom_inv_id, Category.comp_id]
  exact (Functor.map_comp_apply _ _ _ _).symm.trans
    (congrArg (fun t : V ⟶ W₀ => (grayCylinderFunctor.obj (K.obj k)).map t.op z') h)

private theorem ιColimitType_eq_of_isDegenerate_image {V W₀ : Atom} {p : V ⟶ W₀} [IsSplitEpi p]
    (hpi : ¬ IsIso p) {z : (grayCylinderFunctor.obj c.pt).obj (op W₀)}
    (hz : Homotopical.EZCategory.IsNondegenerate _ z) {k : J}
    (z' : (grayCylinderFunctor.obj (K.obj k)).obj (op W₀))
    (hz' : (grayCylinderFunctor.map (c.ι.app k)).app _ z' = z) {j : J}
    (v : (grayMarkedFunctor K V).obj j)
    (himg : (grayCylinderFunctor.map (c.ι.app j)).app _ v.1 =
      (grayCylinderFunctor.obj c.pt).map p.op z) :
    (grayMarkedFunctor K V).ιColimitType j v =
      (grayMarkedFunctor K V).ιColimitType k
        ((degGrayMarked K p (isCollapseHom_of_isSplitEpi p) hpi).app k z') := by
  rcases v with ⟨v, hd | ⟨U, x, e, rfl⟩⟩
  · exact ιColimitType_eq_of_isDegenerate hc hpi hz z' hz' ⟨v, Or.inl hd⟩ hd himg
  · have hdeg : IsDegenerate (grayCylinderFunctor.obj c.pt) (U := grayCylinder.obj U)
        ((grayCylinderUnit c.pt).app (op U) ((c.ι.app j).app _ x)) := by
      have h1 : IsDegenerate _ ((grayCylinderFunctor.obj c.pt).map p.op z) :=
        ⟨_, p, z, isCollapseHom_of_isSplitEpi p, hpi, rfl⟩
      rw [← himg] at h1
      change IsDegenerate _ ((grayCylinderFunctor.map (c.ι.app j)).app _
        ((grayCylinderFunctor.obj (K.obj j)).map e.hom.op
          ((grayCylinderUnit (K.obj j)).app (op U) x))) at h1
      rw [grayCylinderFunctor_map_app_map_grayCylinderUnit_app] at h1
      exact (isDegenerate_map_iso_iff e _).1 h1
    obtain ⟨W, s, w, hs, hsi, hsw⟩ := isDegenerate_of_isDegenerate_grayCylinderUnit hdeg
    obtain ⟨k₂, w', hw'⟩ := Types.jointly_surjective_of_isColimit (isColimitEvaluation hc W) w
    have hx : (c.ι.app j).app _ x = (c.ι.app k₂).app _ ((K.obj k₂).map s.op w') :=
      hsw.symm.trans ((congrArg (c.pt.map s.op) hw'.symm).trans
        (NatTrans.naturality_apply (c.ι.app k₂) s.op w').symm)
    have hval : ((unitGrayMarked K e).app k₂ ((K.obj k₂).map s.op w')).1 =
        (grayCylinderFunctor.obj (K.obj k₂)).map (e.hom ≫ grayCylinder.map s).op
          ((grayCylinderUnit _).app (op W) w') := by
      change (grayCylinderFunctor.obj (K.obj k₂)).map e.hom.op
          ((grayCylinderUnit _).app (op U) ((K.obj k₂).map s.op w')) = _
      exact (congrArg ((grayCylinderFunctor.obj (K.obj k₂)).map e.hom.op)
        (NatTrans.naturality_apply (grayCylinderUnit (K.obj k₂)) s.op w')).trans
          (Functor.map_comp_apply _ _ _ _).symm
    have hdeg₂ : IsDegenerate _ ((unitGrayMarked K e).app k₂ ((K.obj k₂).map s.op w')).1 := by
      rw [hval]
      exact ⟨_, e.hom ≫ grayCylinder.map s, _, collapses.comp_mem _ _ (isCollapseHom_of_iso e)
        (isCollapseHom_grayCylinder_map s hs),
        fun h => not_isIso_grayCylinder_map s hs hsi (IsIso.of_isIso_comp_left e.hom _), rfl⟩
    refine (ιColimitType_eq_of_natTrans (unitGrayMarked K e)
      (ιColimitType_eq_of_isColimit (isColimitEvaluation hc U) hx)).trans
        (ιColimitType_eq_of_isDegenerate hc hpi hz z' hz' _ hdeg₂ (Eq.trans ?_ himg))
    change (grayCylinderFunctor.map (c.ι.app k₂)).app _ ((grayCylinderFunctor.obj
        (K.obj k₂)).map e.hom.op ((grayCylinderUnit (K.obj k₂)).app (op U)
          ((K.obj k₂).map s.op w'))) =
      (grayCylinderFunctor.map (c.ι.app j)).app _ ((grayCylinderFunctor.obj (K.obj j)).map
        e.hom.op ((grayCylinderUnit (K.obj j)).app (op U) x))
    rw [grayCylinderFunctor_map_app_map_grayCylinderUnit_app,
      grayCylinderFunctor_map_app_map_grayCylinderUnit_app, ← hx]
    rfl

private theorem isColimit_grayMarkedCoconeTypes (V : Atom) :
    (grayMarkedCoconeTypes c V).IsColimit := by
  refine ⟨⟨fun t t' htt' => ?_, fun ⟨δ, hδ⟩ => ?_⟩⟩
  · obtain ⟨j, v, rfl⟩ := (grayMarkedFunctor K V).ιColimitType_jointly_surjective t
    obtain ⟨j', v', rfl⟩ := (grayMarkedFunctor K V).ιColimitType_jointly_surjective t'
    have himg : (grayCylinderFunctor.map (c.ι.app j)).app (op V) v.1 =
        (grayCylinderFunctor.map (c.ι.app j')).app (op V) v'.1 := congrArg Subtype.val htt'
    by_cases hδ : IsDegenerate _ ((grayCylinderFunctor.map (c.ι.app j)).app (op V) v.1)
    · obtain ⟨W₀, p, z, hp, hz, hpz⟩ := Homotopical.EZCategory.exists_isNondegenerate _ (op V).unop
        ((grayCylinderFunctor.map (c.ι.app j)).app (op V) v.1)
      have hpi : ¬ IsIso p := fun h =>
        (isDegenerate_iff_not_isNondegenerate _ z).1
          ((isDegenerate_map_iso_iff (asIso p) z).1 (hpz ▸ hδ)) hz
      obtain ⟨k, z', hz'⟩ :=
        Types.jointly_surjective_of_isColimit (isColimitGrayEvaluation hc W₀) z
      exact (ιColimitType_eq_of_isDegenerate_image hc hpi hz z' hz' v hpz.symm).trans
        (ιColimitType_eq_of_isDegenerate_image hc hpi hz z' hz' v' (himg.symm.trans hpz.symm)).symm
    · rcases v with ⟨v, hd | ⟨U, x, e, rfl⟩⟩
      · exact absurd (isDegenerate_app _ hd) hδ
      rcases v' with ⟨v', hd' | ⟨U', x', e', rfl⟩⟩
      · exact absurd (himg ▸ isDegenerate_app _ hd') hδ
      · refine ιColimitType_unitGrayMarked_eq hc e e' x x' ?_
        have h := himg
        change (grayCylinderFunctor.map (c.ι.app j)).app _ ((grayCylinderFunctor.obj
            (K.obj j)).map e.hom.op ((grayCylinderUnit (K.obj j)).app (op U) x)) =
          (grayCylinderFunctor.map (c.ι.app j')).app _ ((grayCylinderFunctor.obj
            (K.obj j')).map e'.hom.op ((grayCylinderUnit (K.obj j')).app (op U') x')) at h
        rwa [grayCylinderFunctor_map_app_map_grayCylinderUnit_app,
          grayCylinderFunctor_map_app_map_grayCylinderUnit_app] at h
  · rcases hδ with ⟨W, q, w, hq, hqi, rfl⟩ | ⟨U, x, e, rfl⟩
    · obtain ⟨k, w', hw'⟩ :=
        Types.jointly_surjective_of_isColimit (isColimitGrayEvaluation hc W) w
      refine ⟨(grayMarkedFunctor K V).ιColimitType k ((degGrayMarked K q hq hqi).app k w'),
        Subtype.ext ?_⟩
      change (grayCylinderFunctor.map (c.ι.app k)).app _
        ((grayCylinderFunctor.obj (K.obj k)).map q.op w') = _
      rw [NatTrans.naturality_apply]
      exact congrArg _ hw'
    · obtain ⟨k, x', hx'⟩ := Types.jointly_surjective_of_isColimit (isColimitEvaluation hc U) x
      exact ⟨(grayMarkedFunctor K V).ιColimitType k ((unitGrayMarked K e).app k x'),
        Subtype.ext ((grayCylinderFunctor_map_app_map_grayCylinderUnit_app _ _ _).trans
          (congrArg (fun y => (grayCylinderFunctor.obj c.pt).map e.hom.op
            ((grayCylinderUnit c.pt).app (op U) y)) hx'))⟩

end Colimit

instance preservesMonomorphisms_flat :
    (MarkedPresheaf.flat.{u, 0} atomMarking).PreservesMonomorphisms where
  preserves f _ := (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono f))

instance preservesMonomorphisms_markedCylinder : markedCylinder.{u}.PreservesMonomorphisms :=
  markedExactCylinder.preservesMonomorphisms

private theorem mem_marked_iff_grayMarked (X : DiagSet.{u}) (V : Atom)
    (u : (markedCylinder.obj ((MarkedPresheaf.flat atomMarking).obj X)).underlying.obj (op V)) :
    u ∈ (markedCylinder.obj ((MarkedPresheaf.flat atomMarking).obj X)).marked V ↔
      GrayMarked X V ((markedCylinderForgetIso.hom.app
        ((MarkedPresheaf.flat atomMarking).obj X)).app (op V) u) :=
  (mem_marked_markedCylinder_obj_flat X V u).trans (or_congr ⟨fun h => isDegenerate_app _ h,
    fun h => Iso.hom_inv_id_app_apply (markedCylinderForgetIso.app _) _ u ▸
      isDegenerate_app (markedCylinderForgetIso.inv.app _) h⟩ Iff.rfl)

private noncomputable def markedCopyEquiv (X : DiagSet.{u}) (V : Atom)
    (hV : atomMarking.markable V) :
    (markedCylinder.obj ((MarkedPresheaf.flat atomMarking).obj X)).obj.obj
      (op (MarkedSite.marked V hV)) ≃ {v // GrayMarked X V v} :=
  Equiv.ofBijective (fun t => ⟨(markedCylinderForgetIso.hom.app
      ((MarkedPresheaf.flat atomMarking).obj X)).app (op V)
      ((markedCylinder.obj ((MarkedPresheaf.flat atomMarking).obj X)).obj.map
        (MarkedSite.toSelf _).op t), (mem_marked_iff_grayMarked X V _).1 ⟨hV, t, rfl⟩⟩)
    ⟨fun t t' h => (markedCylinder.obj
      ((MarkedPresheaf.flat atomMarking).obj X)).injective_map_toSelf _
        (Function.LeftInverse.injective (Iso.hom_inv_id_app_apply (markedCylinderForgetIso.app
          ((MarkedPresheaf.flat atomMarking).obj X)) (op V)) (congrArg Subtype.val h)),
      fun v => by
        have hm := (mem_marked_iff_grayMarked X V ((markedCylinderForgetIso.inv.app
          ((MarkedPresheaf.flat atomMarking).obj X)).app (op V) v.1)).2
            ((congrArg (GrayMarked X V) (Iso.inv_hom_id_app_apply (markedCylinderForgetIso.app
              ((MarkedPresheaf.flat atomMarking).obj X)) (op V) v.1)).mpr v.2)
        obtain ⟨hV', t, ht⟩ := hm
        exact ⟨t, Subtype.ext ((congrArg _ ht).trans (Iso.inv_hom_id_app_apply
          (markedCylinderForgetIso.app ((MarkedPresheaf.flat atomMarking).obj X)) (op V) v.1))⟩⟩

private theorem markedCopyEquiv_naturality {X Y : DiagSet.{u}} (φ : X ⟶ Y) (V : Atom)
    (hV : atomMarking.markable V)
    (t : (markedCylinder.obj ((MarkedPresheaf.flat atomMarking).obj X)).obj.obj
      (op (MarkedSite.marked V hV))) :
    (markedCopyEquiv Y V hV ((markedCylinder.map ((MarkedPresheaf.flat atomMarking).map φ)).hom.app
      _ t)).1 = (grayCylinderFunctor.map φ).app (op V) (markedCopyEquiv X V hV t).1 := by
  exact (congrArg ((markedCylinderForgetIso.hom.app
    ((MarkedPresheaf.flat atomMarking).obj Y)).app (op V))
      (MarkedPresheaf.forget_map_app_map_toSelf _ _ t).symm).trans
    (ConcreteCategory.congr_hom (NatTrans.congr_app
      (markedCylinderForgetIso.hom.naturality ((MarkedPresheaf.flat atomMarking).map φ)) (op V)) _)

instance preservesColimitsOfSize_flat :
    PreservesColimitsOfSize.{w, w'} (MarkedPresheaf.flat.{u, 0} atomMarking) :=
  (MarkedPresheaf.flatForgetAdjunction atomMarking).leftAdjoint_preservesColimits

private noncomputable def isColimitMarkedCopy {K : J ⥤ DiagSet.{u}} {c : Cocone K}
    (hc : IsColimit c) (V : Atom) (hV : atomMarking.markable V) :
    IsColimit (((evaluation _ (Type u)).obj (op (MarkedSite.marked V hV))).mapCocone
      ((ObjectProperty.ι _).mapCocone
        ((MarkedPresheaf.flat atomMarking ⋙ markedCylinder).mapCocone c))) := by
  set d := ((evaluation _ (Type u)).obj (op (MarkedSite.marked V hV))).mapCocone
      ((ObjectProperty.ι _).mapCocone
        ((MarkedPresheaf.flat atomMarking ⋙ markedCylinder).mapCocone c)) with hd
  have hcomm : ∀ (j : J) (t : (markedCylinder.obj ((MarkedPresheaf.flat atomMarking).obj
      (K.obj j))).obj.obj (op (MarkedSite.marked V hV))),
      markedCopyEquiv c.pt V hV (d.ι.app j t) =
        (grayMarkedCoconeTypes c V).ι j (markedCopyEquiv (K.obj j) V hV t) := fun j t =>
    Subtype.ext (markedCopyEquiv_naturality (c.ι.app j) V hV t)
  let ψ : grayMarkedFunctor K V ⟶ (K ⋙ MarkedPresheaf.flat atomMarking ⋙ markedCylinder) ⋙
      ObjectProperty.ι _ ⋙ (evaluation _ (Type u)).obj (op (MarkedSite.marked V hV)) :=
    { app j := ↾(markedCopyEquiv (K.obj j) V hV).symm
      naturality j j' f := by
        ext v
        refine (markedCopyEquiv (K.obj j') V hV).injective
          (((markedCopyEquiv (K.obj j') V hV).apply_symm_apply _).trans (Subtype.ext ?_))
        exact (congrArg _ (congrArg Subtype.val
          ((markedCopyEquiv (K.obj j) V hV).apply_symm_apply v)).symm).trans
            (markedCopyEquiv_naturality (K.map f) V hV _).symm }
  refine ((Types.isColimit_iff_coconeTypesIsColimit d).2 ⟨⟨fun t t' htt' => ?_, fun s => ?_⟩⟩).some
  · obtain ⟨j, x, rfl⟩ := Functor.ιColimitType_jointly_surjective _ t
    obtain ⟨j', x', rfl⟩ := Functor.ιColimitType_jointly_surjective _ t'
    have h := (isColimit_grayMarkedCoconeTypes hc V).bijective.1
      (a₁ := (grayMarkedFunctor K V).ιColimitType j (markedCopyEquiv (K.obj j) V hV x))
      (a₂ := (grayMarkedFunctor K V).ιColimitType j' (markedCopyEquiv (K.obj j') V hV x'))
      (((hcomm j x).symm.trans (congrArg _ htt')).trans (hcomm j' x'))
    exact (congrArg _ ((markedCopyEquiv (K.obj j) V hV).symm_apply_apply x).symm).trans
      ((ιColimitType_eq_of_natTrans ψ h).trans
        (congrArg _ ((markedCopyEquiv (K.obj j') V hV).symm_apply_apply x')))
  · obtain ⟨t, ht⟩ := (isColimit_grayMarkedCoconeTypes hc V).bijective.2
      (markedCopyEquiv c.pt V hV s)
    obtain ⟨j, y, rfl⟩ := Functor.ιColimitType_jointly_surjective _ t
    refine ⟨Functor.ιColimitType _ j ((markedCopyEquiv (K.obj j) V hV).symm y),
      (markedCopyEquiv c.pt V hV).injective ?_⟩
    exact (hcomm j _).trans ((congrArg _ ((markedCopyEquiv (K.obj j) V hV).apply_symm_apply
      y)).trans ht)

instance preservesColimitsOfSize_reversibleCylinder :
    PreservesColimitsOfSize.{u, u}
      (MarkedPresheaf.flat.{u, 0} atomMarking ⋙ markedCylinder ⋙ Loc) where
  preservesColimitsOfShape := ⟨⟨fun hc => nonempty_isColimit_Loc_mapCocone
    (isColimitOfPreserves (MarkedPresheaf.flat atomMarking ⋙ markedCylinder) hc)
    (fun V hV => isColimitMarkedCopy hc V hV)⟩⟩

noncomputable def reversibleCylinder : ExactCylinder.{u} DiagSet.{u} where
  I := MarkedPresheaf.flat atomMarking ⋙ markedCylinder ⋙ Loc
  endpoint ε := flatCompLocIso.inv ≫ Functor.whiskerLeft (MarkedPresheaf.flat atomMarking)
    (Functor.whiskerRight (markedExactCylinder.endpoint ε) Loc)
  contraction := Functor.whiskerLeft (MarkedPresheaf.flat atomMarking)
    (Functor.whiskerRight markedExactCylinder.contraction Loc) ≫ flatCompLocIso.hom
  endpoint_contraction ε := NatTrans.ext (funext fun X => by
    have h : Loc.map ((markedExactCylinder.endpoint ε).app
        ((MarkedPresheaf.flat atomMarking).obj X)) ≫ Loc.map (markedExactCylinder.contraction.app
          ((MarkedPresheaf.flat atomMarking).obj X)) = 𝟙 _ := by
      rw [← Functor.map_comp, markedExactCylinder.endpoint_app_contraction_app]
      exact Loc.map_id _
    change flatCompLocIso.inv.app X ≫ Loc.map ((markedExactCylinder.endpoint ε).app
        ((MarkedPresheaf.flat atomMarking).obj X)) ≫ Loc.map (markedExactCylinder.contraction.app
          ((MarkedPresheaf.flat atomMarking).obj X)) ≫ flatCompLocIso.hom.app X = 𝟙 X
    rw [reassoc_of% h, Iso.inv_hom_id_app]
    rfl)
  mono_endpoints X := by
    have h : coprod.desc ((flatCompLocIso.inv ≫ Functor.whiskerLeft
        (MarkedPresheaf.flat atomMarking)
          (Functor.whiskerRight (markedExactCylinder.endpoint false) Loc)).app X)
        ((flatCompLocIso.inv ≫ Functor.whiskerLeft (MarkedPresheaf.flat atomMarking)
          (Functor.whiskerRight (markedExactCylinder.endpoint true) Loc)).app X) =
        coprod.map (flatCompLocIso.inv.app X) (flatCompLocIso.inv.app X) ≫
          (coprodComparison Loc ((MarkedPresheaf.flat atomMarking).obj X)
            ((MarkedPresheaf.flat atomMarking).obj X)) ≫
            Loc.map (markedExactCylinder.endpoints _) := by
      have hl : coprod.inl ≫ coprodComparison Loc ((MarkedPresheaf.flat atomMarking).obj X)
          ((MarkedPresheaf.flat atomMarking).obj X) ≫ Loc.map (markedExactCylinder.endpoints _) =
          Loc.map ((markedExactCylinder.endpoint false).app
            ((MarkedPresheaf.flat atomMarking).obj X)) := by
        rw [coprodComparison_inl_assoc, ← Functor.map_comp, ExactCylinder.inl_endpoints]
      have hr : coprod.inr ≫ coprodComparison Loc ((MarkedPresheaf.flat atomMarking).obj X)
          ((MarkedPresheaf.flat atomMarking).obj X) ≫ Loc.map (markedExactCylinder.endpoints _) =
          Loc.map ((markedExactCylinder.endpoint true).app
            ((MarkedPresheaf.flat atomMarking).obj X)) := by
        rw [coprodComparison_inr_assoc, ← Functor.map_comp, ExactCylinder.inr_endpoints]
      ext1
      · rw [coprod.inl_desc, coprod.inl_map_assoc]
        exact (congrArg (flatCompLocIso.inv.app X ≫ ·) hl).symm
      · rw [coprod.inr_desc, coprod.inr_map_assoc]
        exact (congrArg (flatCompLocIso.inv.app X ≫ ·) hr).symm
    have hm : Mono (coprod.map (flatCompLocIso.inv.app X) (flatCompLocIso.inv.app X) ≫
        coprodComparison Loc ((MarkedPresheaf.flat atomMarking).obj X)
          ((MarkedPresheaf.flat atomMarking).obj X) ≫
            Loc.map (markedExactCylinder.endpoints _)) := inferInstance
    exact (congrArg Mono h).mpr hm

end Atoms.Diagrammatic
