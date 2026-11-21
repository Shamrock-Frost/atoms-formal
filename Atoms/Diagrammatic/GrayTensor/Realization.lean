import Atoms.Diagrammatic.GrayTensor.Cells
import Atoms.Diagrammatic.Joyal.FaceNerve

open CategoryTheory Limits Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape
open scoped MonoidalCategory.ExternalProduct

universe u

namespace Atoms.Diagrammatic

def grayProductRDCMap {P P' Q Q' : RDCpx.{0}} (f : P ⟶ P') (g : Q ⟶ Q') :
    grayProductRDC P Q ⟶ grayProductRDC P' Q' :=
  letI : (ConcreteCategory.hom f.hom).isMap.monotone.functor.IsFibered := f.property
  letI : (ConcreteCategory.hom g.hom).isMap.monotone.functor.IsFibered := g.property
  let hm := isMap_prodMap P.obj.isRDC P'.obj.isRDC Q.obj.isRDC Q'.obj.isRDC
    (ConcreteCategory.hom f.hom).isMap (ConcreteCategory.hom g.hom).isMap
  ⟨ConcreteCategory.ofHom (X := (grayProductRDC P Q).obj) (Y := (grayProductRDC P' Q').obj)
    ⟨_, hm⟩, functor_isFibered_prodMap _ _ hm.monotone⟩

@[simp] theorem grayProductRDCMap_apply {P P' Q Q' : RDCpx.{0}} (f : P ⟶ P') (g : Q ⟶ Q')
    (p : (grayProductRDC P Q).obj.toOGP) :
    ConcreteCategory.hom (grayProductRDCMap f g).hom p =
      (ConcreteCategory.hom f.hom p.1, ConcreteCategory.hom g.hom p.2) :=
  rfl

@[reassoc] theorem grayProductRDCMap_comp {P P' P'' Q Q' Q'' : RDCpx.{0}} (f : P ⟶ P')
    (g : Q ⟶ Q') (f' : P' ⟶ P'') (g' : Q' ⟶ Q'') :
    grayProductRDCMap f g ≫ grayProductRDCMap f' g' = grayProductRDCMap (f ≫ f') (g ≫ g') := by
  ext x
  rfl

def atomGrayProductIso (U V : Atom) :
    atomToRDCpx.obj (Atom.grayTensor U V) ≅
      grayProductRDC (atomToRDCpx.obj U) (atomToRDCpx.obj V) :=
  RDCpx.isoOfIso (Atom.grayTensorIso U V).symm

def grayProductCellMap {P Q : RDCpx.{0}} {U V : Atom} (f : atomToRDCpx.obj U ⟶ P)
    (g : atomToRDCpx.obj V ⟶ Q) : atomToRDCpx.obj (Atom.grayTensor U V) ⟶ grayProductRDC P Q :=
  (atomGrayProductIso U V).hom ≫ grayProductRDCMap f g

theorem grayProductCellMap_apply {P Q : RDCpx.{0}} {U V : Atom} (f : atomToRDCpx.obj U ⟶ P)
    (g : atomToRDCpx.obj V ⟶ Q) (t : (Atom.grayTensor U V).ogp) :
    ConcreteCategory.hom (grayProductCellMap f g).hom t =
      (ConcreteCategory.hom f.hom ((Atom.grayTensorIso U V).inv t).1,
        ConcreteCategory.hom g.hom ((Atom.grayTensorIso U V).inv t).2) :=
  rfl

theorem map_grayTensorMap_comp_grayProductCellMap {P Q : RDCpx.{0}} {U V U' V' : Atom}
    (a : U' ⟶ U) (b : V' ⟶ V) (f : atomToRDCpx.obj U ⟶ P) (g : atomToRDCpx.obj V ⟶ Q) :
    atomToRDCpx.map (Atom.grayTensorMap a b) ≫ grayProductCellMap f g =
      grayProductCellMap (atomToRDCpx.map a ≫ f) (atomToRDCpx.map b ≫ g) := by
  ext t
  change (ConcreteCategory.hom f.hom ((Atom.grayTensorIso U V).inv (Atom.grayTensorMap a b t)).1,
    ConcreteCategory.hom g.hom ((Atom.grayTensorIso U V).inv (Atom.grayTensorMap a b t)).2) = _
  rw [Atom.grayTensorMap_apply, Iso.hom_inv_id_apply]
  rfl

theorem injective_grayProductCellMap {P Q : RDCpx.{0}} {U V : Atom} {f : atomToRDCpx.obj U ⟶ P}
    {g : atomToRDCpx.obj V ⟶ Q} (hf : Function.Injective (ConcreteCategory.hom f.hom))
    (hg : Function.Injective (ConcreteCategory.hom g.hom)) :
    Function.Injective (ConcreteCategory.hom (grayProductCellMap f g).hom) := by
  intro s t h
  rw [grayProductCellMap_apply, grayProductCellMap_apply] at h
  apply IsInclusion.injective (f := (Atom.grayTensorIso U V).inv)
  exact Prod.ext (hf (congrArg Prod.fst h)) (hg (congrArg Prod.snd h))

private theorem exists_principal (P : RDCpx.{0}) (x : P.obj.toOGP) :
    ∃ (A : Atom) (ι : atomToRDCpx.obj A ⟶ P),
      Function.Injective (ConcreteCategory.hom ι.hom) ∧ ConcreteCategory.hom ι.hom A.top = x ∧
      ∀ {T : Atom} (h : atomToRDCpx.obj T ⟶ P), (∀ t, ConcreteCategory.hom h.hom t ≤ x) →
        ∃ d : T ⟶ A, atomToRDCpx.map d ≫ ι = h := by
  classical
  let (y : P.obj.toOGP) : FinEnum (P.obj.toOGP.restrict (.Iic y)) :=
    have : Fintype (P.obj.toOGP.restrict (.Iic y)) := (IsMoleculeIn.finite (P.obj.isRDC y)).fintype
    FinEnum.ofEquiv _ (Fintype.equivFin _)
  exact ⟨principalAtomRDC P x, principalInclusionRDC P x, injective_principalInclusionRDC P x,
    principalInclusionRDC_top P x, fun h hh =>
      ⟨principalLiftRDC P x h hh, principalLiftRDC_comp_principalInclusionRDC P x h hh⟩⟩

private theorem isCollapseHom_of_map_comp_eq {P : RDCpx.{0}} {T A : Atom}
    {ι : atomToRDCpx.obj A ⟶ P} (hι : Function.Injective (ConcreteCategory.hom ι.hom))
    {h : atomToRDCpx.obj T ⟶ P} {d : T ⟶ A} (hd : atomToRDCpx.map d ≫ ι = h)
    (htop : ConcreteCategory.hom ι.hom A.top = ConcreteCategory.hom h.hom T.top) :
    IsCollapseHom d := fun a => by
  have hle : ConcreteCategory.hom ι.hom a ≤ ConcreteCategory.hom h.hom T.top :=
    htop ▸ (ConcreteCategory.hom ι.hom).isMap.monotone (A.le_top a)
  obtain ⟨s, -, hs⟩ := (ConcreteCategory.hom h.hom).isMap.fibration hle
  refine ⟨s, hι ?_⟩
  rw [← hs, ← hd]
  rfl

private theorem exists_map_comp_eq_of_injective {P : RDCpx.{0}} {W T : Atom}
    {k : atomToRDCpx.obj W ⟶ P} (hk : Function.Injective (ConcreteCategory.hom k.hom))
    (h : atomToRDCpx.obj T ⟶ P)
    (hh : ∀ t, ∃ w, ConcreteCategory.hom k.hom w = ConcreteCategory.hom h.hom t) :
    ∃ d : T ⟶ W, atomToRDCpx.map d ≫ k = h := by
  obtain ⟨A, ι, hι, htop, hfac⟩ := exists_principal P (ConcreteCategory.hom k.hom W.top)
  obtain ⟨dk, hdk⟩ := hfac k fun w => (ConcreteCategory.hom k.hom).isMap.monotone (W.le_top w)
  obtain ⟨dh, hdh⟩ := hfac h fun t => by
    obtain ⟨w, hw⟩ := hh t
    exact hw ▸ (ConcreteCategory.hom k.hom).isMap.monotone (W.le_top w)
  have hinj : IsInclusionHom dk := fun a b hab => hk (by
    rw [← hdk]
    exact congrArg (ConcreteCategory.hom ι.hom) hab)
  have := isIso_of_isInclusionHom_of_isCollapseHom dk hinj
    (isCollapseHom_of_map_comp_eq hι hdk htop)
  refine ⟨dh ≫ inv dk, ?_⟩
  rw [atomToRDCpx.map_comp, Category.assoc, ← hdk, ← Category.assoc (atomToRDCpx.map (inv dk)),
    ← atomToRDCpx.map_comp, IsIso.inv_hom_id, atomToRDCpx.map_id, Category.id_comp, hdh]

theorem injective_of_isNondegenerate_realize {P : RDCpx.{0}} {T : Atom}
    (f : atomToRDCpx.obj T ⟶ P)
    (hf : Homotopical.EZCategory.IsNondegenerate (realize.{u}.obj P) (ULift.up f)) :
    Function.Injective (ConcreteCategory.hom f.hom) := by
  obtain ⟨A, ι, hι, htop, hfac⟩ := exists_principal P (ConcreteCategory.hom f.hom T.top)
  obtain ⟨d, hd⟩ := hfac f fun t => (ConcreteCategory.hom f.hom).isMap.monotone (T.le_top t)
  have := isSplitEpi_of_isCollapseHom d (isCollapseHom_of_map_comp_eq hι hd htop)
  have : IsIso d := hf d inferInstance ⟨ULift.up ι, congrArg ULift.up hd⟩
  intro s t hst
  have hinj : Function.Injective d := fun a b hab => by
    simpa using congrArg (inv d) hab
  apply hinj
  apply hι
  rw [← hd] at hst
  exact hst

private noncomputable def realizeGrayTensorUnit (P Q : RDCpx.{0}) :
    realize.{u}.obj P ⊠ realize.{u}.obj Q ⟶
      grayTensorIndex ⋙ realize.{u}.obj (grayProductRDC P Q) where
  app p := ↾fun fg => ULift.up (grayProductCellMap fg.1.down fg.2.down)
  naturality p q h := by
    ext ⟨⟨f⟩, ⟨g⟩⟩
    exact congrArg ULift.up (map_grayTensorMap_comp_grayProductCellMap h.1.unop h.2.unop f g).symm

private noncomputable def realizeGrayTensorHom (P Q : RDCpx.{0}) :
    grayTensor (realize.{u}.obj P) (realize.{u}.obj Q) ⟶ realize.obj (grayProductRDC P Q) :=
  (grayTensor _ _).descOfIsLeftKanExtension (grayTensorUnit _ _) _ (realizeGrayTensorUnit P Q)

private theorem realizeGrayTensorHom_app_grayTensorCell {P Q : RDCpx.{0}} {U V : Atom}
    (f : atomToRDCpx.obj U ⟶ P) (g : atomToRDCpx.obj V ⟶ Q) :
    (realizeGrayTensorHom.{u} P Q).app (op (Atom.grayTensor U V))
        (grayTensorCell (X := realize.{u}.obj P) (Y := realize.{u}.obj Q) (ULift.up f)
          (ULift.up g)) =
      ULift.up (grayProductCellMap f g) :=
  ConcreteCategory.congr_hom
    ((grayTensor _ _).descOfIsLeftKanExtension_fac_app (grayTensorUnit _ _) _
      (realizeGrayTensorUnit P Q) (op U, op V))
    ((ULift.up f, ULift.up g) : (realize.{u}.obj P).obj (op U) × (realize.{u}.obj Q).obj (op V))

private theorem surjective_realizeGrayTensorHom_app (P Q : RDCpx.{0}) (T : Atom) :
    Function.Surjective ((realizeGrayTensorHom.{u} P Q).app (op T)) := by
  rintro ⟨h⟩
  obtain ⟨A, ιA, hιA, htopA, -⟩ := exists_principal P (ConcreteCategory.hom h.hom T.top).1
  obtain ⟨B, ιB, hιB, htopB, -⟩ := exists_principal Q (ConcreteCategory.hom h.hom T.top).2
  obtain ⟨d, hd⟩ := exists_map_comp_eq_of_injective (injective_grayProductCellMap hιA hιB) h
    fun t => by
      have hle := (ConcreteCategory.hom h.hom).isMap.monotone (T.le_top t)
      obtain ⟨a, -, ha⟩ := (ConcreteCategory.hom ιA.hom).isMap.fibration (htopA ▸ hle.1)
      obtain ⟨b, -, hb⟩ := (ConcreteCategory.hom ιB.hom).isMap.fibration (htopB ▸ hle.2)
      refine ⟨(Atom.grayTensorIso A B).hom (a, b), ?_⟩
      rw [grayProductCellMap_apply, Iso.hom_inv_id_apply]
      exact Prod.ext ha hb
  refine ⟨(grayTensor _ _).map d.op (grayTensorCell (ULift.up ιA) (ULift.up ιB)), ?_⟩
  rw [NatTrans.naturality_apply, realizeGrayTensorHom_app_grayTensorCell]
  exact congrArg ULift.up hd

private theorem exists_collapse_injective_presentation {P Q : RDCpx.{0}} {T : Atom}
    (w : diagram (grayTensor (realize.{u}.obj P) (realize.{u}.obj Q)) T) :
    ∃ (A B : Atom) (c : T ⟶ Atom.grayTensor A B) (f : atomToRDCpx.obj A ⟶ P)
      (g : atomToRDCpx.obj B ⟶ Q), IsCollapseHom c ∧
      Function.Injective (ConcreteCategory.hom f.hom) ∧
      Function.Injective (ConcreteCategory.hom g.hom) ∧
      w = (grayTensor _ _).map c.op (grayTensorCell (ULift.up f) (ULift.up g)) := by
  obtain ⟨S, p, w₀, hp, hw₀, rfl⟩ := Homotopical.EZCategory.exists_isNondegenerate _ _ w
  obtain ⟨A, B, ⟨f⟩, ⟨g⟩, e, hf, hg, rfl⟩ := exists_tensor_presentation w₀
    fun h => (isDegenerate_iff_not_isNondegenerate _ w₀).1 h hw₀
  refine ⟨A, B, p ≫ e.hom, f, g, ?_, injective_of_isNondegenerate_realize f
    (not_not.1 ((isDegenerate_iff_not_isNondegenerate _ _).not.1 hf)),
    injective_of_isNondegenerate_realize g
    (not_not.1 ((isDegenerate_iff_not_isNondegenerate _ _).not.1 hg)), ?_⟩
  · exact ((isCollapseHom_of_iso e).comp (@isCollapseHom_of_isSplitEpi _ _ p hp))
  · rw [op_comp, Functor.map_comp_apply]

private theorem injective_realizeGrayTensorHom_app (P Q : RDCpx.{0}) (T : Atom) :
    Function.Injective ((realizeGrayTensorHom.{u} P Q).app (op T)) := by
  intro w w' hww'
  obtain ⟨A, B, c, f, g, hc, hf, hg, rfl⟩ := exists_collapse_injective_presentation w
  obtain ⟨A', B', c', f', g', hc', hf', hg', rfl⟩ := exists_collapse_injective_presentation w'
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply,
    realizeGrayTensorHom_app_grayTensorCell, realizeGrayTensorHom_app_grayTensorCell] at hww'
  have hcomp : atomToRDCpx.map c ≫ grayProductCellMap f g =
      atomToRDCpx.map c' ≫ grayProductCellMap f' g' := ULift.up_inj.1 hww'
  have hval : ∀ a b, ∃ a' b', ConcreteCategory.hom f'.hom a' = ConcreteCategory.hom f.hom a ∧
      ConcreteCategory.hom g'.hom b' = ConcreteCategory.hom g.hom b := fun a b => by
    obtain ⟨s, hs⟩ := hc ((Atom.grayTensorIso A B).hom (a, b))
    have := congrArg (fun k : atomToRDCpx.obj T ⟶ grayProductRDC P Q =>
      ConcreteCategory.hom k.hom s) hcomp
    change ConcreteCategory.hom (grayProductCellMap f g).hom (c s) =
      ConcreteCategory.hom (grayProductCellMap f' g').hom (c' s) at this
    rw [hs, grayProductCellMap_apply, grayProductCellMap_apply, Iso.hom_inv_id_apply] at this
    exact ⟨_, _, (congrArg Prod.fst this).symm, (congrArg Prod.snd this).symm⟩
  obtain ⟨a, ha⟩ := exists_map_comp_eq_of_injective hf' f fun t => by
    obtain ⟨a', -, h, -⟩ := hval t B.top
    exact ⟨a', h⟩
  obtain ⟨b, hb⟩ := exists_map_comp_eq_of_injective hg' g fun t => by
    obtain ⟨_, b', -, h⟩ := hval A.top t
    exact ⟨b', h⟩
  have hcell : grayTensorCell (X := realize.{u}.obj P) (Y := realize.{u}.obj Q) (ULift.up f)
      (ULift.up g) = (grayTensor _ _).map (Atom.grayTensorMap a b).op
        (grayTensorCell (X := realize.{u}.obj P) (Y := realize.{u}.obj Q) (ULift.up f')
          (ULift.up g')) := by
    subst ha hb
    exact grayTensorCell_restrict (X := realize.{u}.obj P) (Y := realize.{u}.obj Q) a b
      (ULift.up f') (ULift.up g')
  have hcc : c ≫ Atom.grayTensorMap a b = c' := by
    refine Atom.hom_ext fun t => injective_grayProductCellMap hf' hg' ?_
    have := congrArg (fun k : atomToRDCpx.obj T ⟶ grayProductRDC P Q =>
      ConcreteCategory.hom k.hom t) hcomp
    rw [← ha, ← hb, ← map_grayTensorMap_comp_grayProductCellMap] at this
    exact this
  rw [hcell, ← Functor.map_comp_apply, ← op_comp, hcc]

private theorem isIso_realizeGrayTensorHom (P Q : RDCpx.{0}) :
    IsIso (realizeGrayTensorHom.{u} P Q) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨T⟩
  rw [CategoryTheory.isIso_iff_bijective]
  exact ⟨injective_realizeGrayTensorHom_app P Q T, surjective_realizeGrayTensorHom_app P Q T⟩

noncomputable def realizeGrayProductIso (P Q : RDCpx.{0}) :
    realize.{u}.obj (grayProductRDC P Q) ≅ grayTensor (realize.obj P) (realize.obj Q) :=
  have := isIso_realizeGrayTensorHom.{u} P Q
  (asIso (realizeGrayTensorHom P Q)).symm

@[simp] theorem realizeGrayProductIso_inv_app_grayTensorCell {P Q : RDCpx.{0}} {U V : Atom}
    (f : atomToRDCpx.obj U ⟶ P) (g : atomToRDCpx.obj V ⟶ Q) :
    (realizeGrayProductIso.{u} P Q).inv.app (op (Atom.grayTensor U V))
        (grayTensorCell (X := realize.{u}.obj P) (Y := realize.{u}.obj Q) (ULift.up f)
          (ULift.up g)) =
      ULift.up (grayProductCellMap f g) :=
  realizeGrayTensorHom_app_grayTensorCell f g

private theorem grayTensorBifunctor_map_comp_realizeGrayProductIso_inv {P P' Q Q' : RDCpx.{0}}
    (φ : P' ⟶ P) (ψ : Q' ⟶ Q) :
    grayTensorBifunctor.map (realize.{u}.map φ, realize.{u}.map ψ) ≫
        (realizeGrayProductIso P Q).inv =
      (realizeGrayProductIso P' Q').inv ≫ realize.map (grayProductRDCMap φ ψ) := by
  refine grayTensor_hom_ext fun A B ⟨f⟩ ⟨g⟩ => ?_
  rw [NatTrans.comp_app, NatTrans.comp_app, types_comp_apply, types_comp_apply]
  refine (congrArg ((realizeGrayProductIso.{u} P Q).inv.app _) (grayTensorCell_naturality
    (realize.{u}.map φ) (realize.{u}.map ψ) (ULift.up f) (ULift.up g))).trans ?_
  refine (realizeGrayProductIso_inv_app_grayTensorCell (f ≫ φ) (g ≫ ψ)).trans ?_
  refine Eq.trans ?_ (congrArg ((realize.{u}.map (grayProductRDCMap φ ψ)).app _)
    (realizeGrayProductIso_inv_app_grayTensorCell f g).symm)
  rw [realize_map_app]
  refine congrArg ULift.up ?_
  ext t
  rfl

@[reassoc] theorem realize_map_grayProductRDCMap_comp_realizeGrayProductIso_hom
    {P P' Q Q' : RDCpx.{0}} (φ : P' ⟶ P) (ψ : Q' ⟶ Q) :
    realize.{u}.map (grayProductRDCMap φ ψ) ≫ (realizeGrayProductIso P Q).hom =
      (realizeGrayProductIso P' Q').hom ≫
        grayTensorBifunctor.map (realize.{u}.map φ, realize.{u}.map ψ) := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← grayTensorBifunctor_map_comp_realizeGrayProductIso_inv,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem range_realize_map_grayProductRDCMap_restrictIncl {P Q : RDCpx.{0}}
    (S : LowerSet P.obj.toOGP) (T : LowerSet Q.obj.toOGP) :
    Subfunctor.range (realize.{u}.map (grayProductRDCMap (P.restrictIncl S) (Q.restrictIncl T))) =
      realizeSubset (grayProductRDC P Q) (S ×ˢ T) := by
  ext ⟨A⟩ ⟨h⟩
  constructor
  · rintro ⟨⟨x⟩, hx⟩ t
    obtain rfl := ULift.up_inj.1 hx
    exact ⟨(ConcreteCategory.hom x.hom t).1.2, (ConcreteCategory.hom x.hom t).2.2⟩
  · intro hh
    refine ⟨ULift.up (RDCpx.codRestrict h (S ×ˢ T) hh ≫
      (RDCpx.isoOfIso (grayProductRestrictIso S T)).hom), congrArg ULift.up ?_⟩
    exact WideSubcategory.hom_ext _ (ConcreteCategory.hom_ext _ _ fun _ => rfl)

end Atoms.Diagrammatic
