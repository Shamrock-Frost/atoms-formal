import Atoms.Diagrammatic.Realization
import Atoms.Molecule.RegularComplex.Morphism
import Atoms.ForMathlib.CategoryTheory.Subfunctor.Colimits

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape

universe u

namespace Atoms.Diagrammatic

def principalAtomRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP]
    (x : P.obj.toOGP) : Atom :=
  Atom.ofOGP (P.obj.toOGP.restrict (.Iic x)) (IsAtomIn.isAtom_restrict ⟨P.obj.isRDC x, x, rfl⟩)

def principalAtomIsoRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP]
    (x : P.obj.toOGP) : P.obj.toOGP.restrict (.Iic x) ≅ (principalAtomRDC P x).ogp :=
  FiniteOGP.ofOGPIso _

abbrev principalInclusionOGP (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP]
    (x : P.obj.toOGP) : (principalAtomRDC P x).ogp ⟶ P.obj.toOGP :=
  (principalAtomIsoRDC P x).inv ≫ incl (.Iic x)

instance (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP]
    (x : P.obj.toOGP) : IsInclusion (principalInclusionOGP P x) :=
  inferInstanceAs (IsInclusion ((principalAtomIsoRDC P x).inv ≫ incl (.Iic x)))

def principalInclusionRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP]
    (x : P.obj.toOGP) : atomToRDCpx.obj (principalAtomRDC P x) ⟶ P :=
  @RDCpx.ofInclusion (atomToRDCpx.obj (principalAtomRDC P x)) P (principalInclusionOGP P x)
    (inferInstanceAs (IsInclusion (principalInclusionOGP P x)))

theorem principalInclusionRDC_apply_principalAtomIsoRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP]
    (x : P.obj.toOGP)
    (y : P.obj.toOGP.restrict (.Iic x)) :
    ConcreteCategory.hom (principalInclusionRDC P x).hom
      ((principalAtomIsoRDC P x).hom y) = y.1 :=
  congrArg Subtype.val (ConcreteCategory.congr_hom (principalAtomIsoRDC P x).hom_inv_id y)

theorem principalInclusionRDC_mem_closure (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))]
    [DecidableLE P.obj.toOGP] (x : P.obj.toOGP) (a : (principalAtomRDC P x).ogp) :
    ConcreteCategory.hom (principalInclusionRDC P x).hom a ∈ LowerSet.Iic x :=
  ((principalAtomIsoRDC P x).inv a).2

theorem injective_principalInclusionRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))]
    [DecidableLE P.obj.toOGP] (x : P.obj.toOGP) :
    Function.Injective (ConcreteCategory.hom (principalInclusionRDC P x).hom) :=
  IsInclusion.injective (f := principalInclusionOGP P x)

theorem image_principalInclusionRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))]
    [DecidableLE P.obj.toOGP] (x : P.obj.toOGP) :
    Set.range (ConcreteCategory.hom (principalInclusionRDC P x).hom) = Set.Iic x := by
  ext y
  exact ⟨fun ⟨a, ha⟩ => ha ▸ principalInclusionRDC_mem_closure P x a,
    fun hy => ⟨(principalAtomIsoRDC P x).hom ⟨y, hy⟩,
      principalInclusionRDC_apply_principalAtomIsoRDC P x ⟨y, hy⟩⟩⟩

theorem dimension_principalAtomRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))]
    [DecidableLE P.obj.toOGP] (x : P.obj.toOGP) :
    (principalAtomRDC P x).dimension = grade ℕ x := by
  have h := krullDim_map (principalInclusionOGP P x) ⊤
  rw [principalInclusionOGP, map_comp, map_top_of_isIso, map_incl_top, LowerSet.krullDim_Iic,
    LowerSet.krullDim_top, (principalAtomRDC P x).krullDim_eq_dimension] at h
  exact_mod_cast h.symm

theorem principalInclusionRDC_top (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))]
    [DecidableLE P.obj.toOGP] (x : P.obj.toOGP) :
    ConcreteCategory.hom (principalInclusionRDC P x).hom (principalAtomRDC P x).top = x :=
  le_antisymm (principalInclusionRDC_mem_closure P x (principalAtomRDC P x).top)
    ((principalInclusionRDC_apply_principalAtomIsoRDC P x
      ⟨x, LowerSet.mem_Iic_iff.2 le_rfl⟩).symm.le.trans
      ((ConcreteCategory.hom (principalInclusionRDC P x).hom).isMap.monotone
        ((principalAtomRDC P x).le_top _)))

theorem hom_ext_principalInclusionRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))]
    [DecidableLE P.obj.toOGP] (x : P.obj.toOGP) {T : Atom}
    {g g' : T ⟶ principalAtomRDC P x}
    (h : atomToRDCpx.map g ≫ principalInclusionRDC P x =
      atomToRDCpx.map g' ≫ principalInclusionRDC P x) : g = g' :=
  Atom.hom_ext fun t => injective_principalInclusionRDC P x
    (congrArg (fun f : atomToRDCpx.obj T ⟶ P => ConcreteCategory.hom f.hom t) h)

def principalLiftRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP]
    (x : P.obj.toOGP) {T : Atom} (f : atomToRDCpx.obj T ⟶ P)
    (h : ∀ t, ConcreteCategory.hom f.hom t ∈ LowerSet.Iic x) :
    T ⟶ principalAtomRDC P x :=
  InducedCategory.homMk (RDCpx.codRestrict f (.Iic x) h ≫
    @RDCpx.ofInclusion (RDCpx.restrict P (.Iic x)) (principalAtomRDC P x).rdc
      (principalAtomIsoRDC P x).hom
      (@IsInclusion.of_isIso _ _ (principalAtomIsoRDC P x).hom
        (Iso.isIso_hom (principalAtomIsoRDC P x))))

theorem principalLiftRDC_comp_principalInclusionRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP]
    (x : P.obj.toOGP) {T : Atom}
    (f : atomToRDCpx.obj T ⟶ P) (h : ∀ t, ConcreteCategory.hom f.hom t ∈ LowerSet.Iic x) :
    atomToRDCpx.map (principalLiftRDC P x f h) ≫ principalInclusionRDC P x = f := by
  ext t
  exact principalInclusionRDC_apply_principalAtomIsoRDC P x ⟨ConcreteCategory.hom f.hom t, h t⟩

theorem eq_principalLiftRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP]
    (x : P.obj.toOGP) {T : Atom} (g : T ⟶ principalAtomRDC P x)
    (h : ∀ t, ConcreteCategory.hom (atomToRDCpx.map g ≫ principalInclusionRDC P x).hom t ∈
      LowerSet.Iic x) :
    g = principalLiftRDC P x (atomToRDCpx.map g ≫ principalInclusionRDC P x) h :=
  hom_ext_principalInclusionRDC P x
    (principalLiftRDC_comp_principalInclusionRDC P x _ h).symm

def principalMapRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP]
    {x y : P.obj.toOGP} (hxy : x ≤ y) : principalAtomRDC P x ⟶ principalAtomRDC P y :=
  principalLiftRDC P y (principalInclusionRDC P x) fun a =>
    (principalInclusionRDC_mem_closure P x a).trans hxy

theorem principalMapRDC_comp_principalInclusionRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP]
    {x y : P.obj.toOGP} (hxy : x ≤ y) :
    atomToRDCpx.map (principalMapRDC P hxy) ≫ principalInclusionRDC P y =
      principalInclusionRDC P x :=
  principalLiftRDC_comp_principalInclusionRDC _ _ _ _

def principalDiagramRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP] :
    P.obj.toOGP ⥤ Atom where
  obj x := principalAtomRDC P x
  map f := principalMapRDC P (leOfHom f)
  map_id x := hom_ext_principalInclusionRDC P x (by
    rw [principalMapRDC_comp_principalInclusionRDC, atomToRDCpx.map_id, Category.id_comp])
  map_comp f g := hom_ext_principalInclusionRDC P _ (by
    rw [principalMapRDC_comp_principalInclusionRDC, atomToRDCpx.map_comp, Category.assoc,
      principalMapRDC_comp_principalInclusionRDC, principalMapRDC_comp_principalInclusionRDC])

theorem principalLiftRDC_comp_principalMapRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))]
    [DecidableLE P.obj.toOGP] {x y : P.obj.toOGP} (hxy : x ≤ y) {T : Atom}
    (f : atomToRDCpx.obj T ⟶ P) (h : ∀ t, ConcreteCategory.hom f.hom t ∈ LowerSet.Iic x)
    (h' : ∀ t, ConcreteCategory.hom f.hom t ∈ LowerSet.Iic y) :
    principalLiftRDC P x f h ≫ principalMapRDC P hxy = principalLiftRDC P y f h' :=
  hom_ext_principalInclusionRDC P y (by
    rw [atomToRDCpx.map_comp, Category.assoc, principalMapRDC_comp_principalInclusionRDC,
      principalLiftRDC_comp_principalInclusionRDC, principalLiftRDC_comp_principalInclusionRDC])

def realizeCocone (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP] :
    Cocone (principalDiagramRDC P ⋙ uliftYoneda.{u}) where
  pt := realize.obj P
  ι :=
    { app x := (realizeAtomIso (principalAtomRDC P x)).inv ≫
        realize.map (principalInclusionRDC P x)
      naturality x y f := by
        ext ⟨T⟩ ⟨g : T ⟶ principalAtomRDC P x⟩
        exact congrArg ULift.up (congrArg (atomToRDCpx.map g ≫ ·)
          (principalMapRDC_comp_principalInclusionRDC P (leOfHom f))) }

theorem realizeCocone_pt (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP] :
    (realizeCocone.{u} P).pt = realize.obj P :=
  rfl

theorem ιColimitType_eq_ιColimitType_principalLiftRDC (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP]
    (T : Atom) (x : P.obj.toOGP)
    (g : T ⟶ principalAtomRDC P x) :
    ((principalDiagramRDC P ⋙ uliftYoneda.{u}) ⋙
        (evaluation Atomᵒᵖ (Type u)).obj (op T)).ιColimitType x ⟨g⟩ =
      ((principalDiagramRDC P ⋙ uliftYoneda.{u}) ⋙
        (evaluation Atomᵒᵖ (Type u)).obj (op T)).ιColimitType
        (ConcreteCategory.hom (atomToRDCpx.map g ≫ principalInclusionRDC P x).hom T.top)
        ⟨principalLiftRDC P _ (atomToRDCpx.map g ≫ principalInclusionRDC P x)
          (hom_apply_mem_closure_apply_top _)⟩ := by
  have hzx : ConcreteCategory.hom (atomToRDCpx.map g ≫ principalInclusionRDC P x).hom T.top ≤ x :=
    principalInclusionRDC_mem_closure P x (g T.top)
  refine (Functor.ιColimitType_eq_iff _ _ _).2
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨homOfLE hzx, ?_⟩))
  change ULift.up g = ULift.up (principalLiftRDC P _ (atomToRDCpx.map g ≫ principalInclusionRDC P x)
    (hom_apply_mem_closure_apply_top _) ≫ principalMapRDC P (leOfHom (homOfLE hzx)))
  exact congrArg ULift.up ((eq_principalLiftRDC P x g fun t =>
    principalInclusionRDC_mem_closure P x (g t)).trans
      (principalLiftRDC_comp_principalMapRDC P _ _ _ _).symm)

theorem bijective_descColimitType_realizeCocone (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))]
    [DecidableLE P.obj.toOGP] (T : Atomᵒᵖ) :
    Function.Bijective (Functor.descColimitType _
      ((Functor.coconeTypesEquiv _).symm
        (((evaluation Atomᵒᵖ (Type u)).obj T).mapCocone (realizeCocone P)))) := by
  induction T with | op T => ?_
  refine ⟨fun a b hab => ?_, fun f => ?_⟩
  · obtain ⟨x, ⟨g⟩, rfl⟩ := Functor.ιColimitType_jointly_surjective _ a
    obtain ⟨y, ⟨g'⟩, rfl⟩ := Functor.ιColimitType_jointly_surjective _ b
    change T ⟶ principalAtomRDC P x at g
    change T ⟶ principalAtomRDC P y at g'
    change (realize.obj P).map g.op ⟨principalInclusionRDC P x⟩ =
      (realize.obj P).map g'.op ⟨principalInclusionRDC P y⟩ at hab
    simp only [realize_obj_map] at hab
    have key : ∀ f f' : atomToRDCpx.obj T ⟶ P, f = f' →
        ((principalDiagramRDC P ⋙ uliftYoneda.{u}) ⋙
            (evaluation Atomᵒᵖ (Type u)).obj (op T)).ιColimitType
          (ConcreteCategory.hom f.hom T.top)
          ⟨principalLiftRDC P _ f (hom_apply_mem_closure_apply_top f)⟩ =
        ((principalDiagramRDC P ⋙ uliftYoneda.{u}) ⋙
            (evaluation Atomᵒᵖ (Type u)).obj (op T)).ιColimitType
          (ConcreteCategory.hom f'.hom T.top)
          ⟨principalLiftRDC P _ f' (hom_apply_mem_closure_apply_top f')⟩ := by
      rintro f _ rfl
      rfl
    exact (ιColimitType_eq_ιColimitType_principalLiftRDC P T x g).trans
      ((key _ _ (ULift.up_inj.1 hab)).trans
        (ιColimitType_eq_ιColimitType_principalLiftRDC P T y g').symm)
  · obtain ⟨f : atomToRDCpx.obj T ⟶ P⟩ := f
    refine ⟨((principalDiagramRDC P ⋙ uliftYoneda.{u}) ⋙
      (evaluation Atomᵒᵖ (Type u)).obj (op T)).ιColimitType
      (ConcreteCategory.hom f.hom T.top)
      ⟨principalLiftRDC P (ConcreteCategory.hom f.hom T.top) f
        (hom_apply_mem_closure_apply_top f)⟩, ?_⟩
    exact congrArg ULift.up
      (principalLiftRDC_comp_principalInclusionRDC P (ConcreteCategory.hom f.hom T.top) f _)

noncomputable def isColimitRealizeCocone (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))]
    [DecidableLE P.obj.toOGP] :
    IsColimit (realizeCocone.{u} P) :=
  evaluationJointlyReflectsColimits _ fun T => Nonempty.some <|
    (Types.isColimit_iff_coconeTypesIsColimit _).2
      ⟨bijective_descColimitType_realizeCocone P T⟩

theorem isPushout_realize_of_union (P : RDCpx.{0}) {A B : LowerSet P.obj.toOGP}
    (hAB : A ⊔ B = ⊤) :
    IsPushout
      (realize.{u}.map (RDCpx.inclusion P (inf_le_left : A ⊓ B ≤ A)))
      (realize.map (RDCpx.inclusion P (inf_le_right : A ⊓ B ≤ B)))
      (realize.map (RDCpx.restrictIncl P A))
      (realize.map (RDCpx.restrictIncl P B)) := by
  have htop : realizeSubset P A ⊔ realizeSubset P B = ⊤ := by
    rw [← realizeSubset_union P A B, hAB, realizeSubset_univ]
  have : IsIso (realizeSubset P A ⊔ realizeSubset P B).ι :=
    (Subfunctor.eq_top_iff_isIso _).1 htop
  have hsq : Lattice.BicartSq (realizeSubset P A ⊓ realizeSubset P B) (realizeSubset P A)
      (realizeSubset P B) (realizeSubset P A ⊔ realizeSubset P B) := ⟨rfl, rfl⟩
  refine (Subfunctor.isPushout_of_bicartSq hsq).of_iso
    (realizeRestrictIso P (A ⊓ B) _ (realizeSubset_inter P A B)).symm
    (realizeRestrictIso P A _ rfl).symm (realizeRestrictIso P B _ rfl).symm
    (asIso (realizeSubset P A ⊔ realizeSubset P B).ι) ?_ ?_ ?_ ?_ <;>
  · ext T g
    rfl

theorem realize_map_restrictInclOfSubset_comp (P : RDCpx.{0})
    {S T R : LowerSet P.obj.toOGP} (hST : S ≤ T) (hTR : T ≤ R) :
    realize.{u}.map (RDCpx.inclusion P hST) ≫ realize.map (RDCpx.inclusion P hTR) =
      realize.map (RDCpx.inclusion P (hST.trans hTR)) := by
  rw [← realize.map_comp]
  rfl

theorem isPushout_realize_restrictInclOfSubset (P : RDCpx.{0})
    (A B : LowerSet P.obj.toOGP) :
    IsPushout
      (realize.{u}.map (RDCpx.inclusion P (inf_le_left : A ⊓ B ≤ A)))
      (realize.map (RDCpx.inclusion P (inf_le_right : A ⊓ B ≤ B)))
      (realize.map (RDCpx.inclusion P (le_sup_left : A ≤ A ⊔ B)))
      (realize.map (RDCpx.inclusion P (le_sup_right : B ≤ A ⊔ B))) := by
  have hsq : Lattice.BicartSq (realizeSubset P A ⊓ realizeSubset P B) (realizeSubset P A)
      (realizeSubset P B) (realizeSubset P A ⊔ realizeSubset P B) := ⟨rfl, rfl⟩
  refine (Subfunctor.isPushout_of_bicartSq hsq).of_iso
    (realizeRestrictIso P (A ⊓ B) _ (realizeSubset_inter P A B)).symm
    (realizeRestrictIso P A _ rfl).symm (realizeRestrictIso P B _ rfl).symm
    (realizeRestrictIso P (A ⊔ B) _ (realizeSubset_union P A B)).symm
    ?_ ?_ ?_ ?_ <;>
  · ext T g
    rfl

def realizeRestrictPrincipalIso (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))]
    [DecidableLE P.obj.toOGP] (x : P.obj.toOGP) {S : LowerSet P.obj.toOGP}
    (hSx : S ≤ .Iic x) (S' : LowerSet (principalAtomRDC P x).ogp)
    (hS' : ∀ a, a ∈ S' ↔ ConcreteCategory.hom (principalInclusionRDC P x).hom a ∈ S) :
    realize.{u}.obj (RDCpx.restrict P S) ≅
      (closedSubpresheaf (principalAtomRDC P x) S').toFunctor :=
  NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun g =>
        ⟨⟨principalLiftRDC P x (g.down ≫ RDCpx.restrictIncl P S)
          fun t => hSx (ConcreteCategory.hom g.down.hom t).2⟩,
          fun t => (hS' _).2 ((congrArg (· ∈ S)
            (principalInclusionRDC_apply_principalAtomIsoRDC P x _)).mpr
              (ConcreteCategory.hom g.down.hom t).2)⟩
      invFun := fun f =>
        ⟨restrictLift P S (atomToRDCpx.map f.1.down ≫ principalInclusionRDC P x)
          fun t => (hS' _).1 (f.2 t)⟩
      left_inv := fun g => ULift.ext _ _ (WideSubcategory.hom_ext _
        (ConcreteCategory.hom_ext _ _ fun t => by
          refine Subtype.ext ?_
          exact principalInclusionRDC_apply_principalAtomIsoRDC P x
            ⟨(ConcreteCategory.hom g.down.hom t).1, hSx (ConcreteCategory.hom g.down.hom t).2⟩))
      right_inv := fun f => Subtype.ext (ULift.ext _ _ (eq_principalLiftRDC P x f.1.down _).symm) })
    (fun {V W} h => by
    ext g
    refine Subtype.ext (ULift.ext _ _ (hom_ext_principalInclusionRDC P x
      ((principalLiftRDC_comp_principalInclusionRDC P x _ _).trans ?_)))
    change _ = atomToRDCpx.map
      (h.unop ≫ principalLiftRDC P x (g.down ≫ RDCpx.restrictIncl P S) _) ≫ _
    rw [atomToRDCpx.map_comp, Category.assoc, principalLiftRDC_comp_principalInclusionRDC]
    rfl)

noncomputable def realizeRestrictPrincipalArrowIso (P : RDCpx.{0})
    [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))]
    [DecidableLE P.obj.toOGP] (x : P.obj.toOGP) {S : LowerSet P.obj.toOGP}
    (hSx : S ≤ .Iic x) (S' : LowerSet (principalAtomRDC P x).ogp)
    (hS' : ∀ a, a ∈ S' ↔ ConcreteCategory.hom (principalInclusionRDC P x).hom a ∈ S) :
    Arrow.mk (realize.{u}.map (RDCpx.inclusion P hSx)) ≅
      Arrow.mk (closedSubpresheaf (principalAtomRDC P x) S').ι :=
  have : IsIso (closedSubpresheaf (principalAtomRDC P x) ⊤).ι :=
    (Subfunctor.eq_top_iff_isIso _).1 (by
      ext ⟨T⟩ f
      exact iff_of_true (fun _ => LowerSet.mem_top) trivial)
  Arrow.isoMk (realizeRestrictPrincipalIso P x hSx S' hS')
    (realizeRestrictPrincipalIso P x le_rfl ⊤
        (fun a => iff_of_true LowerSet.mem_top (principalInclusionRDC_mem_closure P x a)) ≪≫
      asIso (closedSubpresheaf (principalAtomRDC P x) ⊤).ι) (by
    ext V ⟨g⟩
    change atomToRDCpx.obj V.unop ⟶ P.restrict S at g
    refine ULift.ext _ _ (hom_ext_principalInclusionRDC P x
      (((principalLiftRDC_comp_principalInclusionRDC P x _ _).trans ?_).trans
        (principalLiftRDC_comp_principalInclusionRDC P x _ _).symm))
    exact ((Category.assoc g (P.inclusion hSx) (P.restrictIncl (.Iic x))).trans
      (congrArg (g ≫ ·) (P.inclusion_restrictIncl hSx))).symm)

def realizeRestrictIsoOfIso (K : RDCpx.{0}) (V : Atom) (e : K.obj.toOGP ≅ V.ogp)
    (S : LowerSet K.obj.toOGP) (S' : LowerSet V.ogp) (hS' : ∀ p, e.hom p ∈ S' ↔ p ∈ S) :
    realize.{u}.obj (K.restrict S) ≅ (closedSubpresheaf V S').toFunctor :=
  NatIso.ofComponents (fun T => Equiv.toIso
      (X := ULift.{u} (atomToRDCpx.obj T.unop ⟶ K.restrict S))
    { toFun := fun g => ⟨⟨Atom.fullyFaithful.preimage
          (g.down ≫ RDCpx.restrictIncl K S ≫ (RDCpx.isoOfIso (Q := V.rdc) e).hom)⟩,
        fun t => (hS' _).2 (ConcreteCategory.hom g.down.hom t).2⟩
      invFun := fun f => ⟨restrictLift K S
        (atomToRDCpx.map f.1.down ≫ (RDCpx.isoOfIso (Q := V.rdc) e).inv) fun t =>
          (hS' _).1 (by
            change e.hom (e.inv
              (ConcreteCategory.hom (atomToRDCpx.map f.1.down).hom t)) ∈ S'
            rw [Iso.inv_hom_id_apply]
            exact f.2 t)⟩
      left_inv := fun g => ULift.ext _ _ (by
        ext t
        exact Iso.hom_inv_id_apply e _)
      right_inv := fun f => Subtype.ext (ULift.ext _ _
        (Atom.hom_ext fun t => Iso.inv_hom_id_apply e _)) })
    (fun _ => rfl)

end Atoms.Diagrammatic
