import Atoms.Diagrammatic.Pasting.Boundary
import Atoms.Diagrammatic.Pasting.Units
import Atoms.Diagrammatic.Suspension.Basic
import Atoms.Molecule.MoleculeShape.SuspensionCylinder

open CategoryTheory Limits Opposite Order Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

noncomputable def realizeSuspensionPoles (P : RDCpx.{0}) :
    pointPair.{u} ⟶ realize.obj (RDCpx.suspensionFunctor.obj P) :=
  coprod.desc ((realizeAtomIso atomPoint).inv ≫ realize.map (suspPoleRDC P false))
    ((realizeAtomIso atomPoint).inv ≫ realize.map (suspPoleRDC P true))

@[reassoc (attr := simp)] theorem realizeSuspensionPoles_comp {P Q : RDCpx.{0}} (f : P ⟶ Q) :
    realizeSuspensionPoles.{u} P ≫ realize.map (RDCpx.suspensionFunctor.map f) =
      realizeSuspensionPoles Q := by
  refine coprod.hom_ext ?_ ?_ <;>
    simp only [realizeSuspensionPoles, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
      coprod.inl_desc, coprod.inr_desc, Category.assoc, ← Functor.map_comp,
      suspPoleRDC_comp_suspensionFunctor_map]

def suspCell {P : RDCpx.{0}} {T : Atom} (c : atomToRDCpx.obj T ⟶ P) :
    atomToRDCpx.obj (atomSuspension.obj T) ⟶ RDCpx.suspensionFunctor.obj P :=
  (atomSuspensionRDCIso T).hom ≫ RDCpx.suspensionFunctor.map c

@[reassoc] theorem suspCell_comp {P : RDCpx.{0}} {T T' : Atom} (g : T' ⟶ T)
    (c : atomToRDCpx.obj T ⟶ P) :
    suspCell (atomToRDCpx.map g ≫ c) = atomToRDCpx.map (atomSuspension.map g) ≫ suspCell c := by
  rw [suspCell, suspCell, atomSuspensionRDCIso_hom_naturality_assoc, Functor.map_comp]

@[reassoc] theorem suspCell_comp_suspensionFunctor_map {P Q : RDCpx.{0}} {T : Atom}
    (c : atomToRDCpx.obj T ⟶ P) (f : P ⟶ Q) :
    suspCell c ≫ RDCpx.suspensionFunctor.map f = suspCell (c ≫ f) := by
  rw [suspCell, suspCell, Category.assoc, Functor.map_comp]

@[reassoc] theorem suspPole_comp_suspCell {P : RDCpx.{0}} {T : Atom}
    (c : atomToRDCpx.obj T ⟶ P) (α : Bool) :
    atomToRDCpx.map (suspPole T α) ≫ suspCell c = suspPoleRDC P α := by
  rw [suspCell, suspPole_comp_atomSuspensionRDCIso_hom_assoc,
    suspPoleRDC_comp_suspensionFunctor_map]

@[reassoc] theorem uliftYoneda_map_comp_realizeAtomIso_inv {U V : Atom} (g : U ⟶ V) :
    uliftYoneda.map g ≫ (realizeAtomIso.{u} V).inv =
      (realizeAtomIso U).inv ≫ realize.map (atomToRDCpx.map g) :=
  rfl

@[reassoc] theorem suspendedBallPoles_comp_realize_map_suspCell {P : RDCpx.{0}} {T : Atom}
    (c : atomToRDCpx.obj T ⟶ P) :
    suspendedBallPoles T ≫ (realizeAtomIso.{u} (atomSuspension.obj T)).inv ≫
      realize.map (suspCell c) = realizeSuspensionPoles P := by
  rw [suspendedBallPoles, coprod.desc_comp, realizeSuspensionPoles]
  congr 1 <;> rw [uliftYoneda_map_comp_realizeAtomIso_inv_assoc, ← Functor.map_comp,
    suspPole_comp_suspCell]

noncomputable def suspCellHom {P : RDCpx.{0}} {T : Atom} (c : atomToRDCpx.obj T ⟶ P) :
    suspendedBall.{u}.obj T ⟶ Under.mk (realizeSuspensionPoles.{u} P) :=
  Under.homMk ((realizeAtomIso (atomSuspension.obj T)).inv ≫ realize.map (suspCell c))
    (suspendedBallPoles_comp_realize_map_suspCell c)

@[simp] theorem suspCellHom_right {P : RDCpx.{0}} {T : Atom} (c : atomToRDCpx.obj T ⟶ P) :
    (suspCellHom.{u} c).right =
      (realizeAtomIso (atomSuspension.obj T)).inv ≫ realize.map (suspCell c) :=
  rfl

@[reassoc] theorem suspCellHom_comp {P : RDCpx.{0}} {T T' : Atom} (g : T' ⟶ T)
    (c : atomToRDCpx.obj T ⟶ P) :
    suspCellHom.{u} (atomToRDCpx.map g ≫ c) = suspendedBall.map g ≫ suspCellHom c := by
  ext1
  rw [suspCellHom_right, Under.comp_right, suspCellHom_right, suspCell_comp, Functor.map_comp]
  exact (uliftYoneda_map_comp_realizeAtomIso_inv_assoc _ _).symm

noncomputable def realizeToBipointedHom (P : RDCpx.{0}) :
    realize.{u}.obj P ⟶ bipointedHom.obj (Under.mk (realizeSuspensionPoles.{u} P)) where
  app T := ↾fun c => ⟨suspCellHom c.down⟩
  naturality T T' g := by
    ext ⟨c⟩
    exact congrArg ULift.up (suspCellHom_comp g.unop c)

theorem uliftYonedaEquiv_symm_realize {P : RDCpx.{0}} {T : Atom} (c : atomToRDCpx.obj T ⟶ P) :
    (uliftYonedaEquiv (X := T) (F := realize.{u}.obj P)).symm ⟨c⟩ =
      (realizeAtomIso T).inv ≫ realize.map c :=
  rfl

noncomputable def bipointedSuspensionRealizeHom (P : RDCpx.{0}) :
    bipointedSuspension.{u}.obj (realize.obj P) ⟶ Under.mk (realizeSuspensionPoles.{u} P) :=
  (bipointedSuspensionAdjunction.homEquiv _ _).symm (realizeToBipointedHom P)

@[reassoc] theorem bipointedSuspensionRealizeHom_cell {P : RDCpx.{0}} {T : Atom}
    (c : atomToRDCpx.obj T ⟶ P) :
    (bipointedSuspensionBallIso T).inv ≫
      bipointedSuspension.map ((realizeAtomIso T).inv ≫ realize.map c) ≫
        bipointedSuspensionRealizeHom.{u} P = suspCellHom c := by
  have h := Presheaf.uliftYonedaAdjunction_homEquiv_app.{0}
    (uliftYoneda.{u}.leftKanExtension suspendedBall.{u})
    (uliftYoneda.{u}.leftKanExtensionUnit suspendedBall.{u}) (bipointedSuspensionRealizeHom.{u} P)
    (Z := op T) ⟨c⟩
  have h' : ((Presheaf.uliftYonedaAdjunction (uliftYoneda.{u}.leftKanExtension suspendedBall.{u})
      (uliftYoneda.{u}.leftKanExtensionUnit suspendedBall.{u})).homEquiv _ _)
        (bipointedSuspensionRealizeHom.{u} P) = realizeToBipointedHom P :=
    (bipointedSuspensionAdjunction.{u}.homEquiv _ _).apply_symm_apply _
  rw [← uliftYonedaEquiv_symm_realize]
  exact (congrArg ULift.down ((congrArg (fun φ => φ.app (op T) ⟨c⟩) h').symm.trans h)).symm

theorem suspCell_apply {P : RDCpx.{0}} {T : Atom} (c : atomToRDCpx.obj T ⟶ P)
    (a : (atomSuspension.obj T).ogp) :
    ConcreteCategory.hom (suspCell c).hom a =
      suspMap (ConcreteCategory.hom c.hom) ((FiniteOGP.ofOGPIso (suspension T.ogp)).inv a) :=
  rfl

theorem injective_suspCell {P : RDCpx.{0}} {T : Atom} {c : atomToRDCpx.obj T ⟶ P}
    (hc : Function.Injective (ConcreteCategory.hom c.hom)) :
    Function.Injective (ConcreteCategory.hom (suspCell c).hom) :=
  (injective_suspMap hc).comp
    (IsInclusion.injective (f := (FiniteOGP.ofOGPIso (suspension T.ogp)).inv))

private noncomputable def pointPairIncl (α : Bool) : ball.{u} atomPoint ⟶ pointPair.{u} :=
  cond α coprod.inr coprod.inl

private theorem pointPairIncl_comp_suspendedBallPoles (U : Atom) (α : Bool) :
    pointPairIncl.{u} α ≫ suspendedBallPoles U = uliftYoneda.map (suspPole U α) := by
  cases α
  · exact coprod.inl_desc _ _
  · exact coprod.inr_desc _ _

private theorem pointPairIncl_comp_realizeSuspensionPoles (P : RDCpx.{0}) (α : Bool) :
    pointPairIncl.{u} α ≫ realizeSuspensionPoles P =
      (realizeAtomIso atomPoint).inv ≫ realize.map (suspPoleRDC P α) := by
  cases α
  · exact coprod.inl_desc _ _
  · exact coprod.inr_desc _ _

private abbrev sPole (P : RDCpx.{0}) (α : Bool) : (RDCpx.suspensionFunctor.obj P).obj.toOGP :=
  SuspCarrier.pole α

private abbrev sSusp {P : RDCpx.{0}} (x : P.obj.toOGP) :
    (RDCpx.suspensionFunctor.obj P).obj.toOGP :=
  SuspCarrier.susp x

section Inverse

variable (P : RDCpx.{0}) [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))]
  [DecidableLE P.obj.toOGP]
  [∀ w : (RDCpx.suspensionFunctor.obj P).obj.toOGP,
    FinEnum ((RDCpx.suspensionFunctor.obj P).obj.toOGP.restrict (.Iic w))]
  [DecidableLE (RDCpx.suspensionFunctor.obj P).obj.toOGP]

omit [∀ w : (RDCpx.suspensionFunctor.obj P).obj.toOGP,
    FinEnum ((RDCpx.suspensionFunctor.obj P).obj.toOGP.restrict (.Iic w))]
  [DecidableLE (RDCpx.suspensionFunctor.obj P).obj.toOGP] in
private theorem suspCell_principalInclusionRDC_mem (x : P.obj.toOGP)
    (a : (atomSuspension.obj (principalAtomRDC P x)).ogp) :
    ConcreteCategory.hom (suspCell (principalInclusionRDC P x)).hom a ∈
      LowerSet.Iic (sSusp x) := by
  rw [suspCell_apply]
  cases (FiniteOGP.ofOGPIso (suspension (principalAtomRDC P x).ogp)).inv a with
  | pole α => exact SuspCarrier.pole_le_susp α x
  | susp y => exact SuspCarrier.susp_le_susp.2 (principalInclusionRDC_mem_closure P x y)

private def suspPrincipalHom (x : P.obj.toOGP) :
    atomSuspension.obj (principalAtomRDC P x) ⟶
      principalAtomRDC (RDCpx.suspensionFunctor.obj P) (sSusp x) :=
  principalLiftRDC _ _ (suspCell (principalInclusionRDC P x))
    (suspCell_principalInclusionRDC_mem P x)

private theorem suspPrincipalHom_comp (x : P.obj.toOGP) :
    atomToRDCpx.map (suspPrincipalHom P x) ≫
      principalInclusionRDC (RDCpx.suspensionFunctor.obj P) (sSusp x) =
        suspCell (principalInclusionRDC P x) :=
  principalLiftRDC_comp_principalInclusionRDC _ _ _ _

private instance (x : P.obj.toOGP) : IsIso (suspPrincipalHom P x) := by
  have happ (a : (atomSuspension.obj (principalAtomRDC P x)).ogp) :
      ConcreteCategory.hom (principalInclusionRDC (RDCpx.suspensionFunctor.obj P)
        (sSusp x)).hom (suspPrincipalHom P x a) =
        ConcreteCategory.hom (suspCell (principalInclusionRDC P x)).hom a :=
    congrArg (fun g : atomToRDCpx.obj _ ⟶ _ => ConcreteCategory.hom g.hom a)
      (suspPrincipalHom_comp P x)
  refine isIso_of_bijective _ ⟨fun a b hab => ?_, fun b => ?_⟩
  · refine injective_suspCell (injective_principalInclusionRDC P x) ?_
    rw [← happ, ← happ, hab]
  · obtain ⟨a, ha⟩ : ∃ a, ConcreteCategory.hom (suspCell (principalInclusionRDC P x)).hom a =
        ConcreteCategory.hom (principalInclusionRDC (RDCpx.suspensionFunctor.obj P)
          (sSusp x)).hom b := by
      have hb := principalInclusionRDC_mem_closure _ _ b
      revert hb
      cases ConcreteCategory.hom (principalInclusionRDC (RDCpx.suspensionFunctor.obj P)
        (sSusp x)).hom b with
      | pole α =>
        intro _
        refine ⟨(FiniteOGP.ofOGPIso (suspension (principalAtomRDC P x).ogp)).hom
          (SuspCarrier.pole α), ?_⟩
        refine (suspCell_apply (principalInclusionRDC P x) _).trans ?_
        rw [Iso.hom_inv_id_apply, suspMap_pole]
      | susp y =>
        intro hy
        obtain ⟨a, ha⟩ := (image_principalInclusionRDC P x).ge
          (SuspCarrier.susp_le_susp.1 (LowerSet.mem_Iic_iff.1 hy))
        refine ⟨(FiniteOGP.ofOGPIso (suspension (principalAtomRDC P x).ogp)).hom
          (SuspCarrier.susp a), ?_⟩
        refine (suspCell_apply (principalInclusionRDC P x) _).trans ?_
        rw [Iso.hom_inv_id_apply, suspMap_susp, ha]
    exact ⟨a, injective_principalInclusionRDC _ _ ((happ a).trans ha)⟩

omit [∀ x : P.obj.toOGP, FinEnum (P.obj.toOGP.restrict (.Iic x))] [DecidableLE P.obj.toOGP] in
private theorem toAtomPoint_comp_suspPoleRDC (α : Bool) :
    atomToRDCpx.map (toAtomPoint _) ≫ suspPoleRDC P α =
      principalInclusionRDC (RDCpx.suspensionFunctor.obj P) (sPole P α) := by
  ext a
  have h := principalInclusionRDC_mem_closure (RDCpx.suspensionFunctor.obj P) (sPole P α) a
  revert h
  cases ConcreteCategory.hom
    (principalInclusionRDC (RDCpx.suspensionFunctor.obj P) (sPole P α)).hom a with
  | pole β =>
    exact fun h => congrArg (SuspCarrier.pole (X := P.obj.toOGP))
      ((SuspCarrier.pole_le_pole (X := P.obj.toOGP)).1 h).symm
  | susp y => exact fun h => absurd h (SuspCarrier.not_susp_le_pole y α)

omit [∀ w : (RDCpx.suspensionFunctor.obj P).obj.toOGP,
    FinEnum ((RDCpx.suspensionFunctor.obj P).obj.toOGP.restrict (.Iic w))]
  [DecidableLE (RDCpx.suspensionFunctor.obj P).obj.toOGP] in
private theorem hom_ext_suspCell {T : Atom} (x : P.obj.toOGP)
    {g g' : T ⟶ atomSuspension.obj (principalAtomRDC P x)}
    (h : atomToRDCpx.map g ≫ suspCell (principalInclusionRDC P x) =
      atomToRDCpx.map g' ≫ suspCell (principalInclusionRDC P x)) : g = g' :=
  Atom.hom_ext fun t => injective_suspCell (injective_principalInclusionRDC P x)
    (congrArg (fun f : atomToRDCpx.obj T ⟶ _ => ConcreteCategory.hom f.hom t) h)

private theorem inv_suspPrincipalHom_comp (x : P.obj.toOGP) :
    atomToRDCpx.map (inv (suspPrincipalHom P x)) ≫ suspCell (principalInclusionRDC P x) =
      principalInclusionRDC (RDCpx.suspensionFunctor.obj P) (sSusp x) := by
  rw [← suspPrincipalHom_comp, ← Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
    atomToRDCpx.map_id, Category.id_comp]

private noncomputable def inverseLeg :
    ∀ w : (RDCpx.suspensionFunctor.obj P).obj.toOGP,
      ball.{u} (principalAtomRDC (RDCpx.suspensionFunctor.obj P) w) ⟶
        (bipointedSuspension.obj (realize.obj P)).right
  | .pole α => uliftYoneda.map (toAtomPoint _) ≫ pointPairIncl α ≫
      (bipointedSuspension.obj (realize.obj P)).hom
  | .susp x => uliftYoneda.map (inv (suspPrincipalHom P x)) ≫
      ((bipointedSuspensionBallIso (principalAtomRDC P x)).inv ≫
        bipointedSuspension.map ((realizeCocone P).ι.app x)).right

private theorem inverseLeg_pole (α : Bool) :
    inverseLeg.{u} P (sPole P α) = uliftYoneda.map (toAtomPoint _) ≫ pointPairIncl α ≫
      (bipointedSuspension.obj (realize.obj P)).hom :=
  rfl

private theorem inverseLeg_susp (x : P.obj.toOGP) :
    inverseLeg.{u} P (sSusp x) = uliftYoneda.map (inv (suspPrincipalHom P x)) ≫
      ((bipointedSuspensionBallIso (principalAtomRDC P x)).inv ≫
        bipointedSuspension.map ((realizeCocone P).ι.app x)).right :=
  rfl

private theorem inverseLeg_naturality_pole_pole {α β : Bool} (h : sPole P α ≤ sPole P β) :
    uliftYoneda.map (principalMapRDC (RDCpx.suspensionFunctor.obj P) h) ≫
      inverseLeg.{u} P (sPole P β) = inverseLeg P (sPole P α) := by
  obtain rfl : α = β := SuspCarrier.pole_le_pole.1 h
  rw [inverseLeg_pole, ← Functor.map_comp_assoc,
    Subsingleton.elim (_ ≫ toAtomPoint _) (toAtomPoint _)]

private theorem inverseLeg_naturality_pole_susp {α : Bool} {y : P.obj.toOGP}
    (h : sPole P α ≤ sSusp y) :
    uliftYoneda.map (principalMapRDC (RDCpx.suspensionFunctor.obj P) h) ≫
      inverseLeg.{u} P (sSusp y) = inverseLeg P (sPole P α) := by
  have e : principalMapRDC (RDCpx.suspensionFunctor.obj P) h ≫ inv (suspPrincipalHom P y) =
      toAtomPoint _ ≫ suspPole (principalAtomRDC P y) α :=
    hom_ext_suspCell P y (by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        inv_suspPrincipalHom_comp, principalMapRDC_comp_principalInclusionRDC,
        suspPole_comp_suspCell, toAtomPoint_comp_suspPoleRDC])
  rw [inverseLeg_pole, inverseLeg_susp]
  exact (Functor.map_comp_assoc _ _ _ _).symm.trans
    ((congrArg (fun g => uliftYoneda.map g ≫ _) e).trans
      ((Functor.map_comp_assoc _ _ _ _).trans (congrArg (uliftYoneda.map _ ≫ ·)
        ((congrArg (· ≫ _) (pointPairIncl_comp_suspendedBallPoles _ α).symm).trans
          ((Category.assoc _ _ _).trans (congrArg (pointPairIncl α ≫ ·)
            (Under.w ((bipointedSuspensionBallIso (principalAtomRDC P y)).inv ≫
              bipointedSuspension.map ((realizeCocone P).ι.app y)))))))))

private theorem inverseLeg_naturality_susp_susp {x y : P.obj.toOGP} (h : sSusp x ≤ sSusp y) :
    uliftYoneda.map (principalMapRDC (RDCpx.suspensionFunctor.obj P) h) ≫
      inverseLeg.{u} P (sSusp y) = inverseLeg P (sSusp x) := by
  have hxy : x ≤ y := SuspCarrier.susp_le_susp.1 h
  have e : principalMapRDC (RDCpx.suspensionFunctor.obj P) h ≫ inv (suspPrincipalHom P y) =
      inv (suspPrincipalHom P x) ≫ atomSuspension.map (principalMapRDC P hxy) :=
    hom_ext_suspCell P y (by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        inv_suspPrincipalHom_comp, principalMapRDC_comp_principalInclusionRDC,
        ← suspCell_comp, principalMapRDC_comp_principalInclusionRDC,
        inv_suspPrincipalHom_comp])
  have e' : suspendedBall.map (principalMapRDC P hxy) ≫
      (bipointedSuspensionBallIso.{u} (principalAtomRDC P y)).inv ≫
        bipointedSuspension.map ((realizeCocone P).ι.app y) =
      (bipointedSuspensionBallIso (principalAtomRDC P x)).inv ≫
        bipointedSuspension.map ((realizeCocone P).ι.app x) := by
    rw [bipointedSuspensionBallIso_inv_naturality_assoc]
    exact congrArg (_ ≫ ·) ((bipointedSuspension.map_comp _ _).symm.trans
      (congrArg bipointedSuspension.map ((realizeCocone P).w (homOfLE hxy))))
  rw [inverseLeg_susp, inverseLeg_susp]
  exact (Functor.map_comp_assoc _ _ _ _).symm.trans
    ((congrArg (fun g => uliftYoneda.map g ≫ _) e).trans
      ((Functor.map_comp_assoc _ _ _ _).trans
        (congrArg (uliftYoneda.map (inv (suspPrincipalHom P x)) ≫ ·)
          (congrArg Under.Hom.right e'))))

private theorem inverseLeg_naturality {w w' : (RDCpx.suspensionFunctor.obj P).obj.toOGP}
    (h : w ≤ w') :
    uliftYoneda.map (principalMapRDC (RDCpx.suspensionFunctor.obj P) h) ≫
      inverseLeg.{u} P w' = inverseLeg P w := by
  cases w with
  | pole α =>
    cases w' with
    | pole β => exact inverseLeg_naturality_pole_pole P h
    | susp y => exact inverseLeg_naturality_pole_susp P h
  | susp x =>
    cases w' with
    | pole β => exact absurd h (SuspCarrier.not_susp_le_pole x β)
    | susp y => exact inverseLeg_naturality_susp_susp P h

private noncomputable def inverseCocone :
    Cocone (principalDiagramRDC (RDCpx.suspensionFunctor.obj P) ⋙ uliftYoneda.{u}) where
  pt := (bipointedSuspension.obj (realize.obj P)).right
  ι :=
    { app := inverseLeg P
      naturality := fun _ _ f => (inverseLeg_naturality P (leOfHom f)).trans
        (Category.comp_id _).symm }

private noncomputable def inverseMap :
    realize.obj (RDCpx.suspensionFunctor.obj P) ⟶ (bipointedSuspension.obj (realize.obj P)).right :=
  (isColimitRealizeCocone (RDCpx.suspensionFunctor.obj P)).desc (inverseCocone P)

private theorem realize_map_comp_inverseMap {T : Atom}
    {w : (RDCpx.suspensionFunctor.obj P).obj.toOGP}
    (g : T ⟶ principalAtomRDC (RDCpx.suspensionFunctor.obj P) w) :
    (realizeAtomIso.{u} T).inv ≫ realize.map (atomToRDCpx.map g ≫
      principalInclusionRDC (RDCpx.suspensionFunctor.obj P) w) ≫ inverseMap P =
        uliftYoneda.map g ≫ inverseLeg P w := by
  simp only [Functor.map_comp, Category.assoc]
  exact (uliftYoneda_map_comp_realizeAtomIso_inv_assoc g _).symm.trans
    (congrArg (uliftYoneda.map g ≫ ·) ((Category.assoc _ _ _).symm.trans
      ((isColimitRealizeCocone (RDCpx.suspensionFunctor.obj P)).fac (inverseCocone P) w)))

private theorem realizeSuspensionPoles_comp_inverseMap :
    realizeSuspensionPoles.{u} P ≫ inverseMap P =
      (bipointedSuspension.obj (realize.obj P)).hom := by
  have key (α : Bool) : pointPairIncl.{u} α ≫ realizeSuspensionPoles P ≫ inverseMap P =
      pointPairIncl α ≫ (bipointedSuspension.obj (realize.obj P)).hom := by
    have hg := principalLiftRDC_comp_principalInclusionRDC (RDCpx.suspensionFunctor.obj P)
      (sPole P α) (suspPoleRDC P α) (fun _ => LowerSet.mem_Iic_iff.2 le_rfl)
    rw [← Category.assoc, pointPairIncl_comp_realizeSuspensionPoles, Category.assoc, ← hg,
      realize_map_comp_inverseMap, inverseLeg, ← Category.assoc, ← Functor.map_comp,
      Subsingleton.elim (_ ≫ toAtomPoint _) (𝟙 _), CategoryTheory.Functor.map_id, Category.id_comp]
  exact coprod.hom_ext (key false) (key true)

private noncomputable def inverseHom :
    Under.mk (realizeSuspensionPoles.{u} P) ⟶ bipointedSuspension.obj (realize.obj P) :=
  Under.homMk (inverseMap P) (realizeSuspensionPoles_comp_inverseMap P)

private theorem bipointedSuspensionRealizeHom_comp_inverseHom :
    bipointedSuspensionRealizeHom.{u} P ≫ inverseHom P = 𝟙 _ := by
  have : PreservesColimitsOfSize.{0, 0} bipointedSuspension.{u} :=
    bipointedSuspensionAdjunction.leftAdjoint_preservesColimits
  refine (isColimitOfPreserves bipointedSuspension.{u}
    (isColimitRealizeCocone P)).hom_ext fun x => ?_
  refine (cancel_epi (bipointedSuspensionBallIso.{u} (principalAtomRDC P x)).inv).1 ?_
  have h : ((realizeAtomIso.{u} (atomSuspension.obj (principalAtomRDC P x))).inv ≫
      realize.map (suspCell (principalInclusionRDC P x))) ≫ inverseMap P =
      ((bipointedSuspensionBallIso.{u} (principalAtomRDC P x)).inv ≫
        bipointedSuspension.map ((realizeCocone P).ι.app x)).right := by
    rw [Category.assoc, ← suspPrincipalHom_comp, realize_map_comp_inverseMap, inverseLeg_susp]
    exact (Functor.map_comp_assoc _ _ _ _).symm.trans
      ((congrArg (fun g => uliftYoneda.map g ≫ _) (IsIso.hom_inv_id _)).trans
        ((congrArg (· ≫ _) (uliftYoneda.map_id _)).trans (Category.id_comp _)))
  exact (bipointedSuspensionRealizeHom_cell_assoc (principalInclusionRDC P x)
    (inverseHom P)).trans ((Under.UnderMorphism.ext h).trans
      (congrArg (_ ≫ ·)
        (Category.comp_id (bipointedSuspension.map ((realizeCocone P).ι.app x))).symm))

private theorem inverseLeg_pole_comp (α : Bool) :
    inverseLeg.{u} P (sPole P α) ≫ (bipointedSuspensionRealizeHom P).right =
      (realizeAtomIso _).inv ≫
        realize.map (principalInclusionRDC (RDCpx.suspensionFunctor.obj P) (sPole P α)) := by
  have h1 : pointPairIncl α ≫ (bipointedSuspension.obj (realize.obj P)).hom ≫
      (bipointedSuspensionRealizeHom.{u} P).right =
        (realizeAtomIso atomPoint).inv ≫ realize.map (suspPoleRDC P α) :=
    (congrArg (pointPairIncl α ≫ ·) (Under.w _)).trans
      (pointPairIncl_comp_realizeSuspensionPoles P α)
  have h2 : uliftYoneda.map (toAtomPoint _) ≫ (realizeAtomIso.{u} atomPoint).inv ≫
      realize.map (suspPoleRDC P α) = (realizeAtomIso _).inv ≫
        realize.map (principalInclusionRDC (RDCpx.suspensionFunctor.obj P) (sPole P α)) := by
    rw [uliftYoneda_map_comp_realizeAtomIso_inv_assoc, ← Functor.map_comp,
      toAtomPoint_comp_suspPoleRDC]
  exact (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans h1)).trans h2)

private theorem inverseLeg_susp_comp (x : P.obj.toOGP) :
    inverseLeg.{u} P (sSusp x) ≫ (bipointedSuspensionRealizeHom P).right =
      (realizeAtomIso _).inv ≫
        realize.map (principalInclusionRDC (RDCpx.suspensionFunctor.obj P) (sSusp x)) := by
  have h1 := congrArg Under.Hom.right ((Category.assoc _ _ _).trans
    (bipointedSuspensionRealizeHom_cell.{u} (principalInclusionRDC P x)))
  have h2 : uliftYoneda.map (inv (suspPrincipalHom P x)) ≫
      (realizeAtomIso.{u} (atomSuspension.obj (principalAtomRDC P x))).inv ≫
        realize.map (suspCell (principalInclusionRDC P x)) = (realizeAtomIso _).inv ≫
          realize.map (principalInclusionRDC (RDCpx.suspensionFunctor.obj P) (sSusp x)) := by
    rw [uliftYoneda_map_comp_realizeAtomIso_inv_assoc, ← Functor.map_comp,
      inv_suspPrincipalHom_comp]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1).trans h2)

private theorem inverseHom_comp_bipointedSuspensionRealizeHom :
    inverseHom P ≫ bipointedSuspensionRealizeHom.{u} P = 𝟙 _ := by
  ext1
  refine (isColimitRealizeCocone (RDCpx.suspensionFunctor.obj P)).hom_ext fun w => ?_
  refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.comp_id _).symm)
  refine (congrArg (· ≫ _) ((isColimitRealizeCocone _).fac (inverseCocone P) w)).trans ?_
  cases w with
  | pole α => exact inverseLeg_pole_comp P α
  | susp x => exact inverseLeg_susp_comp P x

end Inverse

instance (P : RDCpx.{0}) : IsIso (bipointedSuspensionRealizeHom.{u} P) := by
  classical
  let (Q : RDCpx.{0}) (y : Q.obj.toOGP) : FinEnum (Q.obj.toOGP.restrict (.Iic y)) :=
    have : Fintype (Q.obj.toOGP.restrict (.Iic y)) := (IsMoleculeIn.finite (Q.obj.isRDC y)).fintype
    FinEnum.ofEquiv _ (Fintype.equivFin _)
  exact ⟨inverseHom P, bipointedSuspensionRealizeHom_comp_inverseHom P,
    inverseHom_comp_bipointedSuspensionRealizeHom P⟩

noncomputable def bipointedSuspensionRealizeIso (P : RDCpx.{0}) :
    bipointedSuspension.{u}.obj (realize.obj P) ≅ Under.mk (realizeSuspensionPoles.{u} P) :=
  asIso (bipointedSuspensionRealizeHom P)

@[simp] theorem bipointedSuspensionRealizeIso_hom (P : RDCpx.{0}) :
    (bipointedSuspensionRealizeIso.{u} P).hom = bipointedSuspensionRealizeHom P :=
  rfl

theorem bipointedSuspensionRealizeIso_cell {P : RDCpx.{0}} {T : Atom}
    (c : atomToRDCpx.obj T ⟶ P) :
    (bipointedSuspensionBallIso T).inv ≫
      bipointedSuspension.map ((realizeAtomIso T).inv ≫ realize.map c) ≫
        (bipointedSuspensionRealizeIso.{u} P).hom = suspCellHom c :=
  bipointedSuspensionRealizeHom_cell c

theorem suspCellHom_comp_homMk {P Q : RDCpx.{0}} {T : Atom} (c : atomToRDCpx.obj T ⟶ P)
    (f : P ⟶ Q) :
    suspCellHom.{u} c ≫ Under.homMk (V := Under.mk (realizeSuspensionPoles Q))
      (realize.map (RDCpx.suspensionFunctor.map f)) (realizeSuspensionPoles_comp f) =
        suspCellHom (c ≫ f) := by
  ext1
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Functor.map_comp _ _ _).symm.trans
    (congrArg realize.map (suspCell_comp_suspensionFunctor_map c f))))

@[reassoc] theorem bipointedSuspensionRealizeIso_hom_naturality {P Q : RDCpx.{0}} (f : P ⟶ Q) :
    bipointedSuspension.map (realize.map f) ≫ (bipointedSuspensionRealizeIso.{u} Q).hom =
      (bipointedSuspensionRealizeIso P).hom ≫
        Under.homMk (V := Under.mk (realizeSuspensionPoles Q))
          (realize.map (RDCpx.suspensionFunctor.map f)) (realizeSuspensionPoles_comp f) := by
  have h (R : RDCpx.{0}) : (bipointedSuspensionAdjunction.homEquiv _ _)
      (bipointedSuspensionRealizeIso.{u} R).hom = realizeToBipointedHom R :=
    (bipointedSuspensionAdjunction.homEquiv _ _).apply_symm_apply _
  refine (bipointedSuspensionAdjunction.homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, h, h]
  ext ⟨T⟩ ⟨c⟩
  exact congrArg ULift.up (suspCellHom_comp_homMk c f).symm

theorem suspCell_id (U : Atom) :
    suspCell (𝟙 (atomToRDCpx.obj U)) = (atomSuspensionRDCIso U).hom := by
  rw [suspCell, CategoryTheory.Functor.map_id, Category.comp_id]

noncomputable def realizeSuspensionAtomIso (U : Atom) :
    realize.{u}.obj (RDCpx.suspensionFunctor.obj (atomToRDCpx.obj U)) ≅
      ball (atomSuspension.obj U) :=
  realize.mapIso (atomSuspensionRDCIso U).symm ≪≫ realizeAtomIso (atomSuspension.obj U)

@[reassoc] theorem realizeSuspensionPoles_comp_realizeSuspensionAtomIso_hom (U : Atom) :
    realizeSuspensionPoles (atomToRDCpx.obj U) ≫ (realizeSuspensionAtomIso.{u} U).hom =
      suspendedBallPoles U := by
  rw [← suspendedBallPoles_comp_realize_map_suspCell (𝟙 _), suspCell_id, realizeSuspensionAtomIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc, Category.assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id]

theorem bipointedSuspension_map_realizeAtomIso_hom (U : Atom) :
    bipointedSuspension.map (realizeAtomIso.{u} U).hom ≫ (bipointedSuspensionBallIso U).hom =
      (bipointedSuspensionRealizeIso (atomToRDCpx.obj U)).hom ≫
        Under.homMk (V := suspendedBall.obj U) (realizeSuspensionAtomIso U).hom
          (realizeSuspensionPoles_comp_realizeSuspensionAtomIso_hom U) := by
  have h : (realizeAtomIso.{u} (atomSuspension.obj U)).inv ≫ realize.map (suspCell (𝟙 _)) ≫
      (realizeSuspensionAtomIso U).hom = 𝟙 _ := by
    rw [suspCell_id, realizeSuspensionAtomIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id]
  have hc := bipointedSuspensionRealizeIso_cell.{u} (𝟙 (atomToRDCpx.obj U))
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  refine (cancel_epi (bipointedSuspension.map (realizeAtomIso.{u} U).inv)).1 ?_
  refine (cancel_epi (bipointedSuspensionBallIso.{u} U).inv).1 ?_
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id, reassoc_of% hc]
  ext1
  exact ((Category.assoc _ _ _).trans h).symm

section Sphere

variable (U : Atom)

private def suspAddr : suspension U.ogp ≅ (atomSuspension.obj U).ogp :=
  FiniteOGP.ofOGPIso _

private theorem ofOGPIso_hom_mem_bdryFull_iff (z : suspension U.ogp) :
    (suspAddr U).hom z ∈ (atomSuspension.obj U).ogp.bdryFull ⊤ ↔
      z ∈ (U.ogp.bdryFull ⊤).susp := by
  have hb : (suspension U.ogp).bdryFull ⊤ = (U.ogp.bdryFull ⊤).susp := by
    rw [← bdryFull_susp U.isMolecule, susp_top]
  rw [← map_top_of_isIso (suspAddr U).hom, ← map_bdryFull, mem_map, hb]
  exact ⟨fun ⟨x, hx, h⟩ => IsInclusion.injective (f := (suspAddr U).hom) h ▸ hx,
    fun h => ⟨z, h, rfl⟩⟩

private def suspBoundaryHom :
    suspension (U.ogp.restrict (U.ogp.bdryFull ⊤)) ⟶
      (atomSuspension.obj U).ogp.restrict ((atomSuspension.obj U).ogp.bdryFull ⊤) :=
  codRestrict (suspension.map (incl _) ≫ (suspAddr U).hom) _ fun w =>
    (ofOGPIso_hom_mem_bdryFull_iff U _).2 (by
      cases w with
      | pole α => exact pole_mem_susp _ α
      | susp x => exact susp_mem_susp.2 x.2)

private theorem isIso_suspBoundaryHom : IsIso (suspBoundaryHom U) := by
  refine (OGP.isIso_iff_bijective _).2 ⟨fun a b h => ?_, fun y => ?_⟩
  · exact injective_suspMap Subtype.val_injective
      (IsInclusion.injective (f := (suspAddr U).hom)
        (congrArg Subtype.val h))
  · obtain ⟨y, hy⟩ := y
    obtain ⟨z, rfl⟩ := (orderIsoOfIso (suspAddr U)).surjective y
    have hz := (ofOGPIso_hom_mem_bdryFull_iff U z).1 hy
    cases z with
    | pole α => exact ⟨SuspCarrier.pole α, rfl⟩
    | susp x => exact ⟨SuspCarrier.susp ⟨x, susp_mem_susp.1 hz⟩, rfl⟩

private noncomputable def suspBoundaryIso :
    RDCpx.suspensionFunctor.obj ((atomToRDCpx.obj U).restrict (U.ogp.bdryFull ⊤)) ≅
      (atomToRDCpx.obj (atomSuspension.obj U)).restrict ((atomSuspension.obj U).ogp.bdryFull ⊤) :=
  RDCpx.isoOfIso (P := RDCpx.suspensionFunctor.obj _) (Q := RDCpx.restrict _ _)
    (@asIso _ _ _ _ (suspBoundaryHom U) (isIso_suspBoundaryHom U))

private theorem suspBoundaryIso_hom_comp :
    (suspBoundaryIso U).hom ≫ RDCpx.restrictIncl _ _ =
      RDCpx.suspensionFunctor.map ((atomToRDCpx.obj U).restrictIncl (U.ogp.bdryFull ⊤)) ≫
        (atomSuspensionRDCIso U).inv := by
  ext w
  rfl

private noncomputable def realizeSuspensionSphereIso :
    realize.{u}.obj (RDCpx.suspensionFunctor.obj ((atomToRDCpx.obj U).restrict (U.ogp.bdryFull ⊤)))
      ≅ sphere (atomSuspension.obj U) :=
  realize.mapIso (suspBoundaryIso U) ≪≫ (sphereRealizeIso (atomSuspension.obj U)).symm

private theorem realizeSuspensionSphereIso_hom_comp :
    (realizeSuspensionSphereIso.{u} U).hom ≫ sphereInclusion (atomSuspension.obj U) =
      realize.map (RDCpx.suspensionFunctor.map
        ((atomToRDCpx.obj U).restrictIncl (U.ogp.bdryFull ⊤))) ≫
          (realizeSuspensionAtomIso U).hom := by
  rw [realizeSuspensionSphereIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    sphereRealizeIso_inv_comp, ← Functor.map_comp_assoc, suspBoundaryIso_hom_comp,
    Functor.map_comp_assoc, realizeSuspensionAtomIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom]

end Sphere

noncomputable def sphereSuspensionPoles (U : Atom) :
    pointPair.{u} ⟶ sphere (atomSuspension.obj U) :=
  realizeSuspensionPoles _ ≫ (realizeSuspensionSphereIso U).hom

@[reassoc (attr := simp)] theorem sphereSuspensionPoles_comp (U : Atom) :
    sphereSuspensionPoles.{u} U ≫ sphereInclusion (atomSuspension.obj U) =
      suspendedBallPoles U := by
  rw [sphereSuspensionPoles, Category.assoc, realizeSuspensionSphereIso_hom_comp,
    realizeSuspensionPoles_comp_assoc, realizeSuspensionPoles_comp_realizeSuspensionAtomIso_hom]

noncomputable def bipointedSuspensionSphereIso (U : Atom) :
    bipointedSuspension.{u}.obj (sphere U) ≅ Under.mk (sphereSuspensionPoles.{u} U) :=
  bipointedSuspension.mapIso (sphereRealizeIso U) ≪≫ bipointedSuspensionRealizeIso _ ≪≫
    Under.isoMk (realizeSuspensionSphereIso U) rfl

theorem bipointedSuspension_map_sphereInclusion (U : Atom) :
    bipointedSuspension.map (sphereInclusion U) ≫ (bipointedSuspensionBallIso.{u} U).hom =
      (bipointedSuspensionSphereIso U).hom ≫
        Under.homMk (V := suspendedBall.obj U) (sphereInclusion (atomSuspension.obj U))
          (sphereSuspensionPoles_comp U) := by
  have hs : sphereInclusion.{u} U = (sphereRealizeIso U).hom ≫
      realize.map ((atomToRDCpx.obj U).restrictIncl (U.ogp.bdryFull ⊤)) ≫
        (realizeAtomIso U).hom := by
    rw [sphereRealizeIso_hom_comp_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hs, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    bipointedSuspension_map_realizeAtomIso_hom, bipointedSuspensionRealizeIso_hom_naturality_assoc,
    bipointedSuspensionSphereIso, Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, Category.assoc]
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
  ext1
  exact (realizeSuspensionSphereIso_hom_comp U).symm

section ClosedSubset

variable (U : Atom) (S : LowerSet U.ogp) (T : LowerSet (atomSuspension.obj U).ogp)
  (hST : ∀ z, (FiniteOGP.ofOGPIso (suspension U.ogp)).hom z ∈ T ↔ z ∈ S.susp)

private def suspSubsetHom :
    suspension (U.ogp.restrict S) ⟶ (atomSuspension.obj U).ogp.restrict T :=
  codRestrict (suspension.map (incl _) ≫ (FiniteOGP.ofOGPIso (suspension U.ogp)).hom) _ fun w =>
    (hST _).2 (by
      cases w with
      | pole α => exact pole_mem_susp _ α
      | susp x => exact susp_mem_susp.2 x.2)

private theorem isIso_suspSubsetHom :
    IsIso (suspSubsetHom U S T hST) := by
  refine (OGP.isIso_iff_bijective _).2 ⟨fun a b h => ?_, fun y => ?_⟩
  · exact injective_suspMap Subtype.val_injective
      (IsInclusion.injective (f := (FiniteOGP.ofOGPIso (suspension U.ogp)).hom)
        (congrArg Subtype.val h))
  · obtain ⟨y, hy⟩ := y
    obtain ⟨z, rfl⟩ := (orderIsoOfIso (FiniteOGP.ofOGPIso (suspension U.ogp))).surjective y
    have hz := (hST z).1 hy
    cases z with
    | pole α => exact ⟨SuspCarrier.pole α, rfl⟩
    | susp x => exact ⟨SuspCarrier.susp ⟨x, susp_mem_susp.1 hz⟩, rfl⟩

private noncomputable def suspSubsetIso :
    RDCpx.suspensionFunctor.obj ((atomToRDCpx.obj U).restrict S) ≅
      (atomToRDCpx.obj (atomSuspension.obj U)).restrict T :=
  RDCpx.isoOfIso (P := RDCpx.suspensionFunctor.obj _) (Q := RDCpx.restrict _ _)
    (@asIso _ _ _ _ (suspSubsetHom U S T hST) (isIso_suspSubsetHom U S T hST))

private theorem suspSubsetIso_hom_comp :
    (suspSubsetIso U S T hST).hom ≫ RDCpx.restrictIncl _ _ =
      RDCpx.suspensionFunctor.map ((atomToRDCpx.obj U).restrictIncl S) ≫
        (atomSuspensionRDCIso U).inv := by
  ext w
  rfl

private noncomputable def realizeSuspensionSubsetIso :
    realize.{u}.obj (RDCpx.suspensionFunctor.obj ((atomToRDCpx.obj U).restrict S)) ≅
      (closedSubpresheaf (atomSuspension.obj U) T).toFunctor :=
  realize.mapIso (suspSubsetIso U S T hST) ≪≫
    realizeRestrictIso (atomToRDCpx.obj (atomSuspension.obj U)) T _ rfl ≪≫
    realizeSubsetAtomIso _ T

private theorem realizeSuspensionSubsetIso_hom_comp :
    (realizeSuspensionSubsetIso.{u} U S T hST).hom ≫ (closedSubpresheaf _ T).ι =
      realize.map (RDCpx.suspensionFunctor.map ((atomToRDCpx.obj U).restrictIncl S)) ≫
          (realizeSuspensionAtomIso U).hom := by
  have h : (realizeRestrictIso.{u} (atomToRDCpx.obj (atomSuspension.obj U)) T _ rfl ≪≫
      realizeSubsetAtomIso _ T).hom ≫
      (closedSubpresheaf (atomSuspension.obj U) T).ι =
        realize.map (RDCpx.restrictIncl _ T) ≫ (realizeAtomIso _).hom :=
    rfl
  rw [realizeSuspensionSubsetIso, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, h, ← Functor.map_comp_assoc, suspSubsetIso_hom_comp, Functor.map_comp_assoc,
    realizeSuspensionAtomIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]

private noncomputable def subsetRealizeIso :
    (closedSubpresheaf.{u} U S).toFunctor ≅ realize.obj ((atomToRDCpx.obj U).restrict S) :=
  (realizeSubsetAtomIso U S).symm ≪≫ (realizeRestrictIso _ _ _ rfl).symm

@[reassoc] private theorem subsetRealizeIso_hom_comp :
    (subsetRealizeIso.{u} U S).hom ≫ realize.map ((atomToRDCpx.obj U).restrictIncl S) =
      (closedSubpresheaf U S).ι ≫ (realizeAtomIso U).inv :=
  rfl

noncomputable def closedSubpresheafSuspensionPoles :
    pointPair.{u} ⟶ (closedSubpresheaf (atomSuspension.obj U) T).toFunctor :=
  realizeSuspensionPoles _ ≫ (realizeSuspensionSubsetIso U S T hST).hom

@[reassoc (attr := simp)] theorem closedSubpresheafSuspensionPoles_comp :
    closedSubpresheafSuspensionPoles.{u} U S T hST ≫ (closedSubpresheaf _ T).ι =
      suspendedBallPoles U := by
  rw [closedSubpresheafSuspensionPoles, Category.assoc, realizeSuspensionSubsetIso_hom_comp,
    realizeSuspensionPoles_comp_assoc, realizeSuspensionPoles_comp_realizeSuspensionAtomIso_hom]

noncomputable def bipointedSuspensionClosedSubpresheafIso :
    bipointedSuspension.{u}.obj (closedSubpresheaf U S).toFunctor ≅
      Under.mk (closedSubpresheafSuspensionPoles.{u} U S T hST) :=
  bipointedSuspension.mapIso (subsetRealizeIso U S) ≪≫ bipointedSuspensionRealizeIso _ ≪≫
    Under.isoMk (realizeSuspensionSubsetIso U S T hST) rfl

theorem bipointedSuspension_map_closedSubpresheaf_ι :
    bipointedSuspension.map (closedSubpresheaf U S).ι ≫ (bipointedSuspensionBallIso.{u} U).hom =
      (bipointedSuspensionClosedSubpresheafIso U S T hST).hom ≫
        Under.homMk (V := suspendedBall.obj U) (closedSubpresheaf (atomSuspension.obj U) T).ι
          (closedSubpresheafSuspensionPoles_comp U S T hST) := by
  have hs : (closedSubpresheaf.{u} U S).ι = (subsetRealizeIso U S).hom ≫
      realize.map ((atomToRDCpx.obj U).restrictIncl S) ≫ (realizeAtomIso U).hom := by
    rw [subsetRealizeIso_hom_comp_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hs, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    bipointedSuspension_map_realizeAtomIso_hom, bipointedSuspensionRealizeIso_hom_naturality_assoc,
    bipointedSuspensionClosedSubpresheafIso, Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, Category.assoc]
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
  ext1
  exact (realizeSuspensionSubsetIso_hom_comp U S T hST).symm

end ClosedSubset

namespace PastingDiagram

variable {p : Under pointPair.{u}}

noncomputable def suspensionHom (w : PastingDiagram (bipointedHom.obj p)) :
    Under.mk (realizeSuspensionPoles.{u} w.shape.rdc) ⟶ p :=
  (bipointedSuspensionRealizeIso w.shape.rdc).inv ≫
    (bipointedSuspensionAdjunction.homEquiv _ _).symm w.map

noncomputable def suspension (w : PastingDiagram (bipointedHom.obj p)) : PastingDiagram p.right :=
  ⟨w.shape.suspension, realize.map w.shape.suspensionRDCIso.inv ≫ w.suspensionHom.right⟩

theorem suspension_map (w : PastingDiagram (bipointedHom.obj p)) :
    w.suspension.map = realize.map w.shape.suspensionRDCIso.inv ≫ w.suspensionHom.right :=
  rfl

theorem dim_suspension (w : PastingDiagram (bipointedHom.obj p)) :
    w.suspension.dim = w.dim + 1 :=
  w.shape.dimension_suspension

theorem IsRound.suspension {w : PastingDiagram (bipointedHom.obj p)} (h : w.IsRound) :
    w.suspension.IsRound :=
  MoleculeShape.isRound_suspension h

theorem realizeSuspensionPoles_comp_suspension_map (w : PastingDiagram (bipointedHom.obj p)) :
    realizeSuspensionPoles w.shape.rdc ≫ realize.map w.shape.suspensionRDCIso.hom ≫
      w.suspension.map = p.hom := by
  rw [suspension_map, ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact Under.w w.suspensionHom

theorem realize_map_suspensionMap_comp_suspension_map {w v : PastingDiagram (bipointedHom.obj p)}
    (j : v.shape.ogp ⟶ w.shape.ogp) [IsInclusion j]
    (hj : realize.map (RDCpx.ofInclusion (P := v.shape.rdc) (Q := w.shape.rdc) j) ≫ w.map = v.map) :
    realize.map (RDCpx.ofInclusion (P := v.shape.suspension.rdc) (Q := w.shape.suspension.rdc)
      (MoleculeShape.suspensionMap j)) ≫ w.suspension.map = v.suspension.map := by
  have hn' : Under.homMk (V := Under.mk (realizeSuspensionPoles.{u} w.shape.rdc))
      (realize.map (RDCpx.suspensionFunctor.map
        (RDCpx.ofInclusion (P := v.shape.rdc) (Q := w.shape.rdc) j)))
      (realizeSuspensionPoles_comp _) ≫ (bipointedSuspensionRealizeIso w.shape.rdc).inv =
        (bipointedSuspensionRealizeIso v.shape.rdc).inv ≫ bipointedSuspension.map
          (realize.map (RDCpx.ofInclusion (P := v.shape.rdc) (Q := w.shape.rdc) j)) := by
    rw [Iso.comp_inv_eq, Category.assoc, bipointedSuspensionRealizeIso_hom_naturality,
      Iso.inv_hom_id_assoc]
  have key : Under.homMk (V := Under.mk (realizeSuspensionPoles.{u} w.shape.rdc))
      (realize.map (RDCpx.suspensionFunctor.map
        (RDCpx.ofInclusion (P := v.shape.rdc) (Q := w.shape.rdc) j)))
      (realizeSuspensionPoles_comp _) ≫ w.suspensionHom = v.suspensionHom := by
    rw [suspensionHom, suspensionHom, reassoc_of% hn',
      ← Adjunction.homEquiv_naturality_left_symm, hj]
  have hr : RDCpx.ofInclusion (P := v.shape.suspension.rdc) (Q := w.shape.suspension.rdc)
      (MoleculeShape.suspensionMap j) ≫ w.shape.suspensionRDCIso.inv =
        v.shape.suspensionRDCIso.inv ≫ RDCpx.suspensionFunctor.map
          (RDCpx.ofInclusion (P := v.shape.rdc) (Q := w.shape.rdc) j) := by
    ext y
    exact ConcreteCategory.congr_hom w.shape.suspensionIso.hom_inv_id _
  exact (Functor.map_comp_assoc _ _ _ _).symm.trans
    ((congrArg (fun g => realize.map g ≫ _) hr).trans ((Functor.map_comp_assoc _ _ _ _).trans
      (congrArg (_ ≫ ·) (congrArg Under.Hom.right key))))

theorem Equiv.suspension {w v : PastingDiagram (bipointedHom.obj p)} (h : w.Equiv v) :
    w.suspension.Equiv v.suspension := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨w.shape.suspensionIso.symm ≪≫ OGP.suspension.mapIso φ ≪≫ v.shape.suspensionIso,
    realize_map_suspensionMap_comp_suspension_map (w := v) (v := w) φ.hom hφ⟩

theorem equiv_boundary_suspension (w : PastingDiagram (bipointedHom.obj p)) (k : ℕ) (α : Bool) :
    (w.suspension.boundary (k + 1) α).Equiv (w.boundary k α).suspension := by
  exact @equiv_of_emb_of_image_eq _ _ _ w.shape.suspension.rdc w.suspension.map
    (w.shape.suspension.boundaryIncl (k + 1) α)
    (MoleculeShape.suspensionMap (w.shape.boundaryIncl k α))
    (inferInstanceAs (IsInclusion (w.shape.suspension.boundaryIncl (k + 1) α)))
    (inferInstanceAs (IsInclusion (MoleculeShape.suspensionMap (w.shape.boundaryIncl k α)))) rfl
    (realize_map_suspensionMap_comp_suspension_map _ rfl)
    (MoleculeShape.map_boundaryIncl_suspension_top w.shape k α)

theorem Pastable.suspension {w v : PastingDiagram (bipointedHom.obj p)} {k : ℕ}
    (h : w.Pastable v k) : w.suspension.Pastable v.suspension (k + 1) :=
  ⟨(equiv_boundary_suspension w k true).trans
    (h.1.suspension.trans (equiv_boundary_suspension v k false).symm), by
    rw [dim_suspension, dim_suspension]
    have := h.2
    omega⟩

theorem equiv_suspension_paste {w v : PastingDiagram (bipointedHom.obj p)} {k : ℕ}
    (h : w.Pastable v k) :
    (w.suspension.paste v.suspension (k + 1) h.suspension).Equiv (w.paste v k h).suspension := by
  have hm := isPastingIn_paste w v k h.1.iso
  have hne : ((OGP.map (pasteInl w v k h.1.iso) ⊤ ⊓ OGP.map (pasteInr w v k h.1.iso) ⊤ :
      LowerSet (w.shape.paste v.shape k h.1.iso).ogp) :
        Set (w.shape.paste v.shape k h.1.iso).ogp).Nonempty := by
    rw [hm.inf_eq_output]
    exact (((isMoleculeIn_map_iff (pasteInl w v k h.1.iso) ⊤).2
      w.shape.isMolecule).boundary k true).nonempty
  have hs := (isPastingIn_map_iff (w.shape.paste v.shape k h.1.iso).suspensionIso.hom (k + 1)
    _ _ _).2 (isPastingIn_susp hm hne)
  rw [susp_top, map_top_of_isIso (w.shape.paste v.shape k h.1.iso).suspensionIso.hom] at hs
  have hi := realize_map_suspensionMap_comp_suspension_map (w := w.paste v k h) (v := w)
    (pasteInl w v k h.1.iso) (ofInclusion_pasteInl_map w v k _ _)
  have hj := realize_map_suspensionMap_comp_suspension_map (w := w.paste v k h) (v := v)
    (pasteInr w v k h.1.iso) (ofInclusion_pasteInr_map w v k _ _)
  have hp : ((w.shape.paste v.shape k h.1.iso).suspension.ogp).IsPastingIn (k + 1)
      (OGP.map (MoleculeShape.suspensionMap (pasteInl w v k h.1.iso)) ⊤)
      (OGP.map (MoleculeShape.suspensionMap (pasteInr w v k h.1.iso)) ⊤)
        (OGP.map (𝟙 (w.shape.paste v.shape k h.1.iso).suspension.ogp) ⊤) := by
    rw [MoleculeShape.map_suspensionMap_top, MoleculeShape.map_suspensionMap_top,
      map_top_of_isIso (𝟙 (w.shape.paste v.shape k h.1.iso).suspension.ogp)]
    exact hs
  refine @equiv_paste_of_emb _ w.suspension v.suspension (w.paste v k h).suspension (k + 1)
    h.suspension (w.shape.paste v.shape k h.1.iso).suspension.rdc (w.paste v k h).suspension.map
    (𝟙 _) (MoleculeShape.suspensionMap (pasteInl w v k h.1.iso))
    (MoleculeShape.suspensionMap (pasteInr w v k h.1.iso)) (IsInclusion.id _)
    (inferInstanceAs (IsInclusion (MoleculeShape.suspensionMap (pasteInl w v k h.1.iso))))
    (inferInstanceAs (IsInclusion (MoleculeShape.suspensionMap (pasteInr w v k h.1.iso))))
    ((congrArg (· ≫ _) ((congrArg realize.map (MoleculeShape.ofInclusion_id
      (w.shape.paste v.shape k h.1.iso).suspension)).trans (realize.map_id _))).trans
        (Category.id_comp _)) hi hj hp

theorem equiv_suspension_ofCell {U : Atom} (x : diagram (bipointedHom.obj p) U) :
    (ofCell x).suspension.Equiv
      (ofCell (X := p.right) (uliftYonedaEquiv (bipointedHomObjEquiv p U x).1)) := by
  have key : (bipointedSuspensionRealizeIso.{u} (atomToRDCpx.obj U)).inv ≫
      (bipointedSuspensionAdjunction.homEquiv _ _).symm
        ((realizeAtomIso U).hom ≫ uliftYonedaEquiv.symm x) =
      Under.homMk (V := suspendedBall.obj U) (realizeSuspensionAtomIso U).hom
        (realizeSuspensionPoles_comp_realizeSuspensionAtomIso_hom U) ≫ x.down := by
    rw [Adjunction.homEquiv_naturality_left_symm,
      bipointedSuspensionAdjunction_homEquiv_symm_uliftYonedaEquiv_symm,
      ← Category.assoc (bipointedSuspension.map _), bipointedSuspension_map_realizeAtomIso_hom]
    exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans (Iso.inv_hom_id_assoc _ _)
  refine ⟨U.toMoleculeShape.suspensionIso.symm ≪≫
    (FiniteOGP.ofOGPIso (OGP.suspension U.ogp) :
      OGP.suspension U.ogp ≅ (atomSuspension.obj U).ogp), ?_⟩
  have hφ : realize.map (RDCpx.isoOfIso (P := U.toMoleculeShape.suspension.rdc)
      (Q := (atomSuspension.obj U).toMoleculeShape.rdc) (U.toMoleculeShape.suspensionIso.symm ≪≫
        (FiniteOGP.ofOGPIso (OGP.suspension U.ogp) :
          OGP.suspension U.ogp ≅ (atomSuspension.obj U).ogp))).hom =
      realize.{u}.map U.toMoleculeShape.suspensionRDCIso.inv ≫
        realize.map (atomSuspensionRDCIso U).inv :=
    (congrArg realize.map (by ext y; rfl)).trans (Functor.map_comp _ _ _)
  rw [ofCell_map, Equiv.symm_apply_apply]
  exact (congrArg (· ≫ _) hφ).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    ((Category.assoc _ _ _).symm.trans (congrArg Under.Hom.right key).symm)))

theorem realize_map_comp_suspension_map {w v : PastingDiagram (bipointedHom.obj p)}
    (f : v.shape.rdc ⟶ w.shape.rdc) (hf : realize.map f ≫ w.map = v.map) :
    realize.map (v.shape.suspensionRDCIso.inv ≫ RDCpx.suspensionFunctor.map f ≫
      w.shape.suspensionRDCIso.hom) ≫ w.suspension.map = v.suspension.map := by
  have hn : Under.homMk (V := Under.mk (realizeSuspensionPoles.{u} w.shape.rdc))
      (realize.map (RDCpx.suspensionFunctor.map f)) (realizeSuspensionPoles_comp _) ≫
        (bipointedSuspensionRealizeIso w.shape.rdc).inv =
      (bipointedSuspensionRealizeIso v.shape.rdc).inv ≫
        bipointedSuspension.map (realize.map f) := by
    rw [Iso.comp_inv_eq, Category.assoc, bipointedSuspensionRealizeIso_hom_naturality,
      Iso.inv_hom_id_assoc]
  have key : Under.homMk (V := Under.mk (realizeSuspensionPoles.{u} w.shape.rdc))
      (realize.map (RDCpx.suspensionFunctor.map f)) (realizeSuspensionPoles_comp _) ≫
        w.suspensionHom = v.suspensionHom := by
    rw [suspensionHom, suspensionHom, reassoc_of% hn, ← Adjunction.homEquiv_naturality_left_symm,
      hf]
  rw [suspension_map, suspension_map, ← Functor.map_comp_assoc, Category.assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Functor.map_comp_assoc, ← key, Under.comp_right]
  rfl

theorem equiv_suspension_unit (w : PastingDiagram (bipointedHom.obj p)) :
    w.unit.suspension.Equiv w.suspension.unit := by
  refine ⟨suspensionUnitShapeIso w.shape, (Functor.map_comp_assoc realize _ _ _).symm.trans ?_⟩
  refine (congrArg (fun g => realize.map g ≫ w.suspension.map)
    (isoOfIso_suspensionUnitShapeIso_comp_cylProj w.shape)).trans ?_
  exact realize_map_comp_suspension_map (w := w) (v := w.unit) _ rfl

theorem isRound_suspension_iff (w : PastingDiagram (bipointedHom.obj p)) :
    w.suspension.IsRound ↔ w.IsRound :=
  w.shape.isRound_suspension_iff

theorem eq_of_suspension_map_eq {M : MoleculeShape} {f g : realize.obj M.rdc ⟶ bipointedHom.obj p}
    (h : (⟨M, f⟩ : PastingDiagram (bipointedHom.obj p)).suspension.map =
      (⟨M, g⟩ : PastingDiagram (bipointedHom.obj p)).suspension.map) : f = g := by
  have h' : (⟨M, f⟩ : PastingDiagram (bipointedHom.obj p)).suspensionHom =
      (⟨M, g⟩ : PastingDiagram (bipointedHom.obj p)).suspensionHom :=
    Under.UnderMorphism.ext ((cancel_epi (realize.map M.suspensionRDCIso.inv)).1 h)
  rw [suspensionHom, suspensionHom, cancel_epi] at h'
  exact (bipointedSuspensionAdjunction.homEquiv _ _).symm.injective h'

theorem suspension_equiv_suspension_iff {w v : PastingDiagram (bipointedHom.obj p)} :
    w.suspension.Equiv v.suspension ↔ w.Equiv v := by
  refine ⟨fun ⟨φ, hφ⟩ => ?_, Equiv.suspension⟩
  set ψ := MoleculeShape.desuspensionIso φ
  refine ⟨ψ, eq_of_suspension_map_eq (M := w.shape) ?_⟩
  have hs := realize_map_suspensionMap_comp_suspension_map (w := v)
    (v := ⟨w.shape, realize.map (RDCpx.isoOfIso (P := w.shape.rdc) (Q := v.shape.rdc) ψ).hom ≫
      v.map⟩) ψ.hom rfl
  have he : RDCpx.ofInclusion (P := w.shape.suspension.rdc) (Q := v.shape.suspension.rdc)
      (MoleculeShape.suspensionMap ψ.hom) =
      (RDCpx.isoOfIso (P := w.shape.suspension.rdc) (Q := v.shape.suspension.rdc) φ).hom := by
    ext y
    exact ConcreteCategory.congr_hom (MoleculeShape.suspensionMap_desuspensionIso_hom φ) y
  rw [he] at hs
  exact hs.symm.trans hφ

theorem pastable_suspension_iff {w v : PastingDiagram (bipointedHom.obj p)} {k : ℕ} :
    w.suspension.Pastable v.suspension (k + 1) ↔ w.Pastable v k := by
  refine ⟨fun h => ⟨suspension_equiv_suspension_iff.1 ((equiv_boundary_suspension w k
    true).symm.trans (h.1.trans (equiv_boundary_suspension v k false))), ?_⟩, Pastable.suspension⟩
  have := h.2
  rw [dim_suspension, dim_suspension] at this
  omega

@[reassoc] theorem realizeSuspensionPoles_comp_realize_map_ofInclusion_suspensionMap
    {M N : MoleculeShape} (j : M.ogp ⟶ N.ogp) [IsInclusion j] :
    realizeSuspensionPoles.{u} M.rdc ≫ realize.map M.suspensionRDCIso.hom ≫
      realize.map (RDCpx.ofInclusion (P := M.suspension.rdc) (Q := N.suspension.rdc)
        (MoleculeShape.suspensionMap j)) =
    realizeSuspensionPoles N.rdc ≫ realize.map N.suspensionRDCIso.hom := by
  rw [← Functor.map_comp, MoleculeShape.suspensionRDCIso_hom_comp_ofInclusion_suspensionMap,
    Functor.map_comp, realizeSuspensionPoles_comp_assoc]

theorem realizeSuspensionPoles_comp_of_equiv_suspension {M : MoleculeShape}
    {f : realize.obj M.suspension.rdc ⟶ p.right} {w : PastingDiagram (bipointedHom.obj p)}
    (h : (⟨M.suspension, f⟩ : PastingDiagram p.right).Equiv w.suspension) :
    realizeSuspensionPoles M.rdc ≫ realize.map M.suspensionRDCIso.hom ≫ f = p.hom := by
  obtain ⟨(φ : M.suspension.ogp ≅ w.shape.suspension.ogp), hφ⟩ := h
  have he : RDCpx.ofInclusion (P := M.suspension.rdc) (Q := w.shape.suspension.rdc)
      (MoleculeShape.suspensionMap (MoleculeShape.desuspensionIso φ).hom) =
      (RDCpx.isoOfIso (P := M.suspension.rdc) (Q := w.shape.suspension.rdc) φ).hom := by
    ext y
    exact ConcreteCategory.congr_hom (MoleculeShape.suspensionMap_desuspensionIso_hom φ) y
  have hφ' : realize.map (RDCpx.isoOfIso (P := M.suspension.rdc) (Q := w.shape.suspension.rdc)
      φ).hom ≫ w.suspension.map = f := hφ
  rw [← hφ', ← he]
  exact (realizeSuspensionPoles_comp_realize_map_ofInclusion_suspensionMap_assoc _ _).trans
    (realizeSuspensionPoles_comp_suspension_map w)

noncomputable def desuspension (M : MoleculeShape) (f : realize.obj M.suspension.rdc ⟶ p.right)
    (hf : realizeSuspensionPoles M.rdc ≫ realize.map M.suspensionRDCIso.hom ≫ f = p.hom) :
    PastingDiagram (bipointedHom.obj p) :=
  ⟨M, bipointedSuspensionAdjunction.homEquiv _ _ ((bipointedSuspensionRealizeIso M.rdc).hom ≫
    Under.homMk (U := Under.mk (realizeSuspensionPoles.{u} M.rdc)) (V := p)
      (realize.map M.suspensionRDCIso.hom ≫ f) hf)⟩

theorem suspension_desuspension_map (M : MoleculeShape)
    (f : realize.obj M.suspension.rdc ⟶ p.right)
    (hf : realizeSuspensionPoles M.rdc ≫ realize.map M.suspensionRDCIso.hom ≫ f = p.hom) :
    (desuspension M f hf).suspension.map = f := by
  have h : (desuspension M f hf).suspensionHom = Under.homMk
      (U := Under.mk (realizeSuspensionPoles.{u} M.rdc)) (V := p)
      (realize.map M.suspensionRDCIso.hom ≫ f) hf := by
    rw [suspensionHom]
    exact (congrArg _ (Equiv.symm_apply_apply _ _)).trans (Iso.inv_hom_id_assoc _ _)
  exact (congrArg (realize.map M.suspensionRDCIso.inv ≫ ·) (congrArg Under.Hom.right h)).trans
    ((Functor.map_comp_assoc _ _ _ _).symm.trans (by
      rw [Iso.inv_hom_id, realize.map_id, Category.id_comp]))

private theorem exists_atom_boundary_iso (A : Bool → MoleculeShape) {n : ℕ}
    (hA : ∀ β, (A β).IsRound) (hd : ∀ β, (A β).dimension = n)
    (hb : ∀ m β, n = m + 1 →
      Nonempty (((A false).boundary m β).ogp ≅ ((A true).boundary m β).ogp)) :
    ∃ M : MoleculeShape, IsAtom M.ogp ∧ M.dimension = n + 1 ∧
      ∀ β, Nonempty ((M.boundary n β).ogp ≅ (A β).ogp) := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (A false).ogp.restrict ((A false).ogp.bdryFull ⊤) ≅
      (A true).ogp.restrict ((A true).ogp.bdryFull ⊤), ψ.IsSigned := by
    rcases n with _ | m
    · exact ⟨_, MoleculeShape.isSigned_bdryIsoOfPoints _ _ (hd false) (hd true)⟩
    · exact ⟨_, MoleculeShape.isSigned_bdryIsoOfParallel _ _ (fun β => (hb m β rfl).some)
        (hA false) (hA true) (hd false) (hd true)⟩
  have hdd : (A false).dimension = (A true).dimension := (hd false).trans (hd true).symm
  refine ⟨MoleculeShape.rewriteAtom _ _ ψ hψ (hA false) (hA true) hdd,
    MoleculeShape.isAtom_rewriteAtom _ _ _ _ _ _ _, by
      rw [MoleculeShape.dimension_rewriteAtom, hd false], fun β => ?_⟩
  have e := MoleculeShape.boundaryIsoRewriteAtom _ _ ψ hψ (hA false) (hA true) hdd β
  rw [hd false] at e
  cases β
  · exact ⟨e⟩
  · exact ⟨e⟩

theorem exists_cell_equiv_suspension {V : Atom} (c : diagram p.right V) {n : ℕ}
    (hV : V.dimension = n + 2) (a : Bool → PastingDiagram (bipointedHom.obj p))
    (ha : ∀ α, ((ofCell c).boundary (n + 1) α).Equiv (a α).suspension) :
    ∃ (U : Atom) (d : diagram (bipointedHom.obj p) U), (ofCell d).suspension.Equiv (ofCell c) := by
  have hdim (α : Bool) : (a α).dim = n := by
    have h := (dim_eq_of_equiv (ha α)).symm
    have hc : (ofCell c).dim = V.dimension := rfl
    rw [dim_suspension, dim_boundary (ofCell c) (by omega)] at h
    omega
  have hround (α : Bool) : (a α).IsRound := (isRound_suspension_iff _).1
    ((ha α).isRound_iff.1 (isRound_boundary_of_isRound (u := ofCell c)
      (IsAtomIn.isRound V.isAtom) _ α))
  have hb (m : ℕ) (β : Bool) (hm : n = m + 1) :
      ((a false).boundary m β).Equiv ((a true).boundary m β) := by
    have e (α : Bool) : ((a α).boundary m β).suspension.Equiv ((ofCell c).boundary (m + 1) β) :=
      (equiv_boundary_suspension _ m β).symm.trans ((((ha α).symm.boundary (m + 1) β)).trans
        (equiv_boundary_boundary _ (by omega) α β))
    exact suspension_equiv_suspension_iff.1 ((e false).trans (e true).symm)
  obtain ⟨M, hM, hdM, hMb⟩ := exists_atom_boundary_iso (fun α => (a α).shape) hround hdim
    fun m β hm => ⟨(hb m β hm).iso⟩
  have hφ (β : Bool) : Nonempty ((M.suspension.boundary (n + 1) β).ogp ≅
      (V.toMoleculeShape.boundary (n + 1) β).ogp) :=
    ⟨(M.nonempty_iso_boundary_suspension n β).some ≪≫ (M.boundary n β).suspensionIso.symm ≪≫
      OGP.suspension.mapIso (hMb β).some ≪≫ (a β).shape.suspensionIso ≪≫ (ha β).iso.symm⟩
  obtain ⟨θ⟩ := MoleculeShape.nonempty_iso_of_boundary_iso M.suspension V.toMoleculeShape
    (fun β => (hφ β).some) ((isAtom_iff_of_iso M.suspensionIso).1 (isAtom_suspension _ hM))
    V.isAtom (by rw [M.dimension_suspension, hdM]) hV
  set z : PastingDiagram p.right :=
    ⟨M.suspension, realize.map (RDCpx.isoOfIso (P := M.suspension.rdc)
      (Q := V.toMoleculeShape.rdc) θ).hom ≫ (ofCell c).map⟩
  have hz : z.Equiv (ofCell c) := ⟨θ, rfl⟩
  have hB : (⟨(M.boundary n false).suspension, realize.map (RDCpx.ofInclusion
      (P := (M.boundary n false).suspension.rdc) (Q := M.suspension.rdc)
      (MoleculeShape.suspensionMap (M.boundaryIncl n false))) ≫ z.map⟩ :
        PastingDiagram p.right).Equiv (a false).suspension :=
    ((@equiv_of_emb_of_image_eq _ _ _ M.suspension.rdc z.map
      (MoleculeShape.suspensionMap (M.boundaryIncl n false))
      (M.suspension.boundaryIncl (n + 1) false)
      (inferInstanceAs (IsInclusion (MoleculeShape.suspensionMap (M.boundaryIncl n false))))
      (inferInstanceAs (IsInclusion (M.suspension.boundaryIncl (n + 1) false))) rfl rfl
      (MoleculeShape.map_boundaryIncl_suspension_top M n false).symm).trans
      (hz.boundary (n + 1) false)).trans (ha false)
  have hpoles : realizeSuspensionPoles M.rdc ≫ realize.map M.suspensionRDCIso.hom ≫ z.map =
      p.hom :=
    (realizeSuspensionPoles_comp_realize_map_ofInclusion_suspensionMap_assoc _ _).symm.trans
      (realizeSuspensionPoles_comp_of_equiv_suspension hB)
  set w := desuspension M z.map hpoles
  have hw : w.suspension.Equiv z :=
    (equiv_mk_iff (S := M.suspension)).2 (suspension_desuspension_map M z.map hpoles)
  set U : Atom := Atom.ofIsAtom M.toFiniteOGP hM
  refine ⟨U, uliftYonedaEquiv ((realizeAtomIso U).inv ≫ w.map), ?_⟩
  have hd : (ofCell (uliftYonedaEquiv ((realizeAtomIso U).inv ≫ w.map))).Equiv w :=
    (equiv_mk_iff (S := M)).2 ((congrArg ((realizeAtomIso U).hom ≫ ·)
      (Equiv.symm_apply_apply _ _)).trans (Iso.hom_inv_id_assoc _ _))
  exact (hd.suspension.trans hw).trans hz

end PastingDiagram

noncomputable def RoundPastingDiagram.suspension {p : Under pointPair.{u}}
    (e : RoundPastingDiagram (bipointedHom.obj p)) : RoundPastingDiagram p.right :=
  ⟨e.toPastingDiagram.suspension, e.isRound.suspension⟩

@[simp] theorem RoundPastingDiagram.suspension_toPastingDiagram {p : Under pointPair.{u}}
    (e : RoundPastingDiagram (bipointedHom.obj p)) :
    e.suspension.toPastingDiagram = e.toPastingDiagram.suspension :=
  rfl

theorem Parallel.of_suspension {p : Under pointPair.{u}}
    {e e' : RoundPastingDiagram (bipointedHom.obj p)}
    (h : Parallel e.suspension e'.suspension) : Parallel e e' := by
  have hd : e.dim = e'.dim := by
    have := h.1
    rw [RoundPastingDiagram.suspension_toPastingDiagram,
      RoundPastingDiagram.suspension_toPastingDiagram, PastingDiagram.dim_suspension,
      PastingDiagram.dim_suspension] at this
    omega
  refine ⟨hd, ?_⟩
  rcases Nat.eq_zero_or_pos e.dim with hz | hpos
  · exact Or.inl hz
  obtain ⟨d, hdd⟩ := Nat.exists_eq_add_one_of_ne_zero hpos.ne'
  refine Or.inr fun α => ?_
  have hb := h.2.resolve_left (by
    rw [RoundPastingDiagram.suspension_toPastingDiagram, PastingDiagram.dim_suspension]
    omega) α
  rw [RoundPastingDiagram.suspension_toPastingDiagram,
    RoundPastingDiagram.suspension_toPastingDiagram, PastingDiagram.dim_suspension,
    PastingDiagram.dim_suspension, ← hd, hdd, Nat.add_sub_cancel] at hb
  rw [← hd, hdd]
  exact PastingDiagram.suspension_equiv_suspension_iff.1
    ((PastingDiagram.equiv_boundary_suspension _ _ α).symm.trans
      (hb.trans (PastingDiagram.equiv_boundary_suspension _ _ α)))

end Atoms.Diagrammatic
