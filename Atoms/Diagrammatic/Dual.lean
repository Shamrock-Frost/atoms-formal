import Atoms.Diagrammatic.Realization
import Atoms.Shape.Dual

open CategoryTheory Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable (J : ℕ → Bool)

namespace DiagSet

def dual : DiagSet.{u} ⥤ DiagSet.{u} :=
  (Functor.whiskeringLeft Atomᵒᵖ Atomᵒᵖ (Type u)).obj (Atom.dualFunctor J).op

@[simp] theorem dual_obj_obj (X : DiagSet.{u}) (U : Atomᵒᵖ) :
    ((dual J).obj X).obj U = X.obj (op (U.unop.dual J)) :=
  rfl

@[simp] theorem dual_obj_map (X : DiagSet.{u}) {U V : Atomᵒᵖ} (f : U ⟶ V) :
    ((dual J).obj X).map f = X.map (Atom.dualMap J f.unop).op :=
  rfl

@[simp] theorem dual_map_app {X Y : DiagSet.{u}} (f : X ⟶ Y) (U : Atomᵒᵖ) :
    ((dual J).map f).app U = f.app (op (U.unop.dual J)) :=
  rfl

def dualEquivalence : DiagSet.{u} ≌ DiagSet.{u} :=
  (Atom.dualEquivalence J).op.congrLeft

@[simp] theorem dualEquivalence_functor : (dualEquivalence.{u} J).functor = dual J :=
  rfl

@[simp] theorem dualEquivalence_inverse : (dualEquivalence.{u} J).inverse = dual J :=
  rfl

def dualDualIso (X : DiagSet.{u}) : (dual J).obj ((dual J).obj X) ≅ X :=
  (dualEquivalence J).counitIso.app X

@[simp] theorem dualDualIso_hom_app (X : DiagSet.{u}) (U : Atomᵒᵖ) :
    (dualDualIso J X).hom.app U = X.map (Atom.dualDualIso J U.unop).inv.op :=
  rfl

@[simp] theorem dualDualIso_inv_app (X : DiagSet.{u}) (U : Atomᵒᵖ) :
    (dualDualIso J X).inv.app U = X.map (Atom.dualDualIso J U.unop).hom.op :=
  rfl

theorem dual_map_dualDualIso_hom (X : DiagSet.{u}) :
    (dual J).map (dualDualIso J X).hom = (dualDualIso J ((dual J).obj X)).hom := by
  ext U : 2
  rw [dual_map_app, dualDualIso_hom_app, dualDualIso_hom_app, dual_obj_map]
  exact congrArg (fun f => X.map (Quiver.Hom.op f)) (congrArg Iso.inv
    (Iso.ext (α := (Atom.dualFunctor J).mapIso (Atom.dualDualIso J U.unop))
      (Atom.dualFunctor_map_dualDualIso_hom J U.unop))).symm

def dualBallIso (U : Atom) : (dual J).obj (ball.{u} U) ≅ ball.{u} (U.dual J) :=
  NatIso.ofComponents (fun W ↦ Equiv.toIso (Equiv.ulift.trans
      (((Atom.dualEquivalence J).toAdjunction.homEquiv W.unop U).trans Equiv.ulift.symm)))
    fun f ↦ by
      ext ⟨g⟩
      exact ULift.ext _ _ ((Atom.dualEquivalence J).toAdjunction.homEquiv_naturality_left f.unop g)

@[reassoc] theorem dual_map_uliftYoneda_map_comp_dualBallIso_hom {U V : Atom} (f : U ⟶ V) :
    (dual J).map (uliftYoneda.{u}.map f) ≫ (dualBallIso J V).hom =
      (dualBallIso J U).hom ≫ uliftYoneda.map (Atom.dualMap J f) := by
  ext W ⟨g⟩
  exact ULift.ext _ _ ((Atom.dualEquivalence J).toAdjunction.homEquiv_naturality_right g f)

end DiagSet

def realizeDualIso (P : RDCpx.{0}) :
    realize.{u}.obj ((RDCpx.dualFunctor J).obj P) ≅ (DiagSet.dual J).obj (realize.obj P) :=
  NatIso.ofComponents (fun T => Equiv.toIso (Equiv.ulift.trans
    (((RDCpx.dualHomEquiv J T.unop.rdc P).trans
      ((RDCpx.isoOfIso (P := (RDCpx.dualFunctor J).obj T.unop.rdc) (Q := (T.unop.dual J).rdc)
        (T.unop.toMoleculeShape.dualIso J)).homCongr (Iso.refl P))).trans Equiv.ulift.symm)))
    fun {T T'} f => by
      ext ⟨g⟩
      exact ULift.ext _ _ (WideSubcategory.hom_ext _ (ConcreteCategory.hom_ext _ _ fun x =>
        congrArg (ConcreteCategory.hom g.hom)
          ((T.unop.toMoleculeShape.dualIso J).hom_inv_id_apply _).symm))

@[reassoc]
theorem realizeDualIso_hom_naturality {P Q : RDCpx.{0}} (f : P ⟶ Q) :
    realize.{u}.map ((RDCpx.dualFunctor J).map f) ≫ (realizeDualIso J Q).hom =
      (realizeDualIso J P).hom ≫ (DiagSet.dual J).map (realize.map f) := by
  ext T ⟨g⟩
  exact ULift.ext _ _ (WideSubcategory.hom_ext _ (ConcreteCategory.hom_ext _ _ fun x => rfl))

end Atoms.Diagrammatic
