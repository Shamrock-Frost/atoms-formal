import Atoms.Molecule.Cartesian
import Atoms.Molecule.Construction.Basic
import Atoms.ForMathlib.CategoryTheory.Widesubcategory

universe u v w

open CategoryTheory Set Topology

namespace Atoms.Molecule.OGP

def IsRDC (P : OGP.{u}) : Prop := ∀ x : P, IsMoleculeIn P (.Iic x)

theorem isRDC_of_isMolecule {P : OGP.{u}} (h : IsMolecule P) : IsRDC P := fun x =>
  (h.isAtomIn_Iic (LowerSet.mem_top (a := x))).1

theorem isRDC_point : point.{u}.IsRDC :=
  isRDC_of_isMolecule isAtom_point.isMoleculeIn

theorem IsMoleculeIn.isConnected {P : OGP.{u}} {U : LowerSet P} (h : IsMoleculeIn P U) :
    IsConnected (U : Set P) := by
  refine ⟨h.nonempty, ?_⟩
  induction h with
  | point x _ =>
    rw [LowerSet.coe_Iic, ← IsUpperSet.closure_singleton]
    exact isPreconnected_singleton.closure
  | atom t _ _ _ =>
    rw [LowerSet.coe_Iic, ← IsUpperSet.closure_singleton]
    exact isPreconnected_singleton.closure
  | paste k V W U hp hV _ _ ihV ihW =>
    obtain ⟨x, hx⟩ := (hV.boundary k true).nonempty
    have hxVW : x ∈ V ⊓ W := hp.inf_eq_output ▸ hx
    rw [← hp.sup_eq, LowerSet.coe_sup]
    exact ihV.union x hxVW.1 hxVW.2 ihW

variable {P : OGP.{u}} {Q : OGP.{v}} {R : OGP.{w}}

structure Map (P : OGP.{u}) (Q : OGP.{v}) where
  toFun : P → Q
  isMap : IsMap toFun

namespace Map

instance : FunLike (Map P Q) P Q where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

@[ext] theorem ext {f g : Map P Q} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

def id (P : OGP.{u}) : Map P P := ⟨_root_.id, IsMap.id P⟩

def comp (g : Map Q R) (f : Map P Q) : Map P R := ⟨g ∘ f, f.isMap.comp g.isMap⟩

@[simp] theorem id_apply (x : P) : Map.id P x = x := rfl

@[simp] theorem comp_apply (g : Map Q R) (f : Map P Q) (x : P) : g.comp f x = g (f x) := rfl

end Map

structure RDCpxDown : Type (u + 1) where
  toOGP : OGP.{u}
  isRDC : toOGP.IsRDC

namespace RDCpxDown

instance : CoeSort RDCpxDown.{u} (Type u) := ⟨fun P => P.toOGP⟩

@[ext] structure Hom (P Q : RDCpxDown.{u}) where
  private mk ::
  hom' : Map P.toOGP Q.toOGP

instance : Category RDCpxDown.{u} where
  Hom := Hom
  id P := ⟨Map.id P.toOGP⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory RDCpxDown.{u} fun P Q => Map P.toOGP Q.toOGP where
  hom := Hom.hom'
  ofHom := Hom.mk

end RDCpxDown

def cartesian : MorphismProperty RDCpxDown.{u} := fun _ _ f =>
  (ConcreteCategory.hom f).isMap.monotone.functor.IsFibered

instance : cartesian.{u}.IsMultiplicative where
  id_mem _ := Monotone.functor_isFibered_id
  comp_mem f g hf hg := by
    have : (ConcreteCategory.hom f).isMap.monotone.functor.IsFibered := hf
    have : (ConcreteCategory.hom g).isMap.monotone.functor.IsFibered := hg
    exact Monotone.functor_isFibered_comp (ConcreteCategory.hom f).isMap.monotone
      (ConcreteCategory.hom g).isMap.monotone

def localEmbeddings : MorphismProperty RDCpxDown.{u} := fun _ _ f =>
  IsLocalEmbedding (ConcreteCategory.hom f)

instance : localEmbeddings.{u}.IsMultiplicative where
  id_mem P := IsLocalEmbedding.id P.toOGP
  comp_mem _ _ hf hg := hg.comp hf

theorem localEmbeddings_le_cartesian : localEmbeddings.{u} ≤ cartesian.{u} := fun _ _ _ hf =>
  hf.functor_isFibered

abbrev RDCpx : Type (u + 1) := WideSubcategory cartesian.{u}

@[implicit_reducible] def RDCpxEq : Type (u + 1) := WideSubcategory localEmbeddings.{u}

deriving instance Category for RDCpxEq

abbrev RDCpxEq.toRDCpx : RDCpxEq.{u} ⥤ RDCpx.{u} :=
  (𝟭 RDCpxDown.{u}).mapWideSubcategory localEmbeddings_le_cartesian

namespace RDCpx

variable {P Q : RDCpx.{u}}

def ofInclusion (f : P.obj.toOGP ⟶ Q.obj.toOGP) [IsInclusion f] : P ⟶ Q :=
  let φ : Map P.obj.toOGP Q.obj.toOGP := ⟨f, isMap_of_isInclusion f⟩
  ⟨ConcreteCategory.ofHom (X := P.obj) (Y := Q.obj) φ,
    (isLocalEmbedding_of_isInclusion f).functor_isFibered⟩

@[simp] theorem ofInclusion_apply (f : P.obj.toOGP ⟶ Q.obj.toOGP) [IsInclusion f] (x : P.obj) :
    ConcreteCategory.hom (ofInclusion f).hom x = f x :=
  rfl

@[simps] def isoOfIso (e : P.obj.toOGP ≅ Q.obj.toOGP) : P ≅ Q where
  hom := ofInclusion e.hom
  inv := ofInclusion e.inv
  hom_inv_id := by
    ext x
    exact congrArg (fun g : P.obj.toOGP ⟶ P.obj.toOGP => g x) e.hom_inv_id
  inv_hom_id := by
    ext x
    exact congrArg (fun g : Q.obj.toOGP ⟶ Q.obj.toOGP => g x) e.inv_hom_id

end RDCpx

end Atoms.Molecule.OGP
