import Atoms.Diagrammatic.Realization

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

structure PastingDiagram (X : DiagSet.{u}) where
  shape : MoleculeShape
  map : realize.obj shape.rdc ⟶ X

end Atoms.Diagrammatic

namespace Atoms.Diagrammatic.PastingDiagram

variable {X Y : DiagSet.{u}}

def dim (u : PastingDiagram X) : ℕ := u.shape.dimension

theorem dim_def (u : PastingDiagram X) : u.dim = u.shape.dimension := rfl

def IsRound (u : PastingDiagram X) : Prop := u.shape.IsRound

def Equiv (u v : PastingDiagram X) : Prop :=
  ∃ φ : u.shape.ogp ≅ v.shape.ogp,
    realize.map (RDCpx.isoOfIso (P := u.shape.rdc) (Q := v.shape.rdc) φ).hom ≫ v.map = u.map

noncomputable def Equiv.iso {u v : PastingDiagram X} (h : u.Equiv v) :
    u.shape.ogp ≅ v.shape.ogp :=
  h.choose

theorem Equiv.map_comm {u v : PastingDiagram X} (h : u.Equiv v) :
    realize.map (RDCpx.isoOfIso (P := u.shape.rdc) (Q := v.shape.rdc) h.iso).hom ≫ v.map =
      u.map :=
  h.choose_spec

@[refl]
theorem Equiv.refl (u : PastingDiagram X) : u.Equiv u :=
  ⟨Iso.refl _, by
    change realize.map (𝟙 _) ≫ u.map = u.map
    rw [realize.map_id, Category.id_comp]⟩

@[symm]
theorem Equiv.symm {u v : PastingDiagram X} (h : u.Equiv v) : v.Equiv u := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.symm, ?_⟩
  have h : (RDCpx.isoOfIso (P := v.shape.rdc) (Q := u.shape.rdc) φ.symm).hom ≫
      (RDCpx.isoOfIso (P := u.shape.rdc) (Q := v.shape.rdc) φ).hom = 𝟙 _ :=
    (RDCpx.isoOfIso (P := u.shape.rdc) (Q := v.shape.rdc) φ).inv_hom_id
  rw [← hφ, ← Category.assoc, ← realize.map_comp, h, realize.map_id, Category.id_comp]

@[trans]
theorem Equiv.trans {u v w : PastingDiagram X} (h : u.Equiv v) (h' : v.Equiv w) : u.Equiv w := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨ψ, hψ⟩ := h'
  refine ⟨φ ≪≫ ψ, ?_⟩
  change realize.map ((RDCpx.isoOfIso (P := u.shape.rdc) (Q := v.shape.rdc) φ).hom ≫
    (RDCpx.isoOfIso (P := v.shape.rdc) (Q := w.shape.rdc) ψ).hom) ≫ w.map = u.map
  rw [realize.map_comp, Category.assoc, hψ, hφ]

theorem Equiv.cond {a a' b b' : PastingDiagram X} (ea : a.Equiv a') (α : Bool)
    (eb : b.Equiv b') : (cond α a b).Equiv (cond α a' b') := by
  cases α
  · exact eb
  · exact ea

instance : @Trans (PastingDiagram X) (PastingDiagram X) (PastingDiagram X) Equiv Equiv Equiv :=
  ⟨Equiv.trans⟩

theorem dim_eq_of_equiv {u v : PastingDiagram X} (h : u.Equiv v) : u.dim = v.dim := by
  have hd := krullDim_eq_of_orderIso (orderIsoOfIso h.iso)
  rw [u.shape.krullDim_eq_dimension, v.shape.krullDim_eq_dimension] at hd
  exact_mod_cast hd

theorem Equiv.isRound_iff {u v : PastingDiagram X} (h : u.Equiv v) : u.IsRound ↔ v.IsRound :=
  (isRound_top_iff_of_iso h.iso).symm

@[implicit_reducible, simps]
def boundary (u : PastingDiagram X) (k : ℕ) (α : Bool) : PastingDiagram X :=
  ⟨u.shape.boundary k α, realize.map (u.shape.boundaryInclRDC k α) ≫ u.map⟩

theorem boundary_congr (u : PastingDiagram X) {k k' : ℕ} (hk : k = k') (β : Bool) :
    u.boundary k β = u.boundary k' β :=
  congrArg (u.boundary · β) hk

theorem dim_boundary (u : PastingDiagram X) {k : ℕ} (hk : k ≤ u.dim) (α : Bool) :
    (u.boundary k α).dim = k :=
  u.shape.dimension_boundary hk α

@[implicit_reducible, simps]
def mapTo (u : PastingDiagram X) (f : X ⟶ Y) : PastingDiagram Y := ⟨u.shape, u.map ≫ f⟩

theorem mapTo_comp {Z : DiagSet.{u}} (u : PastingDiagram X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    u.mapTo (f ≫ g) = (u.mapTo f).mapTo g :=
  congrArg (PastingDiagram.mk u.shape) (Category.assoc _ _ _).symm

theorem mapTo_id (u : PastingDiagram X) : u.mapTo (𝟙 X) = u :=
  congrArg (PastingDiagram.mk u.shape) (Category.comp_id _)

@[implicit_reducible, simps] def ofCell {U : Atom} (x : diagram X U) : PastingDiagram X :=
  ⟨U.toMoleculeShape, (realizeAtomIso U).hom ≫ uliftYonedaEquiv.symm x⟩

theorem ofCell_app (f : X ⟶ Y) {U : Atom} (x : diagram X U) :
    ofCell (f.app (op U) x) = (ofCell x).mapTo f := by
  change PastingDiagram.mk _ _ = PastingDiagram.mk _ _
  congr 1
  exact (congrArg ((realizeAtomIso U).hom ≫ ·)
    (uliftYonedaEquiv_symm_comp x f).symm).trans (Category.assoc _ _ _).symm

theorem ofCell_map_app_map {U T : Atom} (z : diagram X U) (g : T ⟶ U) :
    (ofCell z).map.app (op T) ⟨atomToRDCpx.map g⟩ = X.map g.op z :=
  rfl

theorem ofCell_map_op_map {A H : Atom} (g : A ⟶ H) (h : diagram X H) :
    (ofCell (X.map g.op h)).map = realize.map (atomToRDCpx.map g) ≫ (ofCell h).map := by
  ext ⟨T⟩ ⟨c⟩
  exact (Functor.map_comp_apply X g.op
    (InducedCategory.homMk (F := fun W : Atom => W.rdc) (X := T) (Y := A) c).op h).symm

theorem ofCell_map_injective {U : Atom} {x y : diagram X U}
    (h : (ofCell x).map = (ofCell y).map) : x = y :=
  uliftYonedaEquiv.symm.injective ((cancel_epi (realizeAtomIso U).hom).1 h)

end Atoms.Diagrammatic.PastingDiagram

namespace Atoms.Diagrammatic

structure RoundPastingDiagram (X : DiagSet.{u}) extends PastingDiagram X where
  isRound : toPastingDiagram.IsRound

@[ext] theorem RoundPastingDiagram.ext {X : DiagSet.{u}} {u v : RoundPastingDiagram X}
    (h : u.toPastingDiagram = v.toPastingDiagram) : u = v := by
  cases u; cases v; cases h; rfl

theorem RoundPastingDiagram.mapTo_id {X : DiagSet.{u}} (u : RoundPastingDiagram X) :
    (⟨u.toPastingDiagram.mapTo (𝟙 X), u.isRound⟩ : RoundPastingDiagram X) = u :=
  RoundPastingDiagram.ext u.toPastingDiagram.mapTo_id

def RoundPastingDiagram.roundShape {X : DiagSet.{u}} (u : RoundPastingDiagram X) : RoundShape :=
  ⟨u.shape, u.isRound⟩

end Atoms.Diagrammatic
