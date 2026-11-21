import Atoms.Diagrammatic.Context.Frames
import Atoms.Diagrammatic.Pasting.Substitution
import Atoms.Diagrammatic.Pasting.SubsetRestriction
import Atoms.Shape.Horn

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

namespace Parallel

variable {v w : RoundPastingDiagram X} (h : Parallel v w)

noncomputable def bdryIso :
    v.shape.ogp.restrict (v.shape.ogp.bdryFull ⊤) ≅ w.shape.ogp.restrict (w.shape.ogp.bdryFull ⊤) :=
  (PastingDiagram.exists_bdryIso_of_parallel h).choose

theorem isSigned_bdryIso : h.bdryIso.IsSigned :=
  (PastingDiagram.exists_bdryIso_of_parallel h).choose_spec.1

theorem realize_map_ofInclusion_bdryIso_comp_map :
    realize.map (RDCpx.ofInclusion (P := v.shape.rdc.restrict (v.shape.ogp.bdryFull ⊤))
      (Q := w.shape.rdc) (h.bdryIso.hom ≫ incl _)) ≫ w.map =
      realize.map (v.shape.rdc.restrictIncl (v.shape.ogp.bdryFull ⊤)) ≫ v.map :=
  (PastingDiagram.exists_bdryIso_of_parallel h).choose_spec.2

noncomputable def cellShape : Atom :=
  Atom.ofIsAtom (MoleculeShape.rewriteAtom v.shape w.shape h.bdryIso h.isSigned_bdryIso v.isRound
      w.isRound h.1).toFiniteOGP
    (MoleculeShape.isAtom_rewriteAtom v.shape w.shape h.bdryIso h.isSigned_bdryIso v.isRound
      w.isRound h.1)

theorem dimension_cellShape : h.cellShape.dimension = v.dim + 1 :=
  MoleculeShape.dimension_rewriteAtom v.shape w.shape h.bdryIso h.isSigned_bdryIso v.isRound
    w.isRound h.1

noncomputable def cellShapeEmb (α : Bool) : (cond α w.shape v.shape).ogp ⟶ h.cellShape.ogp :=
  MoleculeShape.rewriteAtomIncl v.shape w.shape h.bdryIso h.isSigned_bdryIso v.isRound w.isRound
    h.1 α

include h in
private theorem shape_dimension_eq : v.shape.dimension = w.shape.dimension := h.1

instance (α : Bool) : IsInclusion (h.cellShapeEmb α) :=
  inferInstanceAs (IsInclusion (MoleculeShape.rewriteAtomIncl v.shape w.shape h.bdryIso
    h.isSigned_bdryIso (v.shape.isRound_iff.2 v.isRound) (w.shape.isRound_iff.2 w.isRound)
    h.shape_dimension_eq α))

theorem bdry_cellShape (α : Bool) :
    h.cellShape.ogp.bdry ⊤ α = h.cellShape.ogp.boundary ⊤ v.dim α :=
  bdry_eq_boundary (h.cellShape.krullDim_top_eq h.dimension_cellShape) α

theorem map_cellShapeEmb (α : Bool) :
    OGP.map (h.cellShapeEmb α) ⊤ = h.cellShape.ogp.boundary ⊤ v.dim α :=
  (MoleculeShape.map_rewriteAtomIncl v.shape w.shape h.bdryIso h.isSigned_bdryIso v.isRound
    w.isRound h.1 α).trans (h.bdry_cellShape α)

theorem map_cellShapeEmb_le_bdryFull (α : Bool) :
    OGP.map (h.cellShapeEmb α) ⊤ ≤ h.cellShape.ogp.bdryFull ⊤ :=
  (MoleculeShape.map_rewriteAtomIncl v.shape w.shape h.bdryIso h.isSigned_bdryIso v.isRound
    w.isRound h.1 α).le.trans (bdry_le_bdryFull ⊤ α)

private theorem exists_sphere :
    ∃ σ : realize.obj (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)) ⟶ X,
      ∀ α, restrictAlong σ _ (h.cellShapeEmb α) (h.map_cellShapeEmb_le_bdryFull α) =
        (cond α w v).toPastingDiagram := by
  have hm (α : Bool) (x : (cond α w.shape v.shape).ogp) :
      h.cellShapeEmb α x ∈ h.cellShape.ogp.bdryFull ⊤ :=
    h.map_cellShapeEmb_le_bdryFull α ⟨x, LowerSet.mem_top, rfl⟩
  have hcov : OGP.map (codRestrict (h.cellShapeEmb false) _ (hm false)) ⊤ ⊔
      OGP.map (codRestrict (h.cellShapeEmb true) _ (hm true)) ⊤ = ⊤ := by
    refine map_injective (incl (h.cellShape.ogp.bdryFull ⊤)) ?_
    rw [map_sup, ← map_comp, ← map_comp, codRestrict_incl, codRestrict_incl, map_incl_top]
    exact congrArg₂ (· ⊔ ·)
      (MoleculeShape.map_rewriteAtomIncl v.shape w.shape h.bdryIso h.isSigned_bdryIso v.isRound
        w.isRound h.1 false)
      (MoleculeShape.map_rewriteAtomIncl v.shape w.shape h.bdryIso h.isSigned_bdryIso v.isRound
        w.isRound h.1 true)
  have himg : OGP.map (incl (v.shape.ogp.bdryFull ⊤) ≫
        codRestrict (h.cellShapeEmb false) _ (hm false)) ⊤ =
      OGP.map (codRestrict (h.cellShapeEmb false) _ (hm false)) ⊤ ⊓
        OGP.map (codRestrict (h.cellShapeEmb true) _ (hm true)) ⊤ := by
    refine map_injective (incl (h.cellShape.ogp.bdryFull ⊤)) ?_
    rw [map_inf, ← map_comp, ← map_comp, ← map_comp, Category.assoc, codRestrict_incl,
      codRestrict_incl, map_comp, map_incl_top]
    exact (MoleculeShape.map_rewriteAtomIncl_inf v.shape w.shape h.bdryIso h.isSigned_bdryIso
      v.isRound w.isRound h.1).symm
  have hab : CoverCompatible (R := h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤))
      (U := v.shape.rdc) (V := w.shape.rdc) (codRestrict (h.cellShapeEmb false) _ (hm false))
      (codRestrict (h.cellShapeEmb true) _ (hm true)) v.map w.map :=
    coverCompatible_of_emb _ _ v.map w.map (C := v.shape.rdc.restrict (v.shape.ogp.bdryFull ⊤))
      (incl _) (h.bdryIso.hom ≫ incl _)
      (fun y => Subtype.ext ((MoleculeShape.rewriteAtomIncl_false_eq_true_iff v.shape w.shape
        h.bdryIso h.isSigned_bdryIso v.isRound w.isRound h.1 _ _).2 ⟨y.2, rfl⟩))
      himg h.realize_map_ofInclusion_bdryIso_comp_map.symm
  refine ⟨coverDesc (R := h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤))
    (U := v.shape.rdc) (V := w.shape.rdc) _ _ hcov v.map w.map hab, fun α => ?_⟩
  cases α
  · exact congrArg (PastingDiagram.mk v.shape) (ofInclusion_coverDesc_left _ _ hcov _ _ hab)
  · exact congrArg (PastingDiagram.mk w.shape) (ofInclusion_coverDesc_right _ _ hcov _ _ hab)

noncomputable def sphere :
    realize.obj (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)) ⟶ X :=
  h.exists_sphere.choose

theorem restrictAlong_sphere (α : Bool) :
    restrictAlong h.sphere _ (h.cellShapeEmb α) (h.map_cellShapeEmb_le_bdryFull α) =
      (cond α w v).toPastingDiagram :=
  h.exists_sphere.choose_spec α

private theorem exists_iso_extends_of_hasRoundType (f : X ⟶ Y) {H : Atom} (x : diagram Y H)
    (hx : HasRoundType (PastingDiagram.ofCell x) ⟨v.toPastingDiagram.mapTo f, v.isRound⟩
      ⟨w.toPastingDiagram.mapTo f, w.isRound⟩) :
    ∃ e : h.cellShape ≅ H, realize.map (h.cellShape.rdc.restrictIncl
      (h.cellShape.ogp.bdryFull ⊤)) ≫ (ofCell (Y.map e.hom.op x)).map = h.sphere ≫ f := by
  have hA : 0 < h.cellShape.dimension := by
    rw [h.dimension_cellShape]
    exact Nat.succ_pos _
  have hn : h.cellShape.dimension - 1 = v.dim := by
    rw [h.dimension_cellShape]
    rfl
  have key : ∀ (β : Bool) {B : MoleculeShape} (g : B.ogp ⟶ h.cellShape.ogp) [IsInclusion g]
      (hg : OGP.map g ⊤ ≤ h.cellShape.ogp.bdryFull ⊤) (b : PastingDiagram X)
      (hkb : restrictAlong h.sphere B g hg = b)
      (himg : OGP.map g ⊤ = h.cellShape.ogp.boundary ⊤ v.dim β),
      (b.mapTo f).Equiv (sphereBoundary h.cellShape hA (h.sphere ≫ f) β) := by
    intro β B g _ hg b hkb himg
    subst hkb
    have hb : OGP.map (h.cellShape.boundaryIncl (h.cellShape.dimension - 1) β) ⊤ ≤
        h.cellShape.ogp.bdryFull ⊤ := by
      rw [h.cellShape.map_boundaryIncl_top, hn, ← himg]
      exact hg
    refine equiv_of_emb_of_image_eq (h.sphere ≫ f)
      (codRestrict g _ fun x => hg ⟨x, LowerSet.mem_top, rfl⟩)
      (codRestrict (h.cellShape.boundaryIncl (h.cellShape.dimension - 1) β) _
        fun x => hb ⟨x, LowerSet.mem_top, rfl⟩) (Category.assoc _ _ _).symm rfl ?_
    rw [map_codRestrict, map_codRestrict, himg, h.cellShape.map_boundaryIncl_top, hn]
  refine exists_iso_extends_of_equiv_boundary hA (hx.dim_eq.trans h.dimension_cellShape.symm)
    (h.sphere ≫ f) x fun α => ?_
  rw [boundary_congr _ hn α]
  cases α
  · exact hx.source.trans (key false (h.cellShapeEmb false) _ _ (h.restrictAlong_sphere false)
      (h.map_cellShapeEmb false))
  · exact hx.target.trans (key true (h.cellShapeEmb true) _ _ (h.restrictAlong_sphere true)
      (h.map_cellShapeEmb true))

theorem hasRoundType_ofCell_iff (f : X ⟶ Y) (a : diagram Y h.cellShape) :
    HasRoundType (PastingDiagram.ofCell a) ⟨v.toPastingDiagram.mapTo f, v.isRound⟩
        ⟨w.toPastingDiagram.mapTo f, w.isRound⟩ ↔
      realize.map (h.cellShape.rdc.restrictIncl (h.cellShape.ogp.bdryFull ⊤)) ≫ (ofCell a).map =
        h.sphere ≫ f := by
  constructor
  · intro hx
    obtain ⟨e, he⟩ := h.exists_iso_extends_of_hasRoundType f a hx
    have hid : Y.map e.hom.op a = a := by
      rw [Atom.iso_eq e (Iso.refl _)]
      exact Y.map_id_apply (op h.cellShape) a
    exact (congrArg (fun x => realize.map (h.cellShape.rdc.restrictIncl
      (h.cellShape.ogp.bdryFull ⊤)) ≫ (ofCell x).map) hid).symm.trans he
  · intro hF
    have key : ∀ (β : Bool) {B : MoleculeShape} (g : B.ogp ⟶ h.cellShape.ogp) [IsInclusion g]
        (hg : OGP.map g ⊤ ≤ h.cellShape.ogp.bdryFull ⊤) (b : PastingDiagram X)
        (hkb : restrictAlong h.sphere B g hg = b)
        (himg : OGP.map g ⊤ = h.cellShape.ogp.boundary ⊤ v.dim β),
        ((ofCell a).boundary v.dim β).Equiv (b.mapTo f) := by
      intro β B g _ hg b hkb himg
      subst hkb
      have E : RDCpx.ofInclusion (P := B.rdc) (Q := h.cellShape.rdc) g =
          RDCpx.ofInclusion (P := B.rdc)
            (Q := h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤))
            (codRestrict g _ fun x => hg ⟨x, LowerSet.mem_top, rfl⟩) ≫
            h.cellShape.rdc.restrictIncl (h.cellShape.ogp.bdryFull ⊤) := by
        ext x
        rfl
      refine equiv_of_emb_of_image_eq (ofCell a).map
        (h.cellShape.boundaryIncl v.dim β) g rfl ?_
        ((h.cellShape.map_boundaryIncl_top _ _).trans himg.symm)
      exact (congrArg (fun t => realize.map t ≫ (ofCell a).map) E).trans
        ((realize.map_comp_assoc _ _ _).trans
          ((congrArg (realize.map _ ≫ ·) hF).trans (Category.assoc _ _ _).symm))
    exact
      { dim_eq := h.dimension_cellShape
        dim_eq_dim := h.1
        source := key false (h.cellShapeEmb false) _ _ (h.restrictAlong_sphere false)
          (h.map_cellShapeEmb false)
        target := key true (h.cellShapeEmb true) _ _ (h.restrictAlong_sphere true)
          (h.map_cellShapeEmb true) }

theorem exists_iso_hasRoundType (f : X ⟶ Y) {H : Atom} (x : diagram Y H)
    (hx : HasRoundType (PastingDiagram.ofCell x) ⟨v.toPastingDiagram.mapTo f, v.isRound⟩
      ⟨w.toPastingDiagram.mapTo f, w.isRound⟩) :
    ∃ e : h.cellShape ≅ H, HasRoundType (PastingDiagram.ofCell (Y.map e.hom.op x))
      ⟨v.toPastingDiagram.mapTo f, v.isRound⟩ ⟨w.toPastingDiagram.mapTo f, w.isRound⟩ :=
  (h.exists_iso_extends_of_hasRoundType f x hx).imp fun _ he =>
    (h.hasRoundType_ofCell_iff f _).2 he

end Parallel

structure CellularExtensionData (X : DiagSet.{u}) where
  ι : Type u
  source : ι → RoundPastingDiagram X
  target : ι → RoundPastingDiagram X
  parallel : ∀ e, Parallel (source e) (target e)

namespace CellularExtensionData

variable (c : CellularExtensionData X)

noncomputable abbrev shape (e : c.ι) : Atom := (c.parallel e).cellShape

theorem dimension_shape (e : c.ι) : (c.shape e).dimension = (c.source e).dim + 1 :=
  (c.parallel e).dimension_cellShape

noncomputable def attach :
    (∐ fun e => realize.{u}.obj
      ((c.shape e).toMoleculeShape.rdc.restrict ((c.shape e).ogp.bdryFull ⊤))) ⟶ X :=
  Sigma.desc (f := fun e => realize.obj
      ((c.shape e).toMoleculeShape.rdc.restrict ((c.shape e).ogp.bdryFull ⊤)))
    fun e => (c.parallel e).sphere

noncomputable def bdryInclSigma :
    (∐ fun e => realize.{u}.obj
      ((c.shape e).toMoleculeShape.rdc.restrict ((c.shape e).ogp.bdryFull ⊤))) ⟶
      ∐ fun e => realize.obj (c.shape e).toMoleculeShape.rdc :=
  Limits.Sigma.map fun e =>
    realize.map ((c.shape e).toMoleculeShape.rdc.restrictIncl ((c.shape e).ogp.bdryFull ⊤))

noncomputable abbrev extension : DiagSet.{u} := pushout c.attach c.bdryInclSigma

noncomputable def incl : X ⟶ c.extension := pushout.inl c.attach c.bdryInclSigma

instance mono_incl : Mono c.incl := by
  have : ∀ e, Mono (realize.map
      ((c.shape e).toMoleculeShape.rdc.restrictIncl ((c.shape e).ogp.bdryFull ⊤))) := fun e =>
    mono_realize_map _ Subtype.val_injective
  have hm : Mono c.bdryInclSigma := inferInstanceAs
    (Mono (Limits.Sigma.map fun e => realize.map
      ((c.shape e).toMoleculeShape.rdc.restrictIncl ((c.shape e).ogp.bdryFull ⊤))))
  exact (MorphismProperty.monomorphisms _).of_isPushout (IsPushout.of_hasPushout _ _) hm

noncomputable def cell (e : c.ι) : diagram c.extension (c.shape e) :=
  uliftYonedaEquiv ((realizeAtomIso (c.shape e)).inv ≫
    Sigma.ι (fun e => realize.obj (c.shape e).toMoleculeShape.rdc) e ≫
      pushout.inr c.attach c.bdryInclSigma)

theorem ofCell_cell_map (e : c.ι) :
    (ofCell (c.cell e)).map = Sigma.ι (fun e => realize.obj (c.shape e).toMoleculeShape.rdc) e ≫
      pushout.inr c.attach c.bdryInclSigma :=
  (congrArg ((realizeAtomIso (c.shape e)).hom ≫ ·) (uliftYonedaEquiv.symm_apply_apply _)).trans
    ((realizeAtomIso (c.shape e)).hom_inv_id_assoc _)

theorem realize_map_restrictIncl_comp_ofCell_cell_map (e : c.ι) :
    realize.map ((c.shape e).toMoleculeShape.rdc.restrictIncl ((c.shape e).ogp.bdryFull ⊤)) ≫
        (ofCell (c.cell e)).map =
      (c.parallel e).sphere ≫ c.incl := by
  have hc := Sigma.ι (fun e => realize.obj
      ((c.shape e).toMoleculeShape.rdc.restrict ((c.shape e).ogp.bdryFull ⊤))) e ≫=
    pushout.condition (f := c.attach) (g := c.bdryInclSigma)
  simp only [attach, bdryInclSigma, Sigma.ι_desc_assoc, Limits.Sigma.ι_map_assoc] at hc
  rw [c.ofCell_cell_map e]
  exact hc.symm

theorem hasRoundType_cell (e : c.ι) :
    HasRoundType (PastingDiagram.ofCell (c.cell e))
      ⟨(c.source e).toPastingDiagram.mapTo c.incl, (c.source e).isRound⟩
      ⟨(c.target e).toPastingDiagram.mapTo c.incl, (c.target e).isRound⟩ :=
  ((c.parallel e).hasRoundType_ofCell_iff c.incl (c.cell e)).2
    (c.realize_map_restrictIncl_comp_ofCell_cell_map e)

theorem hasRoundType_app_cell (φ : c.extension ⟶ Y) (e : c.ι) :
    HasRoundType (PastingDiagram.ofCell (φ.app _ (c.cell e))) ((c.source e).mapTo (c.incl ≫ φ))
      ((c.target e).mapTo (c.incl ≫ φ)) := by
  have h := (c.hasRoundType_cell e).mapTo φ
  rw [← PastingDiagram.ofCell_app] at h
  have hm (u : RoundPastingDiagram X) : u.mapTo (c.incl ≫ φ) =
      RoundPastingDiagram.mapTo ⟨u.toPastingDiagram.mapTo c.incl, u.isRound⟩ φ :=
    RoundPastingDiagram.ext (PastingDiagram.mapTo_comp _ _ _)
  rw [hm, hm]
  exact h

noncomputable def desc {Y : DiagSet.{u}} (f : X ⟶ Y) (g : ∀ e, diagram Y (c.shape e))
    (hg : ∀ e, HasRoundType (PastingDiagram.ofCell (g e))
      ⟨(c.source e).toPastingDiagram.mapTo f, (c.source e).isRound⟩
      ⟨(c.target e).toPastingDiagram.mapTo f, (c.target e).isRound⟩) :
    c.extension ⟶ Y :=
  pushout.desc f (Sigma.desc (f := fun e => realize.obj (c.shape e).toMoleculeShape.rdc)
      fun e => (realizeAtomIso (c.shape e)).hom ≫ uliftYonedaEquiv.symm (g e)) (by
    refine Sigma.hom_ext _ _ fun e => ?_
    simp only [attach, bdryInclSigma, Sigma.ι_desc_assoc, Limits.Sigma.ι_map_assoc, Sigma.ι_desc]
    exact (((c.parallel e).hasRoundType_ofCell_iff f (g e)).1 (hg e)).symm)

variable {Y : DiagSet.{u}} (f : X ⟶ Y) (g : ∀ e, diagram Y (c.shape e))
  (hg : ∀ e, HasRoundType (PastingDiagram.ofCell (g e))
    ⟨(c.source e).toPastingDiagram.mapTo f, (c.source e).isRound⟩
    ⟨(c.target e).toPastingDiagram.mapTo f, (c.target e).isRound⟩)

@[reassoc (attr := simp)]
theorem incl_desc : c.incl ≫ c.desc f g hg = f :=
  pushout.inl_desc _ _ _

@[simp]
theorem desc_app_cell (e : c.ι) : (c.desc f g hg).app (op (c.shape e)) (c.cell e) = g e := by
  have hd : Sigma.ι (fun e => realize.obj (c.shape e).toMoleculeShape.rdc) e ≫
      pushout.inr c.attach c.bdryInclSigma ≫ c.desc f g hg =
        (realizeAtomIso (c.shape e)).hom ≫ uliftYonedaEquiv.symm (g e) := by
    rw [desc, pushout.inr_desc]
    exact Sigma.ι_desc _ e
  refine Eq.trans (b := uliftYonedaEquiv ((realizeAtomIso (c.shape e)).inv ≫
      Sigma.ι (fun e => realize.obj (c.shape e).toMoleculeShape.rdc) e ≫
        pushout.inr c.attach c.bdryInclSigma ≫ c.desc f g hg)) rfl ?_
  exact (congrArg (fun t => uliftYonedaEquiv ((realizeAtomIso (c.shape e)).inv ≫ t)) hd).trans
    ((congrArg uliftYonedaEquiv ((realizeAtomIso (c.shape e)).inv_hom_id_assoc
      (uliftYonedaEquiv.symm (g e)))).trans (uliftYonedaEquiv.apply_symm_apply _))

theorem hom_ext {h h' : c.extension ⟶ Y} (h₁ : c.incl ≫ h = c.incl ≫ h')
    (h₂ : ∀ e, h.app (op (c.shape e)) (c.cell e) = h'.app (op (c.shape e)) (c.cell e)) :
    h = h' := by
  refine pushout.hom_ext h₁ (Sigma.hom_ext _ _ fun e => ?_)
  have he : uliftYonedaEquiv ((realizeAtomIso (c.shape e)).inv ≫
      Sigma.ι (fun e => realize.obj (c.shape e).toMoleculeShape.rdc) e ≫
        pushout.inr c.attach c.bdryInclSigma ≫ h) =
      uliftYonedaEquiv ((realizeAtomIso (c.shape e)).inv ≫
        Sigma.ι (fun e => realize.obj (c.shape e).toMoleculeShape.rdc) e ≫
          pushout.inr c.attach c.bdryInclSigma ≫ h') :=
    h₂ e
  exact (cancel_epi (realizeAtomIso (c.shape e)).inv).1 (uliftYonedaEquiv.injective he)

end CellularExtensionData

theorem ofCell_app_map {Y : DiagSet.{u}} (f : X ⟶ Y) {U : Atom} (x : diagram X U) :
    ((ofCell (f.app (op U) x)).map : realize.obj U.toMoleculeShape.rdc ⟶ Y) =
      ((ofCell x).map ≫ f : realize.obj U.toMoleculeShape.rdc ⟶ Y) :=
  (congrArg ((realizeAtomIso U).hom ≫ ·)
    (uliftYonedaEquiv_symm_comp x f).symm).trans (Category.assoc _ _ _).symm

namespace CellularExtensionData

variable (c : CellularExtensionData X)

theorem exists_incl_app_eq_map_cell {V : Atom} (e : c.ι) (g : V ⟶ c.shape e)
    (hg : g V.top ≠ (c.shape e).top) :
    ∃ y, c.incl.app (op V) y = c.extension.map g.op (c.cell e) := by
  have hmem : ∀ t, ConcreteCategory.hom (atomToRDCpx.map g).hom t ∈
      (c.shape e).ogp.bdryFull ⊤ := fun t =>
    ((c.shape e).mem_bdryFull_top_iff _).2 fun ht =>
      hg (le_antisymm ((c.shape e).le_top _)
        (ht.symm.le.trans ((Atom.isMap g).monotone (V.le_top t))))
  refine ⟨(c.parallel e).sphere.app (op V)
    ⟨restrictLift (c.shape e).toMoleculeShape.rdc _ (atomToRDCpx.map g) hmem⟩, ?_⟩
  exact (congrArg (fun φ => φ.app (op V)
    ⟨restrictLift (c.shape e).toMoleculeShape.rdc _ (atomToRDCpx.map g) hmem⟩)
    (c.realize_map_restrictIncl_comp_ofCell_cell_map e)).symm

private def cellsSubfunctor : Subfunctor c.extension where
  obj V := {x | (∃ y, c.incl.app V y = x) ∨
    ∃ (e : c.ι) (g : V.unop ⟶ c.shape e), c.extension.map g.op (c.cell e) = x}
  map {V W} i := by
    rintro x (⟨y, rfl⟩ | ⟨e, g, rfl⟩)
    · exact Or.inl ⟨X.map i y, NatTrans.naturality_apply c.incl i y⟩
    · exact Or.inr ⟨e, i.unop ≫ g, Functor.map_comp_apply c.extension g.op i (c.cell e)⟩

theorem exists_incl_app_eq_or_exists_map_cell_eq {V : Atom} (x : diagram c.extension V) :
    (∃ y, c.incl.app (op V) y = x) ∨ ∃ (e : c.ι) (g : V ⟶ c.shape e),
      g V.top = (c.shape e).top ∧ c.extension.map g.op (c.cell e) = x := by
  let S := cellsSubfunctor c
  have hinc : Subfunctor.range c.incl ≤ S := by
    rintro V _ ⟨y, rfl⟩
    exact Or.inl ⟨y, rfl⟩
  have hcell : ∀ e, Subfunctor.range (Sigma.ι (fun e => realize.obj
      (c.shape e).toMoleculeShape.rdc) e ≫ pushout.inr c.attach c.bdryInclSigma) ≤ S := by
    rintro e V _ ⟨⟨y⟩, rfl⟩
    refine Or.inr ⟨e, InducedCategory.homMk y, ?_⟩
    rw [← c.ofCell_cell_map e]
    rfl
  let r : c.extension ⟶ S.toFunctor := pushout.desc (Subfunctor.lift c.incl hinc)
    (Sigma.desc fun e => Subfunctor.lift _ (hcell e)) (by
      rw [← cancel_mono S.ι]
      refine Sigma.hom_ext _ _ fun e => ?_
      have hc := Sigma.ι (fun e => realize.obj
          ((c.shape e).toMoleculeShape.rdc.restrict ((c.shape e).ogp.bdryFull ⊤))) e ≫=
        pushout.condition (f := c.attach) (g := c.bdryInclSigma)
      simp only [Category.assoc, Subfunctor.lift_ι, bdryInclSigma, Limits.Sigma.ι_map_assoc,
        Sigma.ι_desc_assoc] at hc ⊢
      exact hc)
  have hr : r ≫ S.ι = 𝟙 _ := by
    refine pushout.hom_ext ?_ (Sigma.hom_ext _ _ fun e => ?_)
    · rw [pushout.inl_desc_assoc, Subfunctor.lift_ι, Category.comp_id]
      rfl
    · rw [pushout.inr_desc_assoc, Sigma.ι_desc_assoc, Subfunctor.lift_ι, Category.comp_id]
  have hx : x ∈ S.obj (op V) := by
    have h : (r.app (op V) x).1 = x :=
      congrArg (fun φ : c.extension ⟶ c.extension => φ.app (op V) x) hr
    exact h ▸ (r.app (op V) x).2
  rcases hx with hx | ⟨e, g, rfl⟩
  · exact Or.inl hx
  · by_cases hg : g V.top = (c.shape e).top
    · exact Or.inr ⟨e, g, hg, rfl⟩
    · exact Or.inl (c.exists_incl_app_eq_map_cell e g hg)

variable (e : c.ι)

private theorem ofInclusion_cellShapeEmb_comp_ofCell_cell (α : Bool) :
    realize.map (RDCpx.ofInclusion (P := (cond α (c.target e).shape (c.source e).shape).rdc)
        (Q := (c.shape e).toMoleculeShape.rdc) ((c.parallel e).cellShapeEmb α)) ≫
      (ofCell (c.cell e)).map =
    (restrictAlong (c.parallel e).sphere _ ((c.parallel e).cellShapeEmb α)
      ((c.parallel e).map_cellShapeEmb_le_bdryFull α)).map ≫ c.incl := by
  have h : RDCpx.ofInclusion (P := (cond α (c.target e).shape (c.source e).shape).rdc)
      (Q := (c.shape e).toMoleculeShape.rdc) ((c.parallel e).cellShapeEmb α) =
      RDCpx.ofInclusion (P := (cond α (c.target e).shape (c.source e).shape).rdc)
        (Q := (c.shape e).toMoleculeShape.rdc.restrict ((c.shape e).ogp.bdryFull ⊤))
        (codRestrict ((c.parallel e).cellShapeEmb α) _ fun x =>
          (c.parallel e).map_cellShapeEmb_le_bdryFull α ⟨x, LowerSet.mem_top, rfl⟩) ≫
        (c.shape e).toMoleculeShape.rdc.restrictIncl ((c.shape e).ogp.bdryFull ⊤) := by
    ext x
    rfl
  exact (congrArg (fun t => realize.map t ≫ (ofCell (c.cell e)).map) h).trans
    ((realize.map_comp_assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (c.realize_map_restrictIncl_comp_ofCell_cell_map e)).trans
        (Category.assoc _ _ _).symm))

theorem ofInclusion_cellShapeEmb_false_comp_ofCell_cell :
    realize.map (RDCpx.ofInclusion (P := (c.source e).shape.rdc)
        (Q := (c.shape e).toMoleculeShape.rdc) ((c.parallel e).cellShapeEmb false)) ≫
      (ofCell (c.cell e)).map = (c.source e).map ≫ c.incl := by
  obtain ⟨-, hm⟩ := PastingDiagram.mk.inj ((c.parallel e).restrictAlong_sphere false)
  exact (c.ofInclusion_cellShapeEmb_comp_ofCell_cell e false).trans
    (congrArg (· ≫ c.incl) (eq_of_heq hm))

theorem ofInclusion_cellShapeEmb_true_comp_ofCell_cell :
    realize.map (RDCpx.ofInclusion (P := (c.target e).shape.rdc)
        (Q := (c.shape e).toMoleculeShape.rdc) ((c.parallel e).cellShapeEmb true)) ≫
      (ofCell (c.cell e)).map = (c.target e).map ≫ c.incl := by
  obtain ⟨-, hm⟩ := PastingDiagram.mk.inj ((c.parallel e).restrictAlong_sphere true)
  exact (c.ofInclusion_cellShapeEmb_comp_ofCell_cell e true).trans
    (congrArg (· ≫ c.incl) (eq_of_heq hm))

theorem cell_cases {V : Atom} (y : diagram c.extension V) :
    (∃ x, c.incl.app (op V) x = y) ∨ IsDegenerate c.extension y ∨
      ∃ (e : c.ι) (f : V ≅ c.shape e), c.extension.map f.hom.op (c.cell e) = y := by
  have hc := isColimitOfPreserves ((evaluation Atomᵒᵖ (Type u)).obj (op V))
    (pushoutIsPushout c.attach c.bdryInclSigma)
  obtain ⟨j, z, hz⟩ := Types.jointly_surjective_of_isColimit hc y
  rcases j with _ | _ | _
  · exact Or.inl ⟨c.attach.app _ z, hz⟩
  · exact Or.inl ⟨z, hz⟩
  have hc' := isColimitOfPreserves ((evaluation Atomᵒᵖ (Type u)).obj (op V))
    (colimit.isColimit (Discrete.functor fun e => realize.obj (c.shape e).toMoleculeShape.rdc))
  obtain ⟨⟨e⟩, ⟨w⟩, rfl⟩ := Types.jointly_surjective_of_isColimit hc' z
  obtain ⟨g, rfl⟩ : ∃ g : V ⟶ c.shape e, atomToRDCpx.map g = w := ⟨InducedCategory.homMk w, rfl⟩
  have hy : c.extension.map g.op (c.cell e) = y :=
    (ofCell_map_app_map (c.cell e) g).symm.trans
      ((congrArg (fun φ => φ.app (op V) ⟨atomToRDCpx.map g⟩) (c.ofCell_cell_map e)).trans hz)
  by_cases ht : g V.top = (c.shape e).top
  · have hcol := isCollapseHom_of_apply_eq_top g ht
    by_cases hd : V.dimension = (c.shape e).dimension
    · have := isIso_of_isCollapseHom_of_dimension_eq _ hcol hd
      exact Or.inr (Or.inr ⟨e, asIso g, hy⟩)
    · exact Or.inr (Or.inl ⟨c.shape e, g, c.cell e, hcol,
        fun hi => hd (Atom.dimension_eq_of_iso (@asIso _ _ _ _ _ hi)), hy⟩)
  · have hv : ∀ t, ConcreteCategory.hom (atomToRDCpx.map g).hom t ∈
        (c.shape e).ogp.bdryFull ⊤ := fun t =>
      ((c.shape e).ogp.bdryFull ⊤).lower ((Atom.isMap g).monotone (V.le_top t))
        (((c.shape e).mem_bdryFull_top_iff _).2 ht)
    have hww : restrictLift (c.shape e).toMoleculeShape.rdc _ (atomToRDCpx.map g) hv ≫
        (c.shape e).toMoleculeShape.rdc.restrictIncl ((c.shape e).ogp.bdryFull ⊤) =
          atomToRDCpx.map g := by
      ext
      rfl
    refine Or.inl ⟨(Sigma.ι _ e ≫ c.attach).app _
      ⟨restrictLift (c.shape e).toMoleculeShape.rdc _ (atomToRDCpx.map g) hv⟩, ?_⟩
    have hsq : Sigma.ι (fun e => realize.obj
          ((c.shape e).toMoleculeShape.rdc.restrict ((c.shape e).ogp.bdryFull ⊤))) e ≫
        c.attach ≫ c.incl =
      realize.map ((c.shape e).toMoleculeShape.rdc.restrictIncl ((c.shape e).ogp.bdryFull ⊤)) ≫
        Sigma.ι (fun e => realize.obj (c.shape e).toMoleculeShape.rdc) e ≫
          pushout.inr c.attach c.bdryInclSigma := by
      rw [incl, pushout.condition]
      exact Limits.Sigma.ι_map_assoc (fun e => realize.map
        ((c.shape e).toMoleculeShape.rdc.restrictIncl ((c.shape e).ogp.bdryFull ⊤))) e _
    refine (congrArg (fun φ => φ.app (op V)
      ⟨restrictLift (c.shape e).toMoleculeShape.rdc _ (atomToRDCpx.map g) hv⟩) hsq).trans ?_
    exact (congrArg (fun u => (Sigma.ι _ e ≫ pushout.inr c.attach c.bdryInclSigma).app (op V)
      ⟨u⟩) hww).trans hz

end CellularExtensionData

end Atoms.Diagrammatic
