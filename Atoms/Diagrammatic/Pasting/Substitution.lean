import Atoms.Diagrammatic.Pasting.Restriction
import Atoms.Molecule.Gluing.SubstitutionAlong

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape

universe u

namespace Atoms.Diagrammatic

def Parallel {X : DiagSet.{u}} (u v : RoundPastingDiagram X) : Prop :=
  u.dim = v.dim ∧ (u.dim = 0 ∨ ∀ α : Bool,
    (u.boundary (u.dim - 1) α).Equiv (v.boundary (v.dim - 1) α))

end Atoms.Diagrammatic

namespace Atoms.Diagrammatic.PastingDiagram

variable {X Y : DiagSet.{u}}

section ParallelBoundary

theorem exists_bdryIso_of_parallel {a b : RoundPastingDiagram X} (h : Parallel a b) :
    ∃ φ : a.shape.ogp.restrict (a.shape.ogp.bdryFull ⊤) ≅
        b.shape.ogp.restrict (b.shape.ogp.bdryFull ⊤), φ.IsSigned ∧
      realize.map (RDCpx.ofInclusion (P := a.shape.rdc.restrict (a.shape.ogp.bdryFull ⊤))
        (Q := b.shape.rdc) (φ.hom ≫ incl _)) ≫ b.map =
        realize.map (a.shape.rdc.restrictIncl (a.shape.ogp.bdryFull ⊤)) ≫ a.map := by
  rcases Nat.eq_zero_or_pos a.dim with h0 | hpos
  · exact ⟨MoleculeShape.bdryIsoOfPoints a.shape b.shape h0 (h.1.symm.trans h0),
      MoleculeShape.isSigned_bdryIsoOfPoints _ _ _ _,
      hom_ext_realize_of_isEmpty (C := a.shape.rdc.restrict (a.shape.ogp.bdryFull ⊤))
        (a.shape.isEmpty_bdryFull h0) _ _⟩
  have hE : ∀ α, (a.boundary (a.dim - 1) α).Equiv (b.boundary (a.dim - 1) α) := fun α => by
    have h' := h.2.resolve_left hpos.ne' α
    rwa [← h.1] at h'
  have hda : a.shape.dimension = a.dim - 1 + 1 := by rw [← dim_def]; omega
  have hdb : b.shape.dimension = a.dim - 1 + 1 := by rw [← dim_def, ← h.1]; omega
  let ψ : ∀ α, (a.shape.boundary (a.dim - 1) α).ogp ≅ (b.shape.boundary (a.dim - 1) α).ogp :=
    fun α => (hE α).iso
  let φ := MoleculeShape.bdryIsoOfParallel a.shape b.shape ψ a.isRound b.isRound hda hdb
  let i : ∀ α, (a.shape.boundary (a.dim - 1) α).ogp ⟶
      a.shape.ogp.restrict (a.shape.ogp.bdryFull ⊤) :=
    fun α => toBdryFull ((a.shape.bdryIso hda α).hom ≫ incl _) (map_hom_incl_top _)
  have hφ : ∀ α, RDCpx.ofInclusion (P := (a.shape.boundary (a.dim - 1) α).rdc)
      (Q := a.shape.rdc.restrict (a.shape.ogp.bdryFull ⊤)) (i α) ≫
        RDCpx.ofInclusion (P := a.shape.rdc.restrict (a.shape.ogp.bdryFull ⊤)) (Q := b.shape.rdc)
          (φ.hom ≫ incl _) =
      (RDCpx.isoOfIso (P := (a.shape.boundary (a.dim - 1) α).rdc)
        (Q := (b.shape.boundary (a.dim - 1) α).rdc) (ψ α)).hom ≫
          b.shape.boundaryInclRDC (a.dim - 1) α := by
    intro α
    ext x
    exact congrArg Subtype.val (ConcreteCategory.congr_hom
      (MoleculeShape.toBdryFull_bdryIsoOfParallel_hom a.shape b.shape ψ a.isRound b.isRound
        hda hdb α) x)
  have side : ∀ α, realize.map (RDCpx.ofInclusion (P := (a.shape.boundary (a.dim - 1) α).rdc)
      (Q := a.shape.rdc.restrict (a.shape.ogp.bdryFull ⊤)) (i α)) ≫
        realize.map (RDCpx.ofInclusion (P := a.shape.rdc.restrict (a.shape.ogp.bdryFull ⊤))
          (Q := b.shape.rdc) (φ.hom ≫ incl _)) ≫ b.map =
      realize.map (RDCpx.ofInclusion (P := (a.shape.boundary (a.dim - 1) α).rdc)
        (Q := a.shape.rdc.restrict (a.shape.ogp.bdryFull ⊤)) (i α)) ≫
          realize.map (a.shape.rdc.restrictIncl (a.shape.ogp.bdryFull ⊤)) ≫ a.map := fun α =>
    calc _ = realize.map (RDCpx.isoOfIso (P := (a.shape.boundary (a.dim - 1) α).rdc)
          (Q := (b.shape.boundary (a.dim - 1) α).rdc) (ψ α)).hom ≫
            (b.boundary (a.dim - 1) α).map := by
          rw [← realize.map_comp_assoc, hφ, realize.map_comp_assoc]
          rfl
      _ = (a.boundary (a.dim - 1) α).map := (hE α).map_comm
      _ = _ := by
          rw [← realize.map_comp_assoc]
          rfl
  exact ⟨φ, MoleculeShape.isSigned_bdryIsoOfParallel _ _ _ _ _ _ _,
    hom_ext_cover (R := a.shape.rdc.restrict (a.shape.ogp.bdryFull ⊤))
      (U := (a.shape.boundary (a.dim - 1) false).rdc)
      (V := (a.shape.boundary (a.dim - 1) true).rdc) (i false) (i true)
      (map_toBdryFull_sup _ _) (side false) (side true)⟩

end ParallelBoundary

section Substitute

variable (u : PastingDiagram X) {v : PastingDiagram X} (ι : Within v u)
  (hι : u.shape.ogp.IsRewritableSubmolecule (OGP.map ι.emb ⊤) ⊤)
  (w : RoundPastingDiagram X)
  (hw : Parallel ⟨v, ι.round_image_iff.1 hι.isRound⟩ w)

noncomputable def substBdryIso :
    v.shape.ogp.restrict (v.shape.ogp.bdryFull ⊤) ≅
      w.shape.ogp.restrict (w.shape.ogp.bdryFull ⊤) :=
  (exists_bdryIso_of_parallel hw).choose

theorem isSigned_substBdryIso : (substBdryIso u ι hι w hw).IsSigned :=
  (exists_bdryIso_of_parallel hw).choose_spec.1

theorem realize_map_ofInclusion_substBdryIso :
    realize.map (RDCpx.ofInclusion (P := v.shape.rdc.restrict (v.shape.ogp.bdryFull ⊤))
      (Q := w.shape.rdc) ((substBdryIso u ι hι w hw).hom ≫ incl _)) ≫ w.map =
      realize.map (v.shape.rdc.restrictIncl (v.shape.ogp.bdryFull ⊤)) ≫ v.map :=
  (exists_bdryIso_of_parallel hw).choose_spec.2

include hw in
private theorem krullDim_eq_of_parallel : krullDim w.shape.ogp = krullDim u.shape.ogp := by
  rw [w.shape.krullDim_eq_dimension, u.shape.krullDim_eq_dimension]
  exact_mod_cast hw.1.symm.trans (ι.isRewritableSubmolecule_image_iff.1 hι).2.2

noncomputable def substShape : MoleculeShape :=
  .ofOGP (substitution hι (bdryIsoAlong ι.emb (substBdryIso u ι hι w hw)))
    (isMolecule_substitution hι _ w.shape.isMolecule w.isRound
      (krullDim_eq_of_parallel u ι hι w hw)
      (isSigned_bdryIsoAlong ι.emb (isSigned_substBdryIso u ι hι w hw)))

noncomputable def substShapeIso :
    substitution hι (bdryIsoAlong ι.emb (substBdryIso u ι hι w hw)) ≅
      (substShape u ι hι w hw).ogp :=
  FiniteOGP.ofOGPIso _

noncomputable def substInlEmb :
    u.shape.ogp.restrict hι.complement ⟶ (substShape u ι hι w hw).ogp :=
  substInl hι _ ≫ (substShapeIso u ι hι w hw).hom

instance : IsInclusion (substInlEmb u ι hι w hw) :=
  inferInstanceAs (IsInclusion (substInl hι _ ≫ (substShapeIso u ι hι w hw).hom))

noncomputable def substInrEmb : w.shape.ogp ⟶ (substShape u ι hι w hw).ogp :=
  substInr hι _ ≫ (substShapeIso u ι hι w hw).hom

instance : IsInclusion (substInrEmb u ι hι w hw) :=
  inferInstanceAs (IsInclusion (substInr hι _ ≫ (substShapeIso u ι hι w hw).hom))

theorem map_substInlEmb_sup_map_substInrEmb :
    OGP.map (substInlEmb u ι hι w hw) ⊤ ⊔ OGP.map (substInrEmb u ι hι w hw) ⊤ = ⊤ := by
  rw [substInlEmb, substInrEmb, map_comp, map_comp, ← map_sup,
    map_substInl_sup_map_substInr, map_top_of_isIso]

@[implicit_reducible] def substInlRDC : RDCpx.{0} :=
  u.shape.rdc.restrict hι.complement

def substInlMap : realize.obj (substInlRDC u ι hι) ⟶ X :=
  realize.map (u.shape.rdc.restrictIncl hι.complement) ≫ u.map

theorem coverCompatible_subst :
    CoverCompatible (R := (substShape u ι hι w hw).rdc) (U := substInlRDC u ι hι)
      (V := w.shape.rdc) (substInlEmb u ι hι w hw) (substInrEmb u ι hι w hw)
      (substInlMap u ι hι) w.map := by
  let φS := substBdryIso u ι hι w hw
  refine coverCompatible_of_emb _ _ _ _ (C := v.shape.rdc.restrict (v.shape.ogp.bdryFull ⊤))
    (substCorner ι.emb hι) (φS.hom ≫ incl _) (fun y => ?_) ?_ ?_
  · exact congrArg (substShapeIso u ι hι w hw).hom (substInl_substCorner ι.emb hι φS y)
  · have e := congrArg (OGP.map (substShapeIso u ι hι w hw).hom)
      (map_substCorner_comp_substInl ι.emb hι φS)
    simp only [map_inf, ← map_comp] at e
    rw [substInlEmb, substInrEmb, ← Category.assoc]
    exact e
  · have E : RDCpx.ofInclusion (P := v.shape.rdc.restrict (v.shape.ogp.bdryFull ⊤))
        (Q := substInlRDC u ι hι) (substCorner ι.emb hι) ≫
          u.shape.rdc.restrictIncl hι.complement =
        v.shape.rdc.restrictIncl (v.shape.ogp.bdryFull ⊤) ≫
          RDCpx.ofInclusion (P := v.shape.rdc) (Q := u.shape.rdc) ι.emb := by
      ext x
      exact ConcreteCategory.congr_hom (substCorner_incl ι.emb hι) x
    calc realize.map (RDCpx.ofInclusion (P := v.shape.rdc.restrict (v.shape.ogp.bdryFull ⊤))
          (Q := substInlRDC u ι hι) (substCorner ι.emb hι)) ≫ substInlMap u ι hι
        = realize.map (v.shape.rdc.restrictIncl (v.shape.ogp.bdryFull ⊤)) ≫
            realize.map (RDCpx.ofInclusion (P := v.shape.rdc) (Q := u.shape.rdc) ι.emb) ≫
              u.map := by
          rw [substInlMap, ← realize.map_comp_assoc, E, realize.map_comp_assoc]
      _ = realize.map (v.shape.rdc.restrictIncl (v.shape.ogp.bdryFull ⊤)) ≫ v.map := by
          rw [ι.comm]
      _ = _ := (realize_map_ofInclusion_substBdryIso u ι hι w hw).symm

end Substitute

@[implicit_reducible, simps]
noncomputable def substitute (u : PastingDiagram X) {v : PastingDiagram X} (ι : Within v u)
    (hι : u.shape.ogp.IsRewritableSubmolecule (OGP.map ι.emb ⊤) ⊤)
    (w : RoundPastingDiagram X)
    (hw : Parallel ⟨v, ι.round_image_iff.1 hι.isRound⟩ w) : PastingDiagram X :=
  ⟨substShape u ι hι w hw,
    coverDesc (R := (substShape u ι hι w hw).rdc) (U := substInlRDC u ι hι)
      (V := w.shape.rdc) (substInlEmb u ι hι w hw) (substInrEmb u ι hι w hw)
      (map_substInlEmb_sup_map_substInrEmb u ι hι w hw) (substInlMap u ι hι) w.map
      (coverCompatible_subst u ι hι w hw)⟩

noncomputable def Within.substitute {u v : PastingDiagram X} (ι : Within v u)
    (hι : u.shape.ogp.IsRewritableSubmolecule (OGP.map ι.emb ⊤) ⊤)
    (w : RoundPastingDiagram X)
    (hw : Parallel ⟨v, ι.round_image_iff.1 hι.isRound⟩ w) :
    Within w.toPastingDiagram (u.substitute ι hι w hw) :=
  ⟨substInrEmb u ι hι w hw,
    ofInclusion_coverDesc_right (R := (substShape u ι hι w hw).rdc) (U := substInlRDC u ι hι)
      (V := w.shape.rdc) _ _ (map_substInlEmb_sup_map_substInrEmb u ι hι w hw) _ _ _⟩

theorem Within.isRewritableSubmolecule_image_substitute {u v : PastingDiagram X}
    (ι : Within v u)
    (hι : u.shape.ogp.IsRewritableSubmolecule (OGP.map ι.emb ⊤) ⊤)
    (w : RoundPastingDiagram X) (hw : Parallel ⟨v, ι.round_image_iff.1 hι.isRound⟩ w) :
    (u.substitute ι hι w hw).shape.ogp.IsRewritableSubmolecule
      (Within.substitute ι hι w hw).image ⊤ := by
  have h := (isRewritableSubmolecule_map_iff (substShapeIso u ι hι w hw).hom _ ⊤).2
    (isRewritableSubmolecule_substInr hι _ w.shape.isMolecule w.isRound
      (krullDim_eq_of_parallel u ι hι w hw)
      (isSigned_bdryIsoAlong ι.emb (isSigned_substBdryIso u ι hι w hw)))
  rw [map_top_of_isIso (substShapeIso u ι hι w hw).hom, ← map_comp] at h
  exact h

section PasteAt

variable (P Q : PastingDiagram X) (k : ℕ) (α : Bool) {V : PastingDiagram X}
  (ι : Within V (Q.boundary k α))

def bdryOccurrence : V.shape.ogp ⟶ Q.shape.ogp :=
  ι.emb ≫ Q.shape.boundaryIncl k α

instance : IsInclusion (bdryOccurrence Q k α ι) :=
  inferInstanceAs (IsInclusion (ι.emb ≫ Q.shape.boundaryIncl k α))

theorem isSubmoleculeOf_bdryOccurrence
    (hι : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤) :
    Q.shape.ogp.IsSubmoleculeOf (OGP.map (bdryOccurrence Q k α ι) ⊤)
      (Q.shape.ogp.boundary ⊤ k α) := by
  have h := (isSubmoleculeOf_map_iff (Q.shape.boundaryIncl k α)).2 hι
  rwa [Within.image, ← map_comp, Q.shape.map_boundaryIncl_top] at h

variable (hι : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤)
  (h : (P.boundary k (!α)).Equiv V)

noncomputable def pasteAtIso :
    P.shape.ogp.restrict (P.shape.ogp.boundary ⊤ k (!α)) ≅
      Q.shape.ogp.restrict (OGP.map (bdryOccurrence Q k α ι) ⊤) :=
  P.shape.subIso (P.shape.isMolecule.boundary k (!α)) ≪≫ h.iso ≪≫
    isoRestrictOfFintype (bdryOccurrence Q k α ι) rfl

noncomputable def pasteAtShape : MoleculeShape :=
  .ofOGP (pastingAt (pasteAtIso P Q k α ι h))
    (isMolecule_pastingAt _ (isSubmoleculeOf_bdryOccurrence Q k α ι hι) P.shape.isMolecule
      Q.shape.isMolecule)

noncomputable def pasteAtShapeIso :
    pastingAt (pasteAtIso P Q k α ι h) ≅ (pasteAtShape P Q k α ι hι h).ogp :=
  FiniteOGP.ofOGPIso _

noncomputable def pasteAtInl : P.shape.ogp ⟶ (pasteAtShape P Q k α ι hι h).ogp :=
  glue.inl (pasteAtIso P Q k α ι h) ≫ (pasteAtShapeIso P Q k α ι hι h).hom

instance : IsInclusion (pasteAtInl P Q k α ι hι h) :=
  inferInstanceAs (IsInclusion (glue.inl _ ≫ (pasteAtShapeIso P Q k α ι hι h).hom))

noncomputable def pasteAtInr : Q.shape.ogp ⟶ (pasteAtShape P Q k α ι hι h).ogp :=
  glue.inr (pasteAtIso P Q k α ι h) ≫ (pasteAtShapeIso P Q k α ι hι h).hom

instance : IsInclusion (pasteAtInr P Q k α ι hι h) :=
  inferInstanceAs (IsInclusion (glue.inr _ ≫ (pasteAtShapeIso P Q k α ι hι h).hom))

theorem map_pasteAtInl_sup_map_pasteAtInr :
    OGP.map (pasteAtInl P Q k α ι hι h) ⊤ ⊔ OGP.map (pasteAtInr P Q k α ι hι h) ⊤ = ⊤ := by
  rw [pasteAtInl, pasteAtInr, map_comp, map_comp, ← map_sup, glue.map_inl_sup_map_inr,
    map_top_of_isIso]

theorem coverCompatible_pasteAt :
    CoverCompatible (R := (pasteAtShape P Q k α ι hι h).rdc) (U := P.shape.rdc) (V := Q.shape.rdc)
      (pasteAtInl P Q k α ι hι h) (pasteAtInr P Q k α ι hι h) P.map Q.map := by
  refine coverCompatible_of_emb _ _ _ _ (C := (P.shape.boundary k (!α)).rdc)
    (P.shape.boundaryIncl k (!α)) (h.iso.hom ≫ bdryOccurrence Q k α ι) (fun y => ?_) ?_ ?_
  · let e := P.shape.subIso (P.shape.isMolecule.boundary k (!α))
    refine congrArg (pasteAtShapeIso P Q k α ι hι h).hom
      (glue.inl_eq_inr_iff.2 ⟨(e.inv y).2, ?_⟩)
    exact congrArg (fun z => bdryOccurrence Q k α ι (h.iso.hom z)) (e.inv_hom_id_apply y)
  · have e := congrArg (OGP.map (pasteAtShapeIso P Q k α ι hι h).hom)
      (map_inl_boundary_pastingAt (pasteAtIso P Q k α ι h))
    rw [map_inf] at e
    simp only [pasteAtInl, pasteAtInr, map_comp, P.shape.map_boundaryIncl_top]
    exact e
  · have E : RDCpx.ofInclusion (P := (P.shape.boundary k (!α)).rdc) (Q := Q.shape.rdc)
        (h.iso.hom ≫ bdryOccurrence Q k α ι) =
        (RDCpx.isoOfIso (P := (P.boundary k (!α)).shape.rdc) (Q := V.shape.rdc) h.iso).hom ≫
          RDCpx.ofInclusion (P := V.shape.rdc) (Q := (Q.boundary k α).shape.rdc) ι.emb ≫
            Q.shape.boundaryInclRDC k α := by
      ext x
      rfl
    rw [E, realize.map_comp_assoc, realize.map_comp_assoc, ← boundary_map, ι.comm,
      h.map_comm]
    rfl

@[implicit_reducible, simps] noncomputable def pasteAtBoundary : PastingDiagram X :=
  ⟨pasteAtShape P Q k α ι hι h,
    coverDesc (R := (pasteAtShape P Q k α ι hι h).rdc) (U := P.shape.rdc) (V := Q.shape.rdc)
      (pasteAtInl P Q k α ι hι h) (pasteAtInr P Q k α ι hι h)
      (map_pasteAtInl_sup_map_pasteAtInr P Q k α ι hι h) P.map Q.map
      (coverCompatible_pasteAt P Q k α ι hι h)⟩

theorem ofInclusion_pasteAtInl_map :
    realize.map (RDCpx.ofInclusion (P := P.shape.rdc) (Q := (pasteAtShape P Q k α ι hι h).rdc)
      (pasteAtInl P Q k α ι hι h)) ≫ (pasteAtBoundary P Q k α ι hι h).map = P.map :=
  ofInclusion_coverDesc_left (R := (pasteAtShape P Q k α ι hι h).rdc) (U := P.shape.rdc)
    (V := Q.shape.rdc) _ _ (map_pasteAtInl_sup_map_pasteAtInr P Q k α ι hι h) _ _ _

theorem ofInclusion_pasteAtInr_map :
    realize.map (RDCpx.ofInclusion (P := Q.shape.rdc) (Q := (pasteAtShape P Q k α ι hι h).rdc)
      (pasteAtInr P Q k α ι hι h)) ≫ (pasteAtBoundary P Q k α ι hι h).map = Q.map :=
  ofInclusion_coverDesc_right (R := (pasteAtShape P Q k α ι hι h).rdc) (U := P.shape.rdc)
    (V := Q.shape.rdc) _ _ (map_pasteAtInl_sup_map_pasteAtInr P Q k α ι hι h) _ _ _

end PasteAt

end Atoms.Diagrammatic.PastingDiagram
