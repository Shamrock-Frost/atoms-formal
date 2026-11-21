import Atoms.Diagrammatic.GrayTensor.Realization
import Atoms.Diagrammatic.Context.Pasting
import Atoms.Molecule.Construction.GrayProductHorn
import Atoms.Molecule.MoleculeShape.GrayProduct

open CategoryTheory Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

@[implicit_reducible]
noncomputable def PastingDiagram.grayTensor (u : PastingDiagram X) (v : PastingDiagram Y) :
    PastingDiagram (grayTensor X Y) where
  shape := u.shape.grayProduct v.shape
  map := realize.map (RDCpx.isoOfIso (P := (u.shape.grayProduct v.shape).rdc)
      (Q := grayProductRDC u.shape.rdc v.shape.rdc) (u.shape.grayProductIso v.shape).symm).hom ≫
    (realizeGrayProductIso u.shape.rdc v.shape.rdc).hom ≫ grayTensorBifunctor.map (u.map, v.map)

namespace PastingDiagram

@[simp] theorem shape_grayTensor (u : PastingDiagram X) (v : PastingDiagram Y) :
    (u.grayTensor v).shape = u.shape.grayProduct v.shape :=
  rfl

theorem dim_grayTensor (u : PastingDiagram X) (v : PastingDiagram Y) :
    (u.grayTensor v).dim = u.dim + v.dim :=
  u.shape.dimension_grayProduct v.shape

theorem isRound_grayTensor {u : PastingDiagram X} {v : PastingDiagram Y} (hu : u.IsRound)
    (hv : v.IsRound) : (u.grayTensor v).IsRound :=
  MoleculeShape.isRound_grayProduct hu hv

theorem grayTensor_map (u : PastingDiagram X) (v : PastingDiagram Y) :
    (u.grayTensor v).map =
      (realize.map (RDCpx.isoOfIso (P := (u.shape.grayProduct v.shape).rdc)
        (Q := grayProductRDC u.shape.rdc v.shape.rdc) (u.shape.grayProductIso v.shape).symm).hom ≫
      (realizeGrayProductIso u.shape.rdc v.shape.rdc).hom ≫
        grayTensorBifunctor.map (X := (realize.obj u.shape.rdc, realize.obj v.shape.rdc))
          (Y := (X, Y)) (u.map, v.map) : realize.obj (u.shape.grayProduct v.shape).rdc ⟶ _) :=
  rfl

theorem grayTensor_mapTo (u : PastingDiagram X) (v : PastingDiagram Y) {X' Y' : DiagSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (u.mapTo f).grayTensor (v.mapTo g) =
      (u.grayTensor v).mapTo (grayTensorBifunctor.map (f, g)) := by
  have h : grayTensorBifunctor.map (X := (realize.obj u.shape.rdc, realize.obj v.shape.rdc))
      (Y := (X', Y')) (u.map ≫ f, v.map ≫ g) =
      grayTensorBifunctor.map (X := (realize.obj u.shape.rdc, realize.obj v.shape.rdc))
        (Y := (X, Y)) (u.map, v.map) ≫
          grayTensorBifunctor.map (X := (X, Y)) (Y := (X', Y')) (f, g) :=
    grayTensorBifunctor.map_comp (X := (_, _)) (Y := (_, _)) (Z := (_, _)) (u.map, v.map) (f, g)
  rw [PastingDiagram.grayTensor, PastingDiagram.grayTensor, mapTo, mapTo, mapTo]
  congr 1
  rw [h, Category.assoc, Category.assoc]

private theorem hom_ext_realize_atom {Z : DiagSet.{u}} {U : Atom} {f g : realize.obj U.rdc ⟶ Z}
    (h : f.app (op U) ⟨𝟙 (atomToRDCpx.obj U)⟩ = g.app (op U) ⟨𝟙 (atomToRDCpx.obj U)⟩) : f = g := by
  rw [← cancel_epi (realizeAtomIso.{u} U).inv]
  exact uliftYonedaEquiv.injective h

private theorem ofCell_map_app_id {U : Atom} (z : diagram X U) :
    (ofCell z).map.app (op U) ⟨𝟙 (atomToRDCpx.obj U)⟩ = z := by
  have h := ofCell_map_app_map z (𝟙 U)
  rw [op_id, Functor.map_id_apply] at h
  exact h

theorem grayTensor_ofCell {U V : Atom} (x : diagram X U) (y : diagram Y V) :
    ((ofCell x).grayTensor (ofCell y)).Equiv (ofCell (grayTensorCell x y)) := by
  refine ⟨Iso.refl _, hom_ext_realize_atom (U := Atom.grayTensor U V) ?_⟩
  have h1 : 𝟙 (atomToRDCpx.obj (Atom.grayTensor U V)) ≫
      (RDCpx.isoOfIso (P := ((ofCell x).grayTensor (ofCell y)).shape.rdc)
        (Q := (ofCell (grayTensorCell x y)).shape.rdc) (Iso.refl _)).hom =
      𝟙 (atomToRDCpx.obj (Atom.grayTensor U V)) := by
    ext t
    rfl
  have h2 : 𝟙 (atomToRDCpx.obj (Atom.grayTensor U V)) ≫
      (RDCpx.isoOfIso (P := (U.toMoleculeShape.grayProduct V.toMoleculeShape).rdc)
        (Q := grayProductRDC U.rdc V.rdc)
        (U.toMoleculeShape.grayProductIso V.toMoleculeShape).symm).hom =
      grayProductCellMap (𝟙 (atomToRDCpx.obj U)) (𝟙 (atomToRDCpx.obj V)) := by
    ext t
    rfl
  refine (realize_map_comp_app _ _ _).trans ?_
  refine (congrArg (fun c => (ofCell (grayTensorCell x y)).map.app (op (Atom.grayTensor U V))
    (ULift.up c)) h1).trans ?_
  refine (ofCell_map_app_id _).trans ?_
  refine Eq.trans ?_ (realize_map_comp_app _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun c => ((realizeGrayProductIso.{u} U.rdc V.rdc).hom ≫
    _).app (op (Atom.grayTensor U V)) (ULift.up c)) h2).symm
  have h3 := realizeGrayProductIso_inv_app_grayTensorCell.{u} (𝟙 (atomToRDCpx.obj U))
    (𝟙 (atomToRDCpx.obj V))
  have h4 := ConcreteCategory.congr_hom
    ((realizeGrayProductIso.{u} U.rdc V.rdc).inv_hom_id_app (op (Atom.grayTensor U V)))
    (grayTensorCell (X := realize.{u}.obj U.rdc) (Y := realize.{u}.obj V.rdc)
      (ULift.up (𝟙 (atomToRDCpx.obj U))) (ULift.up (𝟙 (atomToRDCpx.obj V))))
  refine Eq.trans ?_ (congrArg (fun c => (grayTensorBifunctor.map _).app (op (Atom.grayTensor U V))
    ((realizeGrayProductIso.{u} U.rdc V.rdc).hom.app _ c)) h3)
  refine Eq.trans ?_ (congrArg (fun c => (grayTensorBifunctor.map _).app
    (op (Atom.grayTensor U V)) c) h4).symm
  refine Eq.trans ?_ (grayTensorCell_naturality _ _ _ _).symm
  exact congrArg₂ grayTensorCell (ofCell_map_app_id x).symm (ofCell_map_app_id y).symm

private theorem ofInclusion_grayProductMap_comp {A B M N : MoleculeShape} (e : A.ogp ⟶ M.ogp)
    (e' : B.ogp ⟶ N.ogp) [IsInclusion e] [IsInclusion e'] :
    RDCpx.ofInclusion (P := (A.grayProduct B).rdc) (Q := (M.grayProduct N).rdc)
        (MoleculeShape.grayProductMap e e') ≫
      (RDCpx.isoOfIso (P := (M.grayProduct N).rdc) (Q := grayProductRDC M.rdc N.rdc)
        (M.grayProductIso N).symm).hom =
    (RDCpx.isoOfIso (P := (A.grayProduct B).rdc) (Q := grayProductRDC A.rdc B.rdc)
        (A.grayProductIso B).symm).hom ≫
      grayProductRDCMap (RDCpx.ofInclusion (P := A.rdc) (Q := M.rdc) e)
        (RDCpx.ofInclusion (P := B.rdc) (Q := N.rdc) e') := by
  ext t
  exact (M.grayProductIso N).hom_inv_id_apply _

private theorem realize_map_ofInclusion_grayProductMap_comp {A B M N : MoleculeShape}
    (e : A.ogp ⟶ M.ogp) (e' : B.ogp ⟶ N.ogp) [IsInclusion e] [IsInclusion e']
    {fa : realize.obj A.rdc ⟶ X} {fb : realize.obj B.rdc ⟶ Y} {fm : realize.obj M.rdc ⟶ X}
    {fn : realize.obj N.rdc ⟶ Y}
    (he : realize.map (RDCpx.ofInclusion (P := A.rdc) (Q := M.rdc) e) ≫ fm = fa)
    (he' : realize.map (RDCpx.ofInclusion (P := B.rdc) (Q := N.rdc) e') ≫ fn = fb) :
    realize.map (RDCpx.ofInclusion (P := (A.grayProduct B).rdc) (Q := (M.grayProduct N).rdc)
        (MoleculeShape.grayProductMap e e')) ≫
      realize.map (RDCpx.isoOfIso (P := (M.grayProduct N).rdc) (Q := grayProductRDC M.rdc N.rdc)
        (M.grayProductIso N).symm).hom ≫ (realizeGrayProductIso M.rdc N.rdc).hom ≫
          grayTensorBifunctor.map (X := (realize.obj M.rdc, realize.obj N.rdc)) (Y := (X, Y))
            (fm, fn) =
    realize.map (RDCpx.isoOfIso (P := (A.grayProduct B).rdc) (Q := grayProductRDC A.rdc B.rdc)
        (A.grayProductIso B).symm).hom ≫ (realizeGrayProductIso A.rdc B.rdc).hom ≫
          grayTensorBifunctor.map (X := (realize.obj A.rdc, realize.obj B.rdc)) (Y := (X, Y))
            (fa, fb) := by
  have h := grayTensorBifunctor.map_comp (X := (realize.obj A.rdc, realize.obj B.rdc))
    (Y := (realize.obj M.rdc, realize.obj N.rdc)) (Z := (X, Y))
    (realize.map (RDCpx.ofInclusion (P := A.rdc) (Q := M.rdc) e),
      realize.map (RDCpx.ofInclusion (P := B.rdc) (Q := N.rdc) e')) (fm, fn)
  rw [← realize.map_comp_assoc, ofInclusion_grayProductMap_comp, realize.map_comp_assoc,
    realize_map_grayProductRDCMap_comp_realizeGrayProductIso_hom_assoc, ← h]
  subst he he'
  rfl

def Within.grayTensor {a m : PastingDiagram X} {b n : PastingDiagram Y} (w : Within a m)
    (w' : Within b n) : Within (a.grayTensor b) (m.grayTensor n) where
  emb := MoleculeShape.grayProductMap (P := a.shape) (Q := b.shape) w.emb w'.emb
  isInclusion := MoleculeShape.instIsInclusionGrayProductMap _ _
  comm := realize_map_ofInclusion_grayProductMap_comp w.emb w'.emb w.comm w'.comm

namespace Within

variable {a m : PastingDiagram X} {b n : PastingDiagram Y}

theorem image_grayTensor (w : Within a m) (w' : Within b n) :
    (w.grayTensor w').image =
      OGP.map (m.shape.grayProductIso n.shape).hom (w.image ×ˢ w'.image) :=
  MoleculeShape.map_grayProductMap_top w.emb w'.emb

theorem isSubmoleculeOf_image_grayTensor {w : Within a m} {w' : Within b n}
    (hw : m.shape.ogp.IsSubmoleculeOf w.image ⊤) (hw' : n.shape.ogp.IsSubmoleculeOf w'.image ⊤) :
    (m.grayTensor n).shape.ogp.IsSubmoleculeOf (w.grayTensor w').image ⊤ := by
  rw [image_grayTensor, ← map_top_of_isIso (m.shape.grayProductIso n.shape).hom,
    isSubmoleculeOf_map_iff, ← LowerSet.top_prod_top]
  exact (isSubmoleculeOf_prod_left hw hw'.isMoleculeIn).trans
    (isSubmoleculeOf_prod_right m.shape.isMolecule hw')

theorem isRewritableSubmolecule_image_grayTensor {w : Within a m} {w' : Within b n}
    (hw : m.shape.ogp.IsRewritableSubmolecule w.image ⊤)
    (hw' : n.shape.ogp.IsRewritableSubmolecule w'.image ⊤) :
    (m.grayTensor n).shape.ogp.IsRewritableSubmolecule (w.grayTensor w').image ⊤ := by
  rw [isRewritableSubmolecule_image_iff] at hw hw' ⊢
  exact ⟨isSubmoleculeOf_image_grayTensor hw.1 hw'.1, isRound_grayTensor hw.2.1 hw'.2.1, by
    rw [dim_grayTensor, dim_grayTensor, hw.2.2, hw'.2.2]⟩

theorem image_boundary_grayTensor (u : PastingDiagram X) (v : PastingDiagram Y) (n : ℕ)
    (α : Bool) :
    (boundary (u.grayTensor v) n α).image =
      OGP.map (u.shape.grayProductIso v.shape).hom (⨆ k ≤ n,
        u.shape.ogp.boundary ⊤ k α ×ˢ v.shape.ogp.boundary ⊤ (n - k) (xor k.bodd α)) := by
  rw [image_boundary, ← boundary_prod_of_isGlobular u.shape.isMolecule.isGlobular
    v.shape.isMolecule.isGlobular, LowerSet.top_prod_top, map_boundary,
    map_top_of_isIso]
  rfl

noncomputable def boundaryGrayTensor (u : PastingDiagram X) (v : PastingDiagram Y) {n k : ℕ}
    (hk : k ≤ n) (α : Bool) :
    Within ((u.boundary k α).grayTensor (v.boundary (n - k) (xor k.bodd α)))
      ((u.grayTensor v).boundary n α) :=
  ((boundary u k α).grayTensor (boundary v (n - k) (xor k.bodd α))).ofImageLE
    (boundary (u.grayTensor v) n α) (by
      rw [image_grayTensor, image_boundary, image_boundary, image_boundary_grayTensor]
      exact OGP.map_mono _ (le_iSup₂ (f := fun k _ => u.shape.ogp.boundary ⊤ k α ×ˢ
        v.shape.ogp.boundary ⊤ (n - k) (xor k.bodd α)) k hk))

theorem image_boundaryGrayTensor_trans (u : PastingDiagram X) (v : PastingDiagram Y) {n k : ℕ}
    (hk : k ≤ n) (α : Bool) :
    ((boundaryGrayTensor u v hk α).trans (boundary (u.grayTensor v) n α)).image =
      OGP.map (u.shape.grayProductIso v.shape).hom
        (u.shape.ogp.boundary ⊤ k α ×ˢ v.shape.ogp.boundary ⊤ (n - k) (xor k.bodd α)) := by
  rw [boundaryGrayTensor, image_ofImageLE_trans, image_grayTensor, image_boundary, image_boundary]

end Within

theorem Equiv.grayTensor {u u' : PastingDiagram X} {v v' : PastingDiagram Y} (hu : u.Equiv u')
    (hv : v.Equiv v') : (u.grayTensor v).Equiv (u'.grayTensor v') := by
  have h : ((Within.ofEquiv hu).grayTensor (Within.ofEquiv hv)).image = ⊤ := by
    rw [Within.image_grayTensor, Within.image_ofEquiv, Within.image_ofEquiv, LowerSet.top_prod_top,
      map_top_of_isIso]
  exact (((Within.ofEquiv hu).grayTensor (Within.ofEquiv hv)).equiv_restrictTo_of_eq h
    (u'.grayTensor v').shape.isMolecule).trans (equiv_restrictTo_univ _)

namespace Within

noncomputable def boundarySplitFst (u : PastingDiagram X) (v : PastingDiagram Y) (n j : ℕ)
    (α : Bool) : Within (((u.boundary j α).grayTensor v).boundary n α) (u.grayTensor v) :=
  (boundary _ n α).trans ((boundary u j α).grayTensor (refl v))

noncomputable def boundarySplitSnd (u : PastingDiagram X) (v : PastingDiagram Y) (n j : ℕ)
    (α : Bool) :
    Within ((u.grayTensor (v.boundary (n - j - 1) (xor (j + 1).bodd α))).boundary n α)
      (u.grayTensor v) :=
  (boundary _ n α).trans ((refl u).grayTensor (boundary v (n - j - 1) (xor (j + 1).bodd α)))

theorem image_boundarySplitFst (u : PastingDiagram X) (v : PastingDiagram Y) (n j : ℕ)
    (α : Bool) :
    (boundarySplitFst u v n j α).image = OGP.map (u.shape.grayProductIso v.shape).hom
      ((grayProduct _ _).boundary
        (u.shape.ogp.boundary ⊤ j α ×ˢ (⊤ : LowerSet v.shape.ogp)) n α) := by
  rw [boundarySplitFst, image_boundary_trans, image_grayTensor, image_boundary, image_refl,
    map_boundary]
  rfl

theorem image_boundarySplitSnd (u : PastingDiagram X) (v : PastingDiagram Y) (n j : ℕ)
    (α : Bool) :
    (boundarySplitSnd u v n j α).image = OGP.map (u.shape.grayProductIso v.shape).hom
      ((grayProduct _ _).boundary
        ((⊤ : LowerSet u.shape.ogp) ×ˢ
          v.shape.ogp.boundary ⊤ (n - j - 1) (xor (j + 1).bodd α)) n α) := by
  rw [boundarySplitSnd, image_boundary_trans, image_grayTensor, image_boundary, image_refl,
    map_boundary]
  rfl

theorem image_boundarySplitFst_sup (u : PastingDiagram X) (v : PastingDiagram Y) {n j : ℕ}
    (hj : j < n) (α : Bool) :
    (boundarySplitFst u v n j α).image ⊔ (boundarySplitSnd u v n j α).image =
      (boundary (u.grayTensor v) n α).image := by
  rw [image_boundarySplitFst, image_boundarySplitSnd, ← OGP.map_sup, ← boundary_prod_eq_sup
    u.shape.isMolecule.isGlobular v.shape.isMolecule.isGlobular hj, image_boundary,
    ← map_top_of_isIso (u.shape.grayProductIso v.shape).hom, map_boundary, LowerSet.top_prod_top]
  rfl

theorem isGenPastingIn_boundarySplit (u : PastingDiagram X) (v : PastingDiagram Y) {n j : ℕ}
    (hj : j < n) (α : Bool) :
    (u.grayTensor v).shape.ogp.IsGenPastingIn (n - 1)
      (_root_.cond α (boundarySplitSnd u v n j α).image (boundarySplitFst u v n j α).image)
      (_root_.cond α (boundarySplitFst u v n j α).image (boundarySplitSnd u v n j α).image) := by
  rw [image_boundarySplitFst, image_boundarySplitSnd, ← Bool.apply_cond (OGP.map _),
    ← Bool.apply_cond (OGP.map _)]
  refine OGP.IsGenPastingIn.map _ ?_
  exact isGenPastingIn_boundary_prod u.shape.isMolecule v.shape.isMolecule hj α

end Within

namespace Within

variable {m w u : PastingDiagram X} (ww : Within w m) (wu : Within u m) {k : ℕ} (α : Bool)
  (v : PastingDiagram Y) (ℓ : ℕ)

noncomputable def pastePiece :
    Within (w.grayTensor (v.boundary ℓ (xor (k + 1).bodd (!α)))) (m.grayTensor v) :=
  ww.grayTensor (boundary v ℓ (xor (k + 1).bodd (!α)))

noncomputable def pasteRest :
    Within ((u.grayTensor v).boundary (k + 1 + ℓ) (!α)) (m.grayTensor v) :=
  (boundary _ (k + 1 + ℓ) (!α)).trans (wu.grayTensor (refl v))

theorem image_pastePiece : (pastePiece ww (k := k) α v ℓ).image =
    OGP.map (m.shape.grayProductIso v.shape).hom
      (ww.image ×ˢ v.shape.ogp.boundary ⊤ ℓ (xor (k + 1).bodd (!α))) := by
  rw [pastePiece, image_grayTensor, image_boundary]

theorem image_pasteRest : (pasteRest wu (k := k) α v ℓ).image =
    OGP.map (m.shape.grayProductIso v.shape).hom
      ((grayProduct _ _).boundary (wu.image ×ˢ (⊤ : LowerSet v.shape.ogp)) (k + 1 + ℓ) (!α)) := by
  rw [pasteRest, image_boundary_trans, image_grayTensor, image_refl, map_boundary]
  rfl

variable {ww wu α}

theorem image_pastePiece_sup (hw : w.dim = k + 1)
    (hc : m.shape.ogp.IsPastingAtIn k α ww.image wu.image ⊤) :
    (pastePiece ww (k := k) α v ℓ).image ⊔ (pasteRest wu (k := k) α v ℓ).image =
      (boundary (m.grayTensor v) (k + 1 + ℓ) (!α)).image := by
  have hc' : m.shape.ogp.IsPastingAtIn k α ww.image wu.image (ww.image ⊔ wu.image) :=
    { hc with eq_sup := rfl }
  have hU' := hc'.isMoleculeIn
  rw [image_pastePiece, image_pasteRest, ← OGP.map_sup, ← boundary_prod_eq_prod_sup_of_le
    wu.isMoleculeIn_image.isGlobular hU'.isGlobular v.shape.isMolecule.isGlobular
    (fun i hi => by
      rcases hi.lt_or_eq with hi | rfl
      · rw [← hU'.isGlobular i k hi (!α) (!α), hc'.boundary_not,
          wu.isMoleculeIn_image.isGlobular i k hi (!α) (!α)]
      · exact hc'.boundary_not)
    (fun i hi => hc'.boundary_eq_sup_of_lt hi (by
      rw [ww.krullDim_image, hw]; exact_mod_cast hi) (!α)), ← hc.eq_sup, image_boundary,
    ← map_top_of_isIso (m.shape.grayProductIso v.shape).hom, map_boundary, LowerSet.top_prod_top]
  rfl

theorem isGenPastingIn_pastePiece_pasteRest (hw : w.dim = k + 1)
    (hc : m.shape.ogp.IsPastingAtIn k α ww.image wu.image ⊤) :
    (m.grayTensor v).shape.ogp.IsGenPastingIn (k + ℓ)
      (_root_.cond α (pasteRest wu (k := k) α v ℓ).image (pastePiece ww (k := k) α v ℓ).image)
      (_root_.cond α (pastePiece ww (k := k) α v ℓ).image (pasteRest wu (k := k) α v ℓ).image) := by
  rw [image_pastePiece, image_pasteRest, ← Bool.apply_cond (OGP.map _),
    ← Bool.apply_cond (OGP.map _)]
  exact OGP.IsGenPastingIn.map _ (isGenPastingIn_prod_pasteAt α ww.isMoleculeIn_image
    wu.isMoleculeIn_image v.shape.isMolecule (by rw [ww.krullDim_image, hw])
    { hc with eq_sup := rfl })

end Within

namespace Within

section Right

variable {m w v : PastingDiagram Y} (ww : Within w m) (wv : Within v m) {k : ℕ} (α : Bool)
  (u : PastingDiagram X) (ℓ : ℕ)

noncomputable def pastePieceRight :
    Within ((u.boundary ℓ (xor ℓ.bodd α)).grayTensor w) (u.grayTensor m) :=
  (boundary u ℓ (xor ℓ.bodd α)).grayTensor ww

noncomputable def pasteRestRight :
    Within ((u.grayTensor v).boundary (k + 1 + ℓ) (xor ℓ.bodd α)) (u.grayTensor m) :=
  (boundary _ (k + 1 + ℓ) (xor ℓ.bodd α)).trans ((refl u).grayTensor wv)

theorem image_pastePieceRight : (pastePieceRight ww α u ℓ).image =
    OGP.map (u.shape.grayProductIso m.shape).hom
      (u.shape.ogp.boundary ⊤ ℓ (xor ℓ.bodd α) ×ˢ ww.image) := by
  rw [pastePieceRight, image_grayTensor, image_boundary]

theorem image_pasteRestRight : (pasteRestRight wv (k := k) α u ℓ).image =
    OGP.map (u.shape.grayProductIso m.shape).hom ((grayProduct _ _).boundary
      ((⊤ : LowerSet u.shape.ogp) ×ˢ wv.image) (k + 1 + ℓ) (xor ℓ.bodd α)) := by
  rw [pasteRestRight, image_boundary_trans, image_grayTensor, image_refl, map_boundary]
  rfl

variable {ww wv α}

theorem image_pastePieceRight_sup (hw : w.dim = k + 1)
    (hc : m.shape.ogp.IsPastingAtIn k α ww.image wv.image ⊤) :
    (pastePieceRight ww α u ℓ).image ⊔ (pasteRestRight wv (k := k) α u ℓ).image =
      (boundary (u.grayTensor m) (k + 1 + ℓ) (xor ℓ.bodd α)).image := by
  rw [image_pastePieceRight, image_pasteRestRight, ← OGP.map_sup,
    ← boundary_prod_pasteAt_right u.shape.isMolecule (by rw [ww.krullDim_image, hw])
      { hc with eq_sup := rfl }, ← hc.eq_sup, image_boundary,
    ← map_top_of_isIso (u.shape.grayProductIso m.shape).hom, map_boundary, LowerSet.top_prod_top]
  rfl

theorem isGenPastingIn_pastePieceRight_pasteRestRight (hw : w.dim = k + 1)
    (hc : m.shape.ogp.IsPastingAtIn k α ww.image wv.image ⊤) :
    (u.grayTensor m).shape.ogp.IsGenPastingIn (k + ℓ)
      (_root_.cond (xor ℓ.bodd α) (pasteRestRight wv (k := k) α u ℓ).image
        (pastePieceRight ww α u ℓ).image)
      (_root_.cond (xor ℓ.bodd α) (pastePieceRight ww α u ℓ).image
        (pasteRestRight wv (k := k) α u ℓ).image) := by
  rw [image_pastePieceRight, image_pasteRestRight, ← Bool.apply_cond (OGP.map _),
    ← Bool.apply_cond (OGP.map _)]
  exact OGP.IsGenPastingIn.map _ (isGenPastingIn_prod_pasteAt_right α ww.isMoleculeIn_image
    wv.isMoleculeIn_image u.shape.isMolecule (by rw [ww.krullDim_image, hw])
    { hc with eq_sup := rfl })

end Right

theorem isGenPastingIn_refl_grayTensor {b b' v : PastingDiagram Y} {w : Within b v}
    {w' : Within b' v} {k : ℕ} (h : v.shape.ogp.IsGenPastingIn k w.image w'.image)
    (iA : w.image ⊓ v.shape.ogp.boundary (w.image ⊔ w'.image) k false ≤
      v.shape.ogp.boundary w.image k false)
    (iB : w'.image ⊓ v.shape.ogp.boundary (w.image ⊔ w'.image) k true ≤
      v.shape.ogp.boundary w'.image k true) (u : PastingDiagram X) :
    (u.grayTensor v).shape.ogp.IsGenPastingIn (k + u.dim)
      (_root_.cond u.dim.bodd ((refl u).grayTensor w').image ((refl u).grayTensor w).image)
      (_root_.cond u.dim.bodd ((refl u).grayTensor w).image ((refl u).grayTensor w').image) := by
  rw [image_grayTensor, image_grayTensor, image_refl, ← Bool.apply_cond (OGP.map _),
    ← Bool.apply_cond (OGP.map _)]
  exact OGP.IsGenPastingIn.map _ (isGenPastingIn_prod_right u.shape.isMolecule
    (by rw [LowerSet.krullDim_top, u.shape.krullDim_eq_dimension]; rfl) h iA iB)

theorem isGenPastingIn_grayTensor_refl {a a' u : PastingDiagram X} {w : Within a u}
    {w' : Within a' u} {k : ℕ} (h : u.shape.ogp.IsGenPastingIn k w.image w'.image)
    (iA : w.image ⊓ u.shape.ogp.boundary (w.image ⊔ w'.image) k false ≤
      u.shape.ogp.boundary w.image k false)
    (iB : w'.image ⊓ u.shape.ogp.boundary (w.image ⊔ w'.image) k true ≤
      u.shape.ogp.boundary w'.image k true) (v : PastingDiagram Y) :
    (u.grayTensor v).shape.ogp.IsGenPastingIn (k + v.dim) (w.grayTensor (refl v)).image
      (w'.grayTensor (refl v)).image := by
  rw [image_grayTensor, image_grayTensor, image_refl]
  exact OGP.IsGenPastingIn.map _ (isGenPastingIn_prod_left v.shape.isMolecule
    (by rw [LowerSet.krullDim_top, v.shape.krullDim_eq_dimension]; rfl) h iA iB)

theorem image_grayTensor_refl_sup {a a' u : PastingDiagram X} (w : Within a u) (w' : Within a' u)
    (hcov : w.image ⊔ w'.image = ⊤) (v : PastingDiagram Y) :
    (w.grayTensor (refl v)).image ⊔ (w'.grayTensor (refl v)).image = ⊤ := by
  rw [image_grayTensor, image_grayTensor, ← OGP.map_sup, ← LowerSet.sup_prod, hcov, image_refl,
    LowerSet.top_prod_top, map_top_of_isIso]

end Within

end PastingDiagram

noncomputable def RoundPastingDiagram.grayTensor (u : RoundPastingDiagram X)
    (v : RoundPastingDiagram Y) : RoundPastingDiagram (grayTensor X Y) :=
  ⟨u.toPastingDiagram.grayTensor v.toPastingDiagram,
    PastingDiagram.isRound_grayTensor u.isRound v.isRound⟩

@[simp] theorem RoundPastingDiagram.toPastingDiagram_grayTensor (u : RoundPastingDiagram X)
    (v : RoundPastingDiagram Y) :
    (u.grayTensor v).toPastingDiagram = u.toPastingDiagram.grayTensor v.toPastingDiagram :=
  rfl

end Atoms.Diagrammatic
