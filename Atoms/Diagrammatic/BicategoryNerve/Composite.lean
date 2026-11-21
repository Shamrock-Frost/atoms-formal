import Atoms.Diagrammatic.BicategoryNerve.Basic
import Atoms.Diagrammatic.Pasting.Paste

open CategoryTheory Opposite Order Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape
open CategoryTheory.Bicategory (PathCell pathComp pathComp_mapPath)
open CategoryTheory.FreeBicategory (lift IsStructural)
open scoped CategoryTheory.Bicategory

universe w v u u₂ v₂

namespace Atoms.Diagrammatic.PastingDiagram

variable {B : Type u} [Bicategory.{w, v} B]

attribute [local instance high] FinEnum.instFintype

private theorem exists_isLayerOrder_top (d : PastingDiagram (bicategoryNerve B)) (hd : d.dim ≤ 2) :
    ∃ xs : List d.shape.rdc.obj.toOGP, IsLayerOrder (⊤ : LowerSet d.shape.rdc.obj.toOGP) xs :=
  exists_isLayerOrder_of_krullDim_le d.shape.isMolecule (by
    rw [LowerSet.krullDim_top]
    exact d.shape.krullDim_eq_dimension.trans_le (by exact_mod_cast hd))

noncomputable def nerveComposite (d : PastingDiagram (bicategoryNerve B)) (hd : d.dim ≤ 2) :
    PathCell B :=
  (bicategoryNerveHomEquiv B d.shape.rdc d.map).1.pathCell
    (d.shape.isMolecule : IsMoleculeIn d.shape.rdc.obj.toOGP ⊤)
    (exists_isLayerOrder_top d hd).choose_spec
    (boundary_zero_eq_Iic_vertex (⊤ : LowerSet d.shape.rdc.obj.toOGP) d.shape.isMolecule false)
    (boundary_zero_eq_Iic_vertex (⊤ : LowerSet d.shape.rdc.obj.toOGP) d.shape.isMolecule true)

theorem nerveComposite_eq_pathCell (d : PastingDiagram (bicategoryNerve B))
    (hd : d.dim ≤ 2) {s t : d.shape.rdc.obj.toOGP}
    (hs : d.shape.rdc.obj.toOGP.boundary ⊤ 0 false = .Iic s)
    (ht : d.shape.rdc.obj.toOGP.boundary ⊤ 0 true = .Iic t) {xs : List d.shape.rdc.obj.toOGP}
    (hxs : IsLayerOrder ⊤ xs) :
    d.nerveComposite hd =
      (bicategoryNerveHomEquiv B d.shape.rdc d.map).1.pathCell
        (d.shape.isMolecule : IsMoleculeIn d.shape.rdc.obj.toOGP ⊤) hxs hs ht := by
  exact Labelling.pathCell_congr _ rfl _ _ _ _ _ _ _ _

theorem nerveComposite_eq (d : PastingDiagram (bicategoryNerve B)) (hd : d.dim ≤ 2)
    {s t : d.shape.rdc.obj.toOGP} (hs : d.shape.rdc.obj.toOGP.boundary ⊤ 0 false = .Iic s)
    (ht : d.shape.rdc.obj.toOGP.boundary ⊤ 0 true = .Iic t) {xs : List d.shape.rdc.obj.toOGP}
    (hxs : IsLayerOrder ⊤ xs) :
    d.nerveComposite hd =
      ⟨_, _, (bicategoryNerveHomEquiv B d.shape.rdc d.map).1.toPrefunctor.mapPath
          (pathOf (d.shape.rdc.obj.toOGP.boundary ⊤ 1 false) (d.shape.isMolecule.boundary 1 false)
            ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
            ((d.shape.isMolecule.isGlobular.boundary_boundary_eq_of_le zero_le_one
              (.inl zero_lt_one)).trans hs)
            ((d.shape.isMolecule.isGlobular.boundary_boundary_eq_of_le zero_le_one
              (.inl zero_lt_one)).trans ht)),
        (bicategoryNerveHomEquiv B d.shape.rdc d.map).1.toPrefunctor.mapPath
          (pathOf (d.shape.rdc.obj.toOGP.boundary ⊤ 1 true) (d.shape.isMolecule.boundary 1 true)
            ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
            ((d.shape.isMolecule.isGlobular.boundary_boundary_eq_of_le zero_le_one
              (.inl zero_lt_one)).trans hs)
            ((d.shape.isMolecule.isGlobular.boundary_boundary_eq_of_le zero_le_one
              (.inl zero_lt_one)).trans ht)),
        eqToHom (pathComp_mapPath (bicategoryNerveHomEquiv B d.shape.rdc d.map).1.toPrefunctor
          _) ≫
          (bicategoryNerveHomEquiv B d.shape.rdc d.map).1.compositeAlong
            (d.shape.isMolecule : IsMoleculeIn d.shape.rdc.obj.toOGP ⊤) hxs hs ht ≫
          eqToHom (pathComp_mapPath
            (bicategoryNerveHomEquiv B d.shape.rdc d.map).1.toPrefunctor _).symm⟩ :=
  nerveComposite_eq_pathCell d hd hs ht hxs

theorem krullDim_top_le (d : PastingDiagram (bicategoryNerve B)) {n : ℕ} (hd : d.dim ≤ n) :
    krullDim (⊤ : LowerSet d.shape.rdc.obj.toOGP) ≤ n := by
  rw [LowerSet.krullDim_top]
  exact d.shape.krullDim_eq_dimension.trans_le (by exact_mod_cast hd)

theorem nerveComposite_of_dim_le_one (d : PastingDiagram (bicategoryNerve B)) (hd : d.dim ≤ 1)
    (hd' : d.dim ≤ 2) {s t : d.shape.rdc.obj.toOGP}
    (hs : d.shape.rdc.obj.toOGP.boundary ⊤ 0 false = .Iic s)
    (ht : d.shape.rdc.obj.toOGP.boundary ⊤ 0 true = .Iic t) :
    d.nerveComposite hd' =
      ⟨_, _, (bicategoryNerveHomEquiv B d.shape.rdc d.map).1.toPrefunctor.mapPath
          (pathOf ⊤ (d.shape.isMolecule : IsMoleculeIn d.shape.rdc.obj.toOGP ⊤)
            ((d.krullDim_top_le hd).trans_eq Nat.cast_one) hs ht),
        (bicategoryNerveHomEquiv B d.shape.rdc d.map).1.toPrefunctor.mapPath
          (pathOf ⊤ (d.shape.isMolecule : IsMoleculeIn d.shape.rdc.obj.toOGP ⊤)
            ((d.krullDim_top_le hd).trans_eq Nat.cast_one) hs ht), 𝟙 _⟩ :=
  (nerveComposite_eq_pathCell d hd' hs ht
    (isLayerOrder_nil ((d.krullDim_top_le hd).trans_eq Nat.cast_one))).trans
    (Labelling.pathCell_of_krullDim_le_one _ _ _ _ _ _)

theorem nerveComposite_eq_pathCell_of_isInclusion {d d' : PastingDiagram (bicategoryNerve B)}
    (f : d.shape.ogp ⟶ d'.shape.ogp) [IsInclusion f]
    (h : realize.map (RDCpx.ofInclusion (P := d.shape.rdc) (Q := d'.shape.rdc) f) ≫ d'.map =
      d.map) (hd : d.dim ≤ 2) [DecidablePred (· ∈ OGP.map f ⊤)] {s t : d'.shape.rdc.obj.toOGP}
    (hs : d'.shape.rdc.obj.toOGP.boundary (OGP.map f ⊤) 0 false = .Iic s)
    (ht : d'.shape.rdc.obj.toOGP.boundary (OGP.map f ⊤) 0 true = .Iic t)
    {xs : List d'.shape.rdc.obj.toOGP} (hxs : IsLayerOrder (OGP.map f ⊤) xs) :
    d.nerveComposite hd =
      (bicategoryNerveHomEquiv B d'.shape.rdc d'.map).1.pathCell
        ((isMoleculeIn_map_iff f ⊤).2 d.shape.isMolecule) hxs hs ht := by
  obtain ⟨ys, hys⟩ := exists_isLayerOrder_top d hd
  rw [nerveComposite_eq_pathCell d hd (boundary_zero_eq_Iic_vertex
    (⊤ : LowerSet d.shape.rdc.obj.toOGP) d.shape.isMolecule false) (boundary_zero_eq_Iic_vertex
      (⊤ : LowerSet d.shape.rdc.obj.toOGP) d.shape.isMolecule true) hys]
  have hℓ : (bicategoryNerveHomEquiv B d.shape.rdc d.map).1 =
      (bicategoryNerveHomEquiv B d'.shape.rdc d'.map).1.comap ⟨f, isMap_of_isInclusion f⟩
        d.shape.rdc.obj.isRDC := by
    rw [← h]
    exact bicategoryNerveHomEquiv_comp B _ d'.map
  rw [hℓ]
  exact (Labelling.pathCell_comap_of_isInclusion f _ _ hys _ _).trans
    (Labelling.pathCell_congr _ rfl _ _ _ _ _ _ _ _)

theorem nerveComposite_congr {d d' : PastingDiagram (bicategoryNerve B)} (h : d.Equiv d')
    (hd : d.dim ≤ 2) (hd' : d'.dim ≤ 2) : d.nerveComposite hd = d'.nerveComposite hd' := by
  obtain ⟨ys, hys⟩ := exists_isLayerOrder_top d' hd'
  classical
  have hv (α : Bool) : d'.shape.rdc.obj.toOGP.boundary (OGP.map h.iso.hom ⊤) 0 α =
      .Iic (vertex (⊤ : LowerSet d'.shape.rdc.obj.toOGP) d'.shape.isMolecule α) := by
    rw [map_top_of_isIso]
    exact boundary_zero_eq_Iic_vertex _ _ _
  exact (nerveComposite_eq_pathCell_of_isInclusion h.iso.hom h.map_comm hd (hv false) (hv true)
    ((map_top_of_isIso h.iso.hom).symm ▸ hys)).trans
      ((Labelling.pathCell_congr _ (map_top_of_isIso h.iso.hom) _ _ _ _ _ _ _ _).trans
        (nerveComposite_eq_pathCell d' hd' (boundary_zero_eq_Iic_vertex
          (⊤ : LowerSet d'.shape.rdc.obj.toOGP) d'.shape.isMolecule false)
          (boundary_zero_eq_Iic_vertex (⊤ : LowerSet d'.shape.rdc.obj.toOGP)
            d'.shape.isMolecule true) hys).symm)

theorem nerveComposite_boundary_eq_pathCell (d : PastingDiagram (bicategoryNerve B)) {k : ℕ}
    (α : Bool) (hd : (d.boundary k α).dim ≤ 2) {s t : d.shape.rdc.obj.toOGP}
    (hs : d.shape.rdc.obj.toOGP.boundary (d.shape.rdc.obj.toOGP.boundary ⊤ k α) 0 false = .Iic s)
    (ht : d.shape.rdc.obj.toOGP.boundary (d.shape.rdc.obj.toOGP.boundary ⊤ k α) 0 true = .Iic t)
    {xs : List d.shape.rdc.obj.toOGP}
    (hxs : IsLayerOrder (d.shape.rdc.obj.toOGP.boundary ⊤ k α) xs) :
    (d.boundary k α).nerveComposite hd =
      (bicategoryNerveHomEquiv B d.shape.rdc d.map).1.pathCell
        ((d.shape.isMolecule : IsMoleculeIn d.shape.rdc.obj.toOGP ⊤).boundary k α) hxs hs ht := by
  classical
  exact (nerveComposite_eq_pathCell_of_isInclusion (d := d.boundary k α) (d.shape.boundaryIncl k α)
    rfl hd ((d.shape.map_boundaryIncl_top k α).symm ▸ hs)
    ((d.shape.map_boundaryIncl_top k α).symm ▸ ht)
    ((d.shape.map_boundaryIncl_top k α).symm ▸ hxs)).trans
      (Labelling.pathCell_congr _ (d.shape.map_boundaryIncl_top k α) _ _ _ _ _ _ _ _)

theorem nerveComposite_boundary_eq (d : PastingDiagram (bicategoryNerve B)) :
    (d.boundary 2 false).nerveComposite (d.shape.dimension_boundary_le 2 false) =
      (d.boundary 2 true).nerveComposite (d.shape.dimension_boundary_le 2 true) := by
  have hM : IsMoleculeIn d.shape.rdc.obj.toOGP ⊤ := d.shape.isMolecule
  obtain ⟨xs, hxs⟩ := exists_isLayerOrder_of_krullDim_le (hM.boundary 2 false)
    ((krullDim_boundary_le _ 2 false).trans_eq Nat.cast_ofNat)
  obtain ⟨ys, hys⟩ := exists_isLayerOrder_of_krullDim_le (hM.boundary 2 true)
    ((krullDim_boundary_le _ 2 true).trans_eq Nat.cast_ofNat)
  have hs := boundary_zero_eq_Iic_vertex (⊤ : LowerSet d.shape.rdc.obj.toOGP) hM false
  have ht := boundary_zero_eq_Iic_vertex (⊤ : LowerSet d.shape.rdc.obj.toOGP) hM true
  exact (nerveComposite_boundary_eq_pathCell d false _
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
      ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht) hxs).trans
    (((bicategoryNerveHomEquiv B d.shape.rdc d.map).2.pathCell_boundary_eq hM hs ht hxs hys).trans
      (nerveComposite_boundary_eq_pathCell d true _
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht)
          hys).symm)

theorem nerveComposite_pasteAlong_one (u v : PastingDiagram (bicategoryNerve B))
    (ψ : (u.boundary 1 true).shape.ogp ≅ (v.boundary 1 false).shape.ogp)
    (hab : realize.map (RDCpx.isoOfIso (P := (u.boundary 1 true).shape.rdc)
      (Q := (v.boundary 1 false).shape.rdc) ψ).hom ≫ (v.boundary 1 false).map =
        (u.boundary 1 true).map) (hu : u.dim ≤ 2) (hv : v.dim ≤ 2)
    (hw : (pasteAlong u v 1 ψ hab).dim ≤ 2) {a b : B} {p q r : Quiver.Path (V := B) a b}
    {φ : pathComp (𝟭q B) p ⟶ pathComp (𝟭q B) q} {χ : pathComp (𝟭q B) q ⟶ pathComp (𝟭q B) r}
    (hx : u.nerveComposite hu = ⟨a, b, p, q, φ⟩) (hy : v.nerveComposite hv = ⟨a, b, q, r, χ⟩) :
    (pasteAlong u v 1 ψ hab).nerveComposite hw = ⟨a, b, p, r, φ ≫ χ⟩ := by
  classical
  have hp := isPastingIn_paste u v 1 ψ
  have hM₁ := (isMoleculeIn_map_iff (pasteInl u v 1 ψ) ⊤).2 u.shape.isMolecule
  have hM₂ := (isMoleculeIn_map_iff (pasteInr u v 1 ψ) ⊤).2 v.shape.isMolecule
  have hM : IsMoleculeIn (pasteAlong u v 1 ψ hab).shape.rdc.obj.toOGP ⊤ :=
    (pasteAlong u v 1 ψ hab).shape.isMolecule
  have hs := boundary_zero_eq_Iic_vertex _ hM false
  have ht := boundary_zero_eq_Iic_vertex _ hM true
  have hv₁ (α : Bool) := (hp.boundary_eq_of_lt_cond (A := OGP.map (pasteInr u v 1 ψ) ⊤)
    (B := OGP.map (pasteInl u v 1 ψ) ⊤) false hM₂.isGlobular hM₁.isGlobular zero_lt_one α).symm
  have hv₂ (α : Bool) := (hp.boundary_eq_of_lt_cond (A := OGP.map (pasteInl u v 1 ψ) ⊤)
    (B := OGP.map (pasteInr u v 1 ψ) ⊤) true hM₁.isGlobular hM₂.isGlobular zero_lt_one α).symm
  obtain ⟨xs₁, hxs₁⟩ := exists_isLayerOrder_top u hu
  obtain ⟨xs₂, hxs₂⟩ := exists_isLayerOrder_top v hv
  have h₁ := hxs₁.map_of_isInclusion (pasteInl u v 1 ψ)
  have h₂ := hxs₂.map_of_isInclusion (pasteInr u v 1 ψ)
  have hx' := nerveComposite_eq_pathCell_of_isInclusion (d' := pasteAlong u v 1 ψ hab) _
    (ofInclusion_pasteInl_map u v 1 ψ hab) hu ((hv₁ false).trans hs) ((hv₁ true).trans ht) h₁
  have hy' := nerveComposite_eq_pathCell_of_isInclusion (d' := pasteAlong u v 1 ψ hab) _
    (ofInclusion_pasteInr_map u v 1 ψ hab) hv ((hv₂ false).trans hs) ((hv₂ true).trans ht) h₂
  rw [nerveComposite_eq_pathCell _ hw hs ht (h₁.append_of_isPastingIn_one hp h₂)]
  exact Labelling.pathCell_append_of_isPastingIn_one hM hM₁ hM₂ hp h₁ h₂ hs ht _ _ _ _ _
    (hx'.symm.trans hx) (hy'.symm.trans hy)

theorem nerveComposite_pasteAlong_zero (u v : PastingDiagram (bicategoryNerve B))
    (ψ : (u.boundary 0 true).shape.ogp ≅ (v.boundary 0 false).shape.ogp)
    (hab : realize.map (RDCpx.isoOfIso (P := (u.boundary 0 true).shape.rdc)
      (Q := (v.boundary 0 false).shape.rdc) ψ).hom ≫ (v.boundary 0 false).map =
        (u.boundary 0 true).map) (hu : u.dim ≤ 2) (hv : v.dim ≤ 2)
    (hw : (pasteAlong u v 0 ψ hab).dim ≤ 2) {a c b : B} {p q : Quiver.Path (V := B) a c}
    {p' q' : Quiver.Path (V := B) c b} {φ : pathComp (𝟭q B) p ⟶ pathComp (𝟭q B) q}
    {χ : pathComp (𝟭q B) p' ⟶ pathComp (𝟭q B) q'}
    (hx : u.nerveComposite hu = ⟨a, c, p, q, φ⟩) (hy : v.nerveComposite hv = ⟨c, b, p', q', χ⟩) :
    (pasteAlong u v 0 ψ hab).nerveComposite hw =
      ⟨a, b, p.comp p', q.comp q', (Bicategory.pathCompCompIso (𝟭q B) p p').hom ≫
        (φ ▷ pathComp (𝟭q B) p' ≫ pathComp (𝟭q B) q ◁ χ) ≫
          (Bicategory.pathCompCompIso (𝟭q B) q q').inv⟩ := by
  classical
  have hp := isPastingIn_paste u v 0 ψ
  have hM₁ := (isMoleculeIn_map_iff (pasteInl u v 0 ψ) ⊤).2 u.shape.isMolecule
  have hM₂ := (isMoleculeIn_map_iff (pasteInr u v 0 ψ) ⊤).2 v.shape.isMolecule
  have hM : IsMoleculeIn (pasteAlong u v 0 ψ hab).shape.rdc.obj.toOGP ⊤ :=
    (pasteAlong u v 0 ψ hab).shape.isMolecule
  have hs := boundary_zero_eq_Iic_vertex _ hM false
  have ht := boundary_zero_eq_Iic_vertex _ hM true
  have hm := boundary_zero_eq_Iic_vertex _ hM₁ true
  obtain ⟨xs₁, hxs₁⟩ := exists_isLayerOrder_top u hu
  obtain ⟨xs₂, hxs₂⟩ := exists_isLayerOrder_top v hv
  have h₁ := hxs₁.map_of_isInclusion (pasteInl u v 0 ψ)
  have h₂ := hxs₂.map_of_isInclusion (pasteInr u v 0 ψ)
  have hx' := nerveComposite_eq_pathCell_of_isInclusion (d' := pasteAlong u v 0 ψ hab) _
    (ofInclusion_pasteInl_map u v 0 ψ hab) hu (hp.boundary_input.symm.trans hs) hm h₁
  have hy' := nerveComposite_eq_pathCell_of_isInclusion (d' := pasteAlong u v 0 ψ hab) _
    (ofInclusion_pasteInr_map u v 0 ψ hab) hv
    ((hp.inf_eq_input.symm.trans hp.inf_eq_output).trans hm) (hp.boundary_output.symm.trans ht)
    h₂
  rw [nerveComposite_eq_pathCell _ hw hs ht (h₁.append_of_isPastingIn_zero hM₁ hM₂ hp h₂)]
  exact Labelling.pathCell_append_of_isPastingIn_zero hM hM₁ hM₂ hp h₁ h₂ hs ht _ _ _ _ _
    (hx'.symm.trans hx) (hy'.symm.trans hy)

theorem nerveComposite_boundary_one (d : PastingDiagram (bicategoryNerve B))
    (hd : d.dim ≤ 2) (α : Bool) (hb : (d.boundary 1 α).dim ≤ 2) :
    (d.boundary 1 α).nerveComposite hb =
      ⟨(d.nerveComposite hd).src, (d.nerveComposite hd).tgt,
        cond α (d.nerveComposite hd).cod (d.nerveComposite hd).dom,
        cond α (d.nerveComposite hd).cod (d.nerveComposite hd).dom, 𝟙 _⟩ := by
  have hM : IsMoleculeIn d.shape.rdc.obj.toOGP ⊤ := d.shape.isMolecule
  obtain ⟨xs, hxs⟩ := exists_isLayerOrder_of_krullDim_le hM (d.krullDim_top_le hd)
  have hs := boundary_zero_eq_Iic_vertex _ hM false
  have ht := boundary_zero_eq_Iic_vertex _ hM true
  have hd₁ : krullDim (d.shape.rdc.obj.toOGP.boundary ⊤ 1 α) ≤ 1 :=
    (krullDim_boundary_le _ 1 α).trans_eq Nat.cast_one
  rw [nerveComposite_eq d hd hs ht hxs, nerveComposite_boundary_eq_pathCell d α hb
    ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
    ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)
    (isLayerOrder_nil hd₁), Labelling.pathCell_of_krullDim_le_one _ _ _ _ _ hd₁]
  cases α
  · rfl
  · simp only [cond_true]

theorem cell_eq_comap_ofCell {U : Atom} (x : diagram (bicategoryNerve.{w, v, u} B) U) :
    x.1 = @Labelling.comap U.ogp (ofCell x).shape.rdc.obj.toOGP U.instFintypeCarrierOgp _
      FinEnum.instFintype _ B _ _
      (ConcreteCategory.hom (C := RDCpxDown) (atomToRDCpx.map (𝟙 U)).hom) U.isRDC
      (bicategoryNerveHomEquiv B (ofCell x).shape.rdc (ofCell x).map).1 := by
  have h := congrArg Subtype.val (ofCell_map_app_map x (𝟙 U))
  rw [op_id, Functor.map_id_apply] at h
  refine h.symm.trans (Eq.trans ?_ (bicategoryNerveHomEquiv_symm_app B _ U _))
  rw [Equiv.symm_apply_apply]
theorem nerveComposite_ofCell {U : Atom} (x : diagram (bicategoryNerve.{w, v, u} B) U)
    (hd : (ofCell x).dim ≤ 2) {s t : U.ogp}
    (hs : U.ogp.boundary (.Iic U.top) 0 false = .Iic s)
    (ht : U.ogp.boundary (.Iic U.top) 0 true = .Iic t) {xs : List U.ogp}
    (hxs : IsLayerOrder (.Iic U.top) xs) :
    (ofCell x).nerveComposite hd = @Labelling.pathCell U.ogp (.Iic U.top) xs
      U.instFintypeCarrierOgp _ _ (U.isRDC U.top) hxs s t hs ht B _ _ x.1 := by
  rw [cell_eq_comap_ofCell x]
  have hc : ConcreteCategory.hom (C := RDCpxDown) (atomToRDCpx.map (𝟙 U)).hom =
      (⟨ConcreteCategory.hom (𝟙 U.ogp : U.ogp ⟶ (ofCell x).shape.rdc.obj.toOGP),
        isMap_of_isInclusion _⟩ : Map U.ogp (ofCell x).shape.rdc.obj.toOGP) :=
    Map.ext fun _ => rfl
  rw [hc, @Labelling.pathCell_comap_of_isInclusion U.ogp _ U.instFintypeCarrierOgp _
    FinEnum.instFintype _ B _ _ _ (𝟙 _) _ _ (.Iic U.top) _ (Classical.decPred _) (U.isRDC U.top)
    xs hxs s t hs ht]
  have hM : IsMoleculeIn (ofCell x).shape.rdc.obj.toOGP ⊤ := (ofCell x).shape.isMolecule
  obtain ⟨ys, hys⟩ := exists_isLayerOrder_of_krullDim_le hM ((ofCell x).krullDim_top_le hd)
  have e : (⊤ : LowerSet (ofCell x).shape.rdc.obj.toOGP) =
      OGP.map (𝟙 U.ogp : U.ogp ⟶ (ofCell x).shape.rdc.obj.toOGP) (.Iic U.top) := by
    rw [Atom.Iic_top]
    exact (map_top_of_isIso _).symm
  exact (nerveComposite_eq_pathCell _ hd (boundary_zero_eq_Iic_vertex _ hM false)
    (boundary_zero_eq_Iic_vertex _ hM true) hys).trans
      (Labelling.pathCell_congr (d' := Classical.decPred _) _ e _ _ _ _ _ _ _
        _)
theorem nerveComposite_of_freeImage {W : Type u₂} [Quiver.{v₂} W] (F : Prefunctor W B)
    {D M : MoleculeShape} (g : D.rdc ⟶ M.rdc)
    (φ : realize.obj M.rdc ⟶ bicategoryNerve B)
    (φ' : realize.obj M.rdc ⟶ bicategoryNerve (FreeBicategory W))
    (h : (bicategoryNerveHomEquiv B M.rdc φ).1.toPrefunctor =
      (bicategoryNerveHomEquiv _ M.rdc φ').1.toPrefunctor ⋙q (lift F).toPrefunctor)
    (hM : M.dimension ≤ 1) (hd : D.dimension ≤ 2) {a b : FreeBicategory W}
    {p q : Quiver.Path a b}
    {θ : pathComp (𝟭q (FreeBicategory W)) p ⟶ pathComp (𝟭q (FreeBicategory W)) q}
    (he : (⟨D, realize.map g ≫ φ'⟩ : PastingDiagram _).nerveComposite hd = ⟨a, b, p, q, θ⟩) :
    ∃ ψ, IsStructural F (pathComp (𝟭q _) p) (pathComp (𝟭q _) q) ψ ∧
      (⟨D, realize.map g ≫ φ⟩ : PastingDiagram _).nerveComposite hd =
        ⟨_, _, (lift F).toPrefunctor.mapPath p, (lift F).toPrefunctor.mapPath q, ψ⟩ := by
  have hD : IsMoleculeIn D.rdc.obj.toOGP ⊤ := D.isMolecule
  obtain ⟨xs, hxs⟩ := exists_isLayerOrder_of_krullDim_le hD
    ((⟨D, realize.map g ≫ φ⟩ : PastingDiagram (bicategoryNerve B)).krullDim_top_le hd)
  have hs := boundary_zero_eq_Iic_vertex _ hD false
  have ht := boundary_zero_eq_Iic_vertex _ hD true
  rw [nerveComposite_eq_pathCell (⟨D, realize.map g ≫ φ'⟩ : PastingDiagram _) hd hs ht hxs,
    bicategoryNerveHomEquiv_comp] at he
  rw [nerveComposite_eq_pathCell (⟨D, realize.map g ≫ φ⟩ : PastingDiagram _) hd hs ht hxs,
    bicategoryNerveHomEquiv_comp]
  have hc (j : ℕ) (hj : j < xs.length) :
      grade ℕ ((ConcreteCategory.hom (C := RDCpxDown) g.hom) xs[j]) ≠ 2 := by
    have h1 := grade_le_krullDim ((ConcreteCategory.hom (C := RDCpxDown) g.hom) xs[j])
    have h2 : krullDim M.rdc.obj.toOGP = (M.dimension : WithBot ℕ∞) := M.krullDim_eq_dimension
    rw [h2] at h1
    have : grade ℕ ((ConcreteCategory.hom (C := RDCpxDown) g.hom) xs[j]) ≤ 1 := by
      have h3 : ((grade ℕ ((ConcreteCategory.hom (C := RDCpxDown) g.hom) xs[j]) : ℕ) :
          WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞) := h1.trans (by exact_mod_cast hM)
      exact_mod_cast h3
    omega
  exact Labelling.pathCell_comap_of_comp_lift F _ _ h _ hD hxs hs ht hc he

theorem pathCell_nil_ext {a a' b : B} (ha : a = b) (ha' : a' = b) {p : Quiver.Path a a'}
    (hp : p ≍ (Quiver.Path.nil : Quiver.Path b b)) :
    (⟨a, a', p, p, 𝟙 _⟩ : PathCell B) = ⟨b, b, .nil, .nil, 𝟙 _⟩ := by
  subst ha ha'
  obtain rfl := eq_of_heq hp
  rfl

theorem exists_nerveComposite_eq_of_dim_le_one (d : PastingDiagram (bicategoryNerve.{w, v, u} B))
    (hd : d.dim ≤ 2) (h1 : d.dim ≤ 1) :
    ∃ p : Quiver.Path (d.nerveComposite hd).src (d.nerveComposite hd).tgt,
      d.nerveComposite hd = ⟨_, _, p, p, 𝟙 _⟩ := by
  have hM : IsMoleculeIn d.shape.rdc.obj.toOGP ⊤ := d.shape.isMolecule
  rw [nerveComposite_of_dim_le_one d h1 hd (boundary_zero_eq_Iic_vertex _ hM false)
    (boundary_zero_eq_Iic_vertex _ hM true)]
  exact ⟨_, rfl⟩

theorem exists_nerveComposite_eq_of_dim_eq_zero (d : PastingDiagram (bicategoryNerve.{w, v, u} B))
    (hd : d.dim ≤ 2) (h0 : d.dim = 0) :
    ∃ b : B, d.nerveComposite hd = ⟨b, b, .nil, .nil, 𝟙 _⟩ := by
  have hM : IsMoleculeIn d.shape.rdc.obj.toOGP ⊤ := d.shape.isMolecule
  rw [nerveComposite_of_dim_le_one d (by omega) hd (boundary_zero_eq_Iic_vertex _ hM false)
    (boundary_zero_eq_Iic_vertex _ hM true)]
  have hsub : Subsingleton d.shape.ogp := d.shape.subsingleton_of_dimension_eq_zero h0
  have hp : ∀ {y z : d.shape.rdc.obj.toOGP} (p : Quiver.Path (V := EdgeQuiver _) y z),
      (bicategoryNerveHomEquiv B d.shape.rdc d.map).1.toPrefunctor.mapPath p ≍
        (Quiver.Path.nil : Quiver.Path
          ((bicategoryNerveHomEquiv B d.shape.rdc d.map).1.toPrefunctor.obj y) _) := by
    intro y z p
    cases p with
    | nil => rfl
    | cons q e =>
      have hmin : IsMin e.1 := fun b _ => (Subsingleton.elim (α := d.shape.ogp) e.1 b).le
      exact absurd (e.2.1.symm.trans (hmin.grade ℕ).eq_bot) (by decide)
  exact ⟨_, pathCell_nil_ext rfl (congrArg _ (Subsingleton.elim (α := d.shape.ogp) _ _))
    (hp _)⟩

theorem nerveComposite_boundary_zero (d : PastingDiagram (bicategoryNerve.{w, v, u} B))
    (hd : d.dim ≤ 2) (α : Bool) (hb : (d.boundary 0 α).dim ≤ 2) :
    (d.boundary 0 α).nerveComposite hb =
      ⟨cond α (d.nerveComposite hd).tgt (d.nerveComposite hd).src,
        cond α (d.nerveComposite hd).tgt (d.nerveComposite hd).src, .nil, .nil, 𝟙 _⟩ := by
  obtain ⟨x, hx⟩ := exists_nerveComposite_eq_of_dim_eq_zero (d.boundary 0 α) hb
    (dim_boundary _ (Nat.zero_le _) α)
  have hM : IsMoleculeIn d.shape.rdc.obj.toOGP ⊤ := d.shape.isMolecule
  have hv (β : Bool) : d.shape.rdc.obj.toOGP.boundary (d.shape.rdc.obj.toOGP.boundary ⊤ 0 α) 0 β =
      .Iic (vertex ⊤ hM α) :=
    (boundary_eq_self ((krullDim_boundary_le _ 0 α).trans_eq Nat.cast_zero) β).trans
      (boundary_zero_eq_Iic_vertex _ hM α)
  obtain ⟨xs, hxs⟩ := exists_isLayerOrder_of_krullDim_le (hM.boundary 0 α)
    ((krullDim_boundary_le _ 0 α).trans (by exact_mod_cast Nat.zero_le 2))
  have e := congrArg PathCell.src
    (hx.symm.trans (nerveComposite_boundary_eq_pathCell d α hb (hv false) (hv true) hxs))
  obtain rfl : x = cond α (d.nerveComposite hd).tgt (d.nerveComposite hd).src :=
    e.trans (by cases α <;> rfl)
  exact hx

end Atoms.Diagrammatic.PastingDiagram
