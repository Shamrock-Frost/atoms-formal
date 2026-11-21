import Atoms.Diagrammatic.BicategoryNerve.Realization

open CategoryTheory Opposite Order Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape
open CategoryTheory.Bicategory (PathCell pathComp pathComp_mapPath)
open CategoryTheory.FreeBicategory (lift)
open scoped CategoryTheory.Bicategory

universe w v u v'

namespace Atoms.Diagrammatic

local instance (priority := high) instDecidableMemBdryFullAtom (U : Atom) :
    DecidablePred (· ∈ U.ogp.bdryFull ⊤) :=
  inferInstance

attribute [local instance high] instFintypeRdc

local instance (priority := high) instFintypeRestrict (P : OGP.{0}) (M : LowerSet P)
    [FinEnum (P.restrict M)] : Fintype (P.restrict M) :=
  FinEnum.instFintype

variable {B : Type u} [Bicategory.{w, v} B]

namespace PastingDiagram

noncomputable def nerveCellOf {U : Atom}
    (ℓ : {ℓ : Labelling B U.toMoleculeShape.rdc.obj.toOGP U.toMoleculeShape.rdc.obj.isRDC //
      ℓ.IsCommutative}) : diagram (bicategoryNerve.{w, v, u} B) U :=
  uliftYonedaEquiv ((realizeAtomIso U).inv ≫
    (bicategoryNerveHomEquiv B U.toMoleculeShape.rdc).symm ℓ)

theorem map_ofCell_nerveCellOf {U : Atom}
    (ℓ : {ℓ : Labelling B U.toMoleculeShape.rdc.obj.toOGP U.toMoleculeShape.rdc.obj.isRDC //
      ℓ.IsCommutative}) :
    (ofCell (nerveCellOf ℓ)).map = (bicategoryNerveHomEquiv B U.toMoleculeShape.rdc).symm ℓ := by
  simp [nerveCellOf]

theorem bicategoryNerveHomEquiv_ofCell_nerveCellOf {U : Atom}
    (ℓ : {ℓ : Labelling B U.toMoleculeShape.rdc.obj.toOGP U.toMoleculeShape.rdc.obj.isRDC //
      ℓ.IsCommutative}) :
    bicategoryNerveHomEquiv B (ofCell (nerveCellOf ℓ)).shape.rdc (ofCell (nerveCellOf ℓ)).map =
      ℓ := by
  rw [map_ofCell_nerveCellOf]
  exact Equiv.apply_symm_apply _ _

end PastingDiagram

namespace Parallel

variable {s t : RoundPastingDiagram (bicategoryNerve.{w, v, u} B)} (h : Parallel s t)

noncomputable abbrev sphereLabelling :
    Labelling B (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP
      (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.isRDC :=
  (bicategoryNerveHomEquiv B (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)) h.sphere).1

noncomputable abbrev sphereEmb (α : Bool) :
    (cond α t.shape s.shape).rdc.obj.toOGP ⟶
      (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP :=
  codRestrict (h.cellShapeEmb α) _ fun x =>
    h.map_cellShapeEmb_le_bdryFull α ⟨x, LowerSet.mem_top, rfl⟩

theorem bicategoryNerveHomEquiv_restrictAlong_sphere (α : Bool) :
    (bicategoryNerveHomEquiv B (cond α t.shape s.shape).rdc
        (restrictAlong h.sphere _ (h.cellShapeEmb α) (h.map_cellShapeEmb_le_bdryFull α)).map).1 =
      h.sphereLabelling.comap (P := (cond α t.shape s.shape).rdc.obj.toOGP)
        ⟨h.sphereEmb α, isMap_of_isInclusion _⟩ (cond α t.shape s.shape).rdc.obj.isRDC :=
  bicategoryNerveHomEquiv_comp B _ _

theorem nerveComposite_restrictAlong_sphere (α : Bool)
    (hd : (restrictAlong h.sphere _ (h.cellShapeEmb α) (h.map_cellShapeEmb_le_bdryFull α)).dim ≤ 2)
    [DecidablePred (· ∈ OGP.map (h.sphereEmb α) ⊤)]
    {xs : List (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP}
    (hxs : IsLayerOrder (OGP.map (h.sphereEmb α) ⊤) xs)
    {a b : (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP}
    (ha : (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP.boundary
      (OGP.map (h.sphereEmb α) ⊤) 0 false = .Iic a)
    (hb : (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP.boundary
      (OGP.map (h.sphereEmb α) ⊤) 0 true = .Iic b) :
    (restrictAlong h.sphere _ (h.cellShapeEmb α) (h.map_cellShapeEmb_le_bdryFull α)).nerveComposite
        hd =
      h.sphereLabelling.pathCell ((isMoleculeIn_map_iff (h.sphereEmb α) ⊤).2
        (cond α t.shape s.shape).isMolecule) hxs ha hb := by
  have hM : IsMoleculeIn (cond α t.shape s.shape).rdc.obj.toOGP ⊤ :=
    (cond α t.shape s.shape).isMolecule
  obtain ⟨ys, hys⟩ := exists_isLayerOrder_of_krullDim_le hM
    ((restrictAlong h.sphere _ (h.cellShapeEmb α) _).krullDim_top_le hd)
  have e : (bicategoryNerveHomEquiv B
      (restrictAlong h.sphere _ (h.cellShapeEmb α) (h.map_cellShapeEmb_le_bdryFull α)).shape.rdc
      (restrictAlong h.sphere _ (h.cellShapeEmb α) _).map).1 = _ :=
    h.bicategoryNerveHomEquiv_restrictAlong_sphere α
  rw [PastingDiagram.nerveComposite_eq_pathCell _ hd (boundary_zero_eq_Iic_vertex _ hM false)
    (boundary_zero_eq_Iic_vertex _ hM true) hys, e]
  refine (Labelling.pathCell_comap_of_isInclusion (h.sphereEmb α) h.sphereLabelling hM hys _
    _).trans ?_
  exact Labelling.pathCell_congr _ rfl _ _ _ _ _ _ _ _

theorem map_incl_map_sphereEmb (α : Bool) :
    OGP.map (incl (P := h.cellShape.rdc.obj.toOGP) (h.cellShape.ogp.bdryFull ⊤))
        (OGP.map (h.sphereEmb α) ⊤) = h.cellShape.rdc.obj.toOGP.boundary ⊤ s.dim α := by
  rw [← OGP.map_comp, codRestrict_incl]
  exact h.map_cellShapeEmb α

theorem nerveComposite_cond_eq_pathCell
    {ℓ : Labelling B h.cellShape.toMoleculeShape.rdc.obj.toOGP
      h.cellShape.toMoleculeShape.rdc.obj.isRDC}
    (hℓ : ℓ.comap (P := (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP)
      (inclMap (P := h.cellShape.rdc.obj.toOGP) (h.cellShape.ogp.bdryFull ⊤))
      (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.isRDC = h.sphereLabelling)
    (α : Bool) (hd : (cond α t s).dim ≤ 2) {xs : List h.cellShape.rdc.obj.toOGP}
    (hxs : IsLayerOrder (h.cellShape.rdc.obj.toOGP.boundary ⊤ s.dim α) xs)
    {a b : h.cellShape.rdc.obj.toOGP}
    (ha : h.cellShape.rdc.obj.toOGP.boundary (h.cellShape.rdc.obj.toOGP.boundary ⊤ s.dim α) 0
      false = .Iic a)
    (hb : h.cellShape.rdc.obj.toOGP.boundary (h.cellShape.rdc.obj.toOGP.boundary ⊤ s.dim α) 0
      true = .Iic b) :
    (cond α t s).nerveComposite hd =
      ℓ.pathCell (IsMoleculeIn.boundary (P := h.cellShape.rdc.obj.toOGP)
        h.cellShape.toMoleculeShape.isMolecule s.dim α) hxs ha hb := by
  classical
  have e := h.restrictAlong_sphere α
  have hd' : (restrictAlong h.sphere _ (h.cellShapeEmb α)
      (h.map_cellShapeEmb_le_bdryFull α)).dim ≤ 2 := (congrArg PastingDiagram.dim e).trans_le hd
  have hM := (isMoleculeIn_map_iff (h.sphereEmb α) ⊤).2 (cond α t.shape s.shape).isMolecule
  obtain ⟨ys, hys⟩ := exists_isLayerOrder_of_krullDim_le hM (by
    rw [krullDim_map, LowerSet.krullDim_top]
    exact (cond α t.shape s.shape).krullDim_eq_dimension.trans_le (by exact_mod_cast hd'))
  refine (PastingDiagram.nerveComposite_congr (PastingDiagram.equiv_of_eq e.symm) hd hd').trans ?_
  rw [h.nerveComposite_restrictAlong_sphere α hd' hys (boundary_zero_eq_Iic_vertex _ hM false)
      (boundary_zero_eq_Iic_vertex _ hM true)]
  rw [← hℓ]
  refine (Labelling.pathCell_comap_of_isInclusion (incl (P := h.cellShape.rdc.obj.toOGP)
    (h.cellShape.ogp.bdryFull ⊤)) ℓ hM hys _ _).trans ?_
  exact @Labelling.pathCell_congr _ _ _ _ _ _ _ _ _ _ _
    (h.map_incl_map_sphereEmb α) _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem boundary_map_sphereEmb {α β : Bool} {x : h.cellShape.rdc.obj.toOGP}
    (hm : x ∈ h.cellShape.ogp.bdryFull ⊤)
    (hx : h.cellShape.rdc.obj.toOGP.boundary (h.cellShape.rdc.obj.toOGP.boundary ⊤ s.dim α) 0 β =
      .Iic x) :
    (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP.boundary
      (OGP.map (h.sphereEmb α) ⊤) 0 β = .Iic ⟨x, hm⟩ := by
  refine map_injective (incl (P := h.cellShape.rdc.obj.toOGP) (h.cellShape.ogp.bdryFull ⊤)) ?_
  rw [map_boundary, map_Iic, h.map_incl_map_sphereEmb α]
  exact hx

theorem obj_sphereLabelling {α β : Bool} (hd : (cond α t s).dim ≤ 2)
    {x : (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP}
    (hx : (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP.boundary
      (OGP.map (h.sphereEmb α) ⊤) 0 β = .Iic x) :
    h.sphereLabelling.toPrefunctor.obj x =
      cond β ((cond α t s).nerveComposite hd).tgt ((cond α t s).nerveComposite hd).src := by
  classical
  have e := h.restrictAlong_sphere α
  have hd' : (restrictAlong h.sphere _ (h.cellShapeEmb α)
      (h.map_cellShapeEmb_le_bdryFull α)).dim ≤ 2 := (congrArg PastingDiagram.dim e).trans_le hd
  have hM := (isMoleculeIn_map_iff (h.sphereEmb α) ⊤).2 (cond α t.shape s.shape).isMolecule
  obtain ⟨ys, hys⟩ := exists_isLayerOrder_of_krullDim_le hM (by
    rw [krullDim_map, LowerSet.krullDim_top]
    exact (cond α t.shape s.shape).krullDim_eq_dimension.trans_le (by exact_mod_cast hd'))
  rw [← PastingDiagram.nerveComposite_congr (PastingDiagram.equiv_of_eq e) hd' hd]
  cases β
  · rw [h.nerveComposite_restrictAlong_sphere α hd' hys hx (boundary_zero_eq_Iic_vertex _ hM true)]
    rfl
  · rw [h.nerveComposite_restrictAlong_sphere α hd' hys (boundary_zero_eq_Iic_vertex _ hM false) hx]
    rfl

theorem hasRoundType_nerveCellOf
    (ℓ : {ℓ : Labelling B h.cellShape.toMoleculeShape.rdc.obj.toOGP
      h.cellShape.toMoleculeShape.rdc.obj.isRDC // ℓ.IsCommutative})
    (hℓ : ℓ.1.comap (P := (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP)
      (inclMap (P := h.cellShape.rdc.obj.toOGP) (h.cellShape.ogp.bdryFull ⊤))
      (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.isRDC = h.sphereLabelling) :
    HasRoundType (PastingDiagram.ofCell (PastingDiagram.nerveCellOf ℓ)) s t := by
  have key := (h.hasRoundType_ofCell_iff (𝟙 _) (PastingDiagram.nerveCellOf ℓ)).2 (by
    rw [PastingDiagram.map_ofCell_nerveCellOf, Category.comp_id]
    refine (bicategoryNerveHomEquiv B _).injective (Subtype.ext ?_)
    rw [bicategoryNerveHomEquiv_comp, Equiv.apply_symm_apply]
    exact (congrArg (fun f => ℓ.1.comap f _) (Map.ext fun _ => rfl)).trans hℓ)
  rwa [RoundPastingDiagram.mapTo_id, RoundPastingDiagram.mapTo_id] at key

theorem grade_of_not_mem_bdryFull {x : h.cellShape.rdc.obj.toOGP}
    (hx : x ∉ h.cellShape.ogp.bdryFull ⊤) : grade ℕ x = s.dim + 1 := by
  obtain rfl : x = h.cellShape.top := not_not.1 fun h' => hx ((Atom.mem_bdryFull_top_iff _ x).2 h')
  exact h.cellShape.dimension_eq.symm.trans h.dimension_cellShape

theorem grade_le_of_mem_bdryFull {x : h.cellShape.rdc.obj.toOGP}
    (hx : x ∈ h.cellShape.ogp.bdryFull ⊤) : grade ℕ x ≤ s.dim := by
  have hlt : x < h.cellShape.top :=
    lt_of_le_of_ne (h.cellShape.le_top x) ((Atom.mem_bdryFull_top_iff _ x).1 hx)
  have := grade_strictMono (𝕆 := ℕ) hlt
  have h₁ := h.cellShape.dimension_eq.symm.trans h.dimension_cellShape
  omega

private noncomputable def labellingTwo (hs : s.dim = 2) (b₀ : B) :
    Labelling B h.cellShape.rdc.obj.toOGP h.cellShape.rdc.obj.isRDC :=
  h.sphereLabelling.extend (P := h.cellShape.rdc.obj.toOGP) (hP := h.cellShape.rdc.obj.isRDC) b₀
    (fun e he => absurd (e.2.1.symm.trans (h.grade_of_not_mem_bdryFull he)) (by omega))
    (fun _ hx _ _ _ _ hxM => absurd (hx.symm.trans (h.grade_of_not_mem_bdryFull hxM)) (by omega))

private theorem comap_labellingTwo (hs : s.dim = 2) (b₀ : B) :
    (h.labellingTwo hs b₀).comap (P := (h.cellShape.rdc.restrict
        (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP)
      (inclMap (P := h.cellShape.rdc.obj.toOGP) (h.cellShape.ogp.bdryFull ⊤))
      (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.isRDC = h.sphereLabelling :=
  Labelling.comap_extend _ _ _ _

private theorem isCommutative_labellingTwo (hs : s.dim = 2) (b₀ : B) (hsd : s.dim ≤ 2)
    (htd : t.dim ≤ 2) (hst : s.nerveComposite hsd = t.nerveComposite htd) :
    (h.labellingTwo hs b₀).IsCommutative := by
  intro y hy
  have hy' : y ∉ h.cellShape.ogp.bdryFull ⊤ := fun hm => by
    have := h.grade_le_of_mem_bdryFull hm
    omega
  obtain rfl : y = h.cellShape.top := not_not.1 fun h' => hy' ((Atom.mem_bdryFull_top_iff _ y).2 h')
  have hT : (LowerSet.Iic h.cellShape.top : LowerSet h.cellShape.rdc.obj.toOGP) = ⊤ :=
    h.cellShape.Iic_top
  have hM := (h.cellShape.toMoleculeShape.isMolecule : IsMoleculeIn h.cellShape.rdc.obj.toOGP ⊤)
  apply Labelling.isCommutativeAt_of_pathCell_eq
  intro a b ha hb xs ys hxs hys
  have e (α : Bool) : h.cellShape.rdc.obj.toOGP.boundary (.Iic h.cellShape.top) 2 α =
      h.cellShape.rdc.obj.toOGP.boundary ⊤ s.dim α := by rw [hT, hs]
  have hlo (α : Bool) := exists_isLayerOrder_of_krullDim_le (hM.boundary s.dim α)
    ((krullDim_boundary_le _ _ α).trans (by rw [hs]; rfl))
  obtain ⟨xs', hxs'⟩ := hlo false
  obtain ⟨ys', hys'⟩ := hlo true
  have hv (α β : Bool) := boundary_zero_eq_Iic_vertex _ (hM.boundary s.dim α) β
  refine (@Labelling.pathCell_congr _ _ _ _ _ _ _ _ _ _ _ (e false) _
    (hM.boundary s.dim false) _ _ _ hxs' _ _ _ _ _ _
    (hv false false) (hv false true)).trans ?_
  refine (h.nerveComposite_cond_eq_pathCell (h.comap_labellingTwo hs b₀) false hsd hxs' _
    _).symm.trans
    (hst.trans ((h.nerveComposite_cond_eq_pathCell (h.comap_labellingTwo hs b₀) true htd hys'
      (hv true false) (hv true true)).trans ?_))
  exact @Labelling.pathCell_congr _ _ _ _ _ _ _ _ _ _ _ (e true).symm
    (hM.boundary s.dim true) _ _ _ hys' _ _ _ _ _
    (hv true false) (hv true true) _ _

theorem exists_nerveFiller_two_iff (hs : s.dim = 2) (hsd : s.dim ≤ 2) (htd : t.dim ≤ 2) :
    (∃ x : diagram (bicategoryNerve.{w, v, u} B) h.cellShape,
      HasRoundType (PastingDiagram.ofCell x) s t) ↔
      s.nerveComposite hsd = t.nerveComposite htd := by
  constructor
  · rintro ⟨x, hx⟩
    have ht : t.dim = 2 := hx.dim_eq_dim.symm.trans hs
    have hb (α : Bool) : ((PastingDiagram.ofCell x).boundary 2 α).dim ≤ 2 :=
      (PastingDiagram.ofCell x).shape.dimension_boundary_le 2 α
    have e₀ := hx.source.symm.trans (PastingDiagram.equiv_of_eq
      ((PastingDiagram.ofCell x).boundary_congr hs false))
    have e₁ := hx.target.symm.trans (PastingDiagram.equiv_of_eq
      ((PastingDiagram.ofCell x).boundary_congr hs true))
    exact (PastingDiagram.nerveComposite_congr e₀ hsd (hb false)).trans
      ((PastingDiagram.ofCell x).nerveComposite_boundary_eq.trans
        (PastingDiagram.nerveComposite_congr e₁ htd (hb true)).symm)
  · intro hst
    exact ⟨PastingDiagram.nerveCellOf ⟨h.labellingTwo hs (s.nerveComposite hsd).src,
      h.isCommutative_labellingTwo hs _ hsd htd hst⟩,
      h.hasRoundType_nerveCellOf _ (h.comap_labellingTwo hs _)⟩

theorem mem_bdryFull_of_boundary_zero {α : Bool} {x : h.cellShape.rdc.obj.toOGP}
    (hx : h.cellShape.rdc.obj.toOGP.boundary ⊤ 0 α = .Iic x) :
    x ∈ h.cellShape.ogp.bdryFull ⊤ := by
  have hM := (h.cellShape.toMoleculeShape.isMolecule : IsMoleculeIn h.cellShape.rdc.obj.toOGP ⊤)
  have h₁ : x ∈ h.cellShape.rdc.obj.toOGP.boundary ⊤ 0 α := by
    rw [hx]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  have hg : h.cellShape.rdc.obj.toOGP.boundary (h.cellShape.rdc.obj.toOGP.boundary ⊤ s.dim α) 0
      α = h.cellShape.rdc.obj.toOGP.boundary ⊤ 0 α :=
    hM.isGlobular.boundary_boundary_eq_of_le (Nat.zero_le s.dim) (.inr rfl)
  rw [← hg] at h₁
  exact h.map_cellShapeEmb_le_bdryFull α ((h.map_cellShapeEmb α).ge (boundary_le _ _ _ h₁))

theorem sphereLabelling_obj_vertex {α β : Bool} (hαβ : 0 < s.dim ∨ β = α)
    (hd : (cond α t s).dim ≤ 2) {x : h.cellShape.rdc.obj.toOGP}
    (hx : h.cellShape.rdc.obj.toOGP.boundary ⊤ 0 β = .Iic x) :
    h.sphereLabelling.toPrefunctor.obj ⟨x, h.mem_bdryFull_of_boundary_zero hx⟩ =
      cond β ((cond α t s).nerveComposite hd).tgt ((cond α t s).nerveComposite hd).src := by
  have hM : IsMoleculeIn h.cellShape.rdc.obj.toOGP ⊤ := h.cellShape.toMoleculeShape.isMolecule
  exact h.obj_sphereLabelling hd (h.boundary_map_sphereEmb _
    ((hM.isGlobular.boundary_boundary_eq_of_le (Nat.zero_le s.dim) hαβ).trans hx))

private theorem boundary_top_of_not_mem {α : Bool} {v w : EdgeQuiver h.cellShape.rdc.obj.toOGP}
    (e : v ⟶ w) (he : e.1 ∉ h.cellShape.ogp.bdryFull ⊤) :
    h.cellShape.rdc.obj.toOGP.boundary ⊤ 0 α = .Iic (cond α w v) := by
  have he₁ : e.1 = h.cellShape.top :=
    not_not.1 fun h' => he ((Atom.mem_bdryFull_top_iff _ _).2 h')
  rw [← h.cellShape.Iic_top, ← he₁]
  cases α
  exacts [e.2.2.1, e.2.2.2]

private theorem extendObj_sphereLabelling (b₀ : B) {y : h.cellShape.rdc.obj.toOGP}
    (hy : y ∈ h.cellShape.ogp.bdryFull ⊤) :
    h.sphereLabelling.extendObj (P := h.cellShape.rdc.obj.toOGP)
      (hP := h.cellShape.rdc.obj.isRDC) b₀ y = h.sphereLabelling.toPrefunctor.obj ⟨y, hy⟩ :=
  Labelling.extendObj_of_mem _ _ _

private noncomputable def labellingZero {a b : B} (hs : s.dim = 0) (hsd : s.dim ≤ 2)
    (htd : t.dim ≤ 2)
    (hs' : (s.nerveComposite hsd).src = a) (ht' : (t.nerveComposite htd).tgt = b) (f : a ⟶ b) :
    Labelling B h.cellShape.rdc.obj.toOGP h.cellShape.rdc.obj.isRDC :=
  h.sphereLabelling.extend (P := h.cellShape.rdc.obj.toOGP) (hP := h.cellShape.rdc.obj.isRDC) a
    (fun e he => Quiver.homOfEq f
      (((h.extendObj_sphereLabelling _ _).trans ((h.sphereLabelling_obj_vertex (α := false)
        (.inr rfl) hsd
        (h.boundary_top_of_not_mem e he)).trans hs')).symm)
      (((h.extendObj_sphereLabelling _ _).trans ((h.sphereLabelling_obj_vertex (α := true)
        (.inr rfl) htd
        (h.boundary_top_of_not_mem e he)).trans ht')).symm))
    (fun x hx _ _ _ _ hxM => absurd (hx.symm.trans (h.grade_of_not_mem_bdryFull hxM)) (by omega))

private theorem labellingZero_map {a b : B} (hs : s.dim = 0) (hsd : s.dim ≤ 2)
    (htd : t.dim ≤ 2) (hs' : (s.nerveComposite hsd).src = a) (ht' : (t.nerveComposite htd).tgt = b)
    (f : a ⟶ b) {v w : EdgeQuiver h.cellShape.rdc.obj.toOGP} (e : v ⟶ w)
    (he : e.1 ∉ h.cellShape.ogp.bdryFull ⊤) :
    (h.labellingZero hs hsd htd hs' ht' f).toPrefunctor.map e ≍ f :=
  (heq_of_eq (Labelling.extendPrefunctor_map_of_not_mem (P := h.cellShape.rdc.obj.toOGP) _ _ _ _
    he)).trans
    (Quiver.homOfEq_heq _ _ _)

private theorem labellingZero_obj {a b : B} (hs : s.dim = 0) (hsd : s.dim ≤ 2)
    (htd : t.dim ≤ 2) (hs' : (s.nerveComposite hsd).src = a) (ht' : (t.nerveComposite htd).tgt = b)
    (f : a ⟶ b) {y : h.cellShape.rdc.obj.toOGP} (hy : y ∈ h.cellShape.ogp.bdryFull ⊤) :
    (h.labellingZero hs hsd htd hs' ht' f).toPrefunctor.obj y =
      h.sphereLabelling.toPrefunctor.obj ⟨y, hy⟩ :=
  h.extendObj_sphereLabelling _ _

private theorem comap_labellingZero {a b : B} (hs : s.dim = 0) (hsd : s.dim ≤ 2)
    (htd : t.dim ≤ 2) (hs' : (s.nerveComposite hsd).src = a) (ht' : (t.nerveComposite htd).tgt = b)
    (f : a ⟶ b) :
    (h.labellingZero hs hsd htd hs' ht' f).comap (P := (h.cellShape.rdc.restrict
        (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP)
      (inclMap (P := h.cellShape.rdc.obj.toOGP) (h.cellShape.ogp.bdryFull ⊤))
      (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.isRDC = h.sphereLabelling :=
  Labelling.comap_extend _ _ _ _

private theorem pathCell_of_heq {a b a' b' : B} {f : a ⟶ b} {g : a' ⟶ b'} (ha : a' = a)
    (hb : b' = b) (hg : g ≍ f) :
    (⟨a', b', g.toPath, g.toPath, 𝟙 _⟩ : PathCell B) = ⟨a, b, f.toPath, f.toPath, 𝟙 _⟩ := by
  subst ha hb
  obtain rfl := eq_of_heq hg
  rfl

theorem exists_nerveFiller_zero {a b : B} (hs : s.dim = 0) (hsd : s.dim ≤ 2) (htd : t.dim ≤ 2)
    (hs' : s.nerveComposite hsd = ⟨a, a, .nil, .nil, 𝟙 _⟩)
    (ht' : t.nerveComposite htd = ⟨b, b, .nil, .nil, 𝟙 _⟩) (f : a ⟶ b) :
    ∃ x : diagram (bicategoryNerve.{w, v, u} B) h.cellShape,
      HasRoundType (PastingDiagram.ofCell x) s t ∧ ∀ hd,
        (PastingDiagram.ofCell x).nerveComposite hd = ⟨a, b, f.toPath, f.toPath, 𝟙 _⟩ := by
  have hsa := congrArg PathCell.src hs'
  have htb := congrArg PathCell.tgt ht'
  have hU : h.cellShape.dimension = 1 := h.dimension_cellShape.trans (by rw [hs])
  have hcomm : (h.labellingZero hs hsd htd hsa htb f).IsCommutative := fun y hy => absurd
    ((h.cellShape.grade_le_dimension y).trans_eq hU) (by omega)
  refine ⟨PastingDiagram.nerveCellOf ⟨_, hcomm⟩, h.hasRoundType_nerveCellOf _
    (h.comap_labellingZero hs hsd htd hsa htb f), fun hd => ?_⟩
  have hM : IsMoleculeIn h.cellShape.rdc.obj.toOGP ⊤ := h.cellShape.toMoleculeShape.isMolecule
  have hd₁ : krullDim (⊤ : LowerSet h.cellShape.rdc.obj.toOGP) ≤ 1 := by
    rw [LowerSet.krullDim_top]
    exact h.cellShape.krullDim_eq_dimension.trans_le (by rw [hU]; rfl)
  have hs₀ := boundary_zero_eq_Iic_vertex (P := h.cellShape.rdc.obj.toOGP) _ hM false
  have ht₀ := boundary_zero_eq_Iic_vertex (P := h.cellShape.rdc.obj.toOGP) _ hM true
  rw [PastingDiagram.nerveComposite_eq_pathCell _ hd hs₀ ht₀ (isLayerOrder_nil hd₁),
    PastingDiagram.bicategoryNerveHomEquiv_ofCell_nerveCellOf]
  refine (Labelling.pathCell_of_krullDim_le_one (P := h.cellShape.rdc.obj.toOGP) _ _ _ _ _
    hd₁).trans ?_
  have hg : grade ℕ h.cellShape.top = 1 := h.cellShape.dimension_eq.symm.trans hU
  have hT := h.cellShape.Iic_top
  have hp : pathOf (⊤ : LowerSet h.cellShape.rdc.obj.toOGP) hM hd₁ hs₀ ht₀ =
      Quiver.Hom.toPath (V := EdgeQuiver h.cellShape.rdc.obj.toOGP)
        (⟨h.cellShape.top, hg, by rw [hT]; exact hs₀, by rw [hT]; exact ht₀⟩ :
          Quiver.Hom (V := EdgeQuiver h.cellShape.rdc.obj.toOGP) (vertex _ hM false)
            (vertex _ hM true)) :=
    (eq_pathOf_of_forall_mem hM hd₁ hs₀ ht₀ _ fun _ _ => LowerSet.mem_top).symm
  have hnm : h.cellShape.top ∉ h.cellShape.ogp.bdryFull ⊤ :=
    fun hm => (Atom.mem_bdryFull_top_iff _ _).1 hm rfl
  rw [hp, Prefunctor.mapPath_toPath]
  refine pathCell_of_heq ?_ ?_ (h.labellingZero_map hs hsd htd hsa htb f _ hnm)
  · exact (h.labellingZero_obj hs hsd htd hsa htb f (h.mem_bdryFull_of_boundary_zero hs₀)).trans
      ((h.sphereLabelling_obj_vertex (α := false) (.inr rfl) hsd hs₀).trans hsa)
  · exact (h.labellingZero_obj hs hsd htd hsa htb f (h.mem_bdryFull_of_boundary_zero ht₀)).trans
      ((h.sphereLabelling_obj_vertex (α := true) (.inr rfl) htd ht₀).trans htb)

theorem dom_nerveComposite_cond_heq (hs : s.dim = 1) (α : Bool) (hd : (cond α t s).dim ≤ 2)
    (b₀ : B) (edge : ∀ {v w : EdgeQuiver h.cellShape.rdc.obj.toOGP} (e : v ⟶ w),
      e.1 ∉ h.cellShape.ogp.bdryFull ⊤ → (h.sphereLabelling.extendObj
        (P := h.cellShape.rdc.obj.toOGP) (hP := h.cellShape.rdc.obj.isRDC) b₀ v ⟶
          h.sphereLabelling.extendObj (hP := h.cellShape.rdc.obj.isRDC) b₀ w))
    {x₀ x₁ : h.cellShape.rdc.obj.toOGP}
    (hx₀ : h.cellShape.rdc.obj.toOGP.boundary (.Iic h.cellShape.top) 0 false = .Iic x₀)
    (hx₁ : h.cellShape.rdc.obj.toOGP.boundary (.Iic h.cellShape.top) 0 true = .Iic x₁) :
    ((cond α t s).nerveComposite hd).dom ≍
      (h.sphereLabelling.extendPrefunctor (hP := h.cellShape.rdc.obj.isRDC) b₀ @edge).mapPath
        (pathOf (P := h.cellShape.rdc.obj.toOGP) (h.cellShape.rdc.obj.toOGP.boundary
          (.Iic h.cellShape.top) 1 α) ((h.cellShape.rdc.obj.isRDC h.cellShape.top).boundary 1 α)
          ((krullDim_boundary_le _ 1 α).trans_eq Nat.cast_one)
          (((h.cellShape.rdc.obj.isRDC h.cellShape.top).isGlobular.boundary_boundary_eq_of_le
            zero_le_one (.inl zero_lt_one)).trans hx₀)
          (((h.cellShape.rdc.obj.isRDC h.cellShape.top).isGlobular.boundary_boundary_eq_of_le
            zero_le_one (.inl zero_lt_one)).trans hx₁)) := by
  have hT : (LowerSet.Iic h.cellShape.top : LowerSet h.cellShape.rdc.obj.toOGP) = ⊤ :=
    h.cellShape.Iic_top
  have hU : IsMoleculeIn h.cellShape.rdc.obj.toOGP ⊤ := h.cellShape.toMoleculeShape.isMolecule
  have hv (β : Bool) {x : h.cellShape.rdc.obj.toOGP}
      (hx : h.cellShape.rdc.obj.toOGP.boundary (.Iic h.cellShape.top) 0 β = .Iic x) :
      h.cellShape.rdc.obj.toOGP.boundary (h.cellShape.rdc.obj.toOGP.boundary ⊤ s.dim α) 0 β =
        .Iic x := by
    rw [hU.isGlobular.boundary_boundary_eq_of_le (Nat.zero_le _) (.inl (by omega)), ← hT]
    exact hx
  have hm (β : Bool) {x : h.cellShape.rdc.obj.toOGP}
      (hx : h.cellShape.rdc.obj.toOGP.boundary (.Iic h.cellShape.top) 0 β = .Iic x) :
      x ∈ h.cellShape.ogp.bdryFull ⊤ :=
    h.mem_bdryFull_of_boundary_zero (α := β) (by rw [← hT]; exact hx)
  have hr₀ := h.boundary_map_sphereEmb (hm false hx₀) (hv false hx₀)
  have hr₁ := h.boundary_map_sphereEmb (hm true hx₁) (hv true hx₁)
  have e := h.restrictAlong_sphere α
  have hd' : (restrictAlong h.sphere _ (h.cellShapeEmb α)
      (h.map_cellShapeEmb_le_bdryFull α)).dim ≤ 2 := (congrArg PastingDiagram.dim e).trans_le hd
  have hN := (isMoleculeIn_map_iff (h.sphereEmb α) ⊤).2 (cond α t.shape s.shape).isMolecule
  obtain ⟨ys, hys⟩ := exists_isLayerOrder_of_krullDim_le hN (by
    rw [krullDim_map, LowerSet.krullDim_top]
    exact (cond α t.shape s.shape).krullDim_eq_dimension.trans_le (by exact_mod_cast hd'))
  rw [← PastingDiagram.nerveComposite_congr (PastingDiagram.equiv_of_eq e) hd' hd,
    h.nerveComposite_restrictAlong_sphere α hd' hys hr₀ hr₁]
  have hb : OGP.map (incl (P := h.cellShape.rdc.obj.toOGP) (h.cellShape.ogp.bdryFull ⊤))
      ((h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP.boundary
        (OGP.map (h.sphereEmb α) ⊤) 1 false) =
      h.cellShape.rdc.obj.toOGP.boundary (.Iic h.cellShape.top) 1 α := by
    rw [map_boundary, h.map_incl_map_sphereEmb α, hT, boundary_eq_self (by
      refine (krullDim_boundary_le _ _ α).trans ?_
      rw [hs]) false, hs]
  have key := Labelling.mapPath_extendPrefunctor_mapPath h.sphereLabelling b₀ @edge
    (pathOf ((h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP.boundary
        (OGP.map (h.sphereEmb α) ⊤) 1 false) (hN.boundary 1 false)
      ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
      ((hN.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hr₀)
      ((hN.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hr₁))
  have e₂ : (inclMap (P := h.cellShape.rdc.obj.toOGP) (h.cellShape.ogp.bdryFull ⊤)).mapPath
      (pathOf ((h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP.boundary
        (OGP.map (h.sphereEmb α) ⊤) 1 false) (hN.boundary 1 false)
      ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
      ((hN.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hr₀)
      ((hN.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hr₁)) =
      pathOf (P := h.cellShape.rdc.obj.toOGP) (h.cellShape.rdc.obj.toOGP.boundary
          (.Iic h.cellShape.top) 1 α) ((h.cellShape.rdc.obj.isRDC h.cellShape.top).boundary 1 α)
          ((krullDim_boundary_le _ 1 α).trans_eq Nat.cast_one)
          (((h.cellShape.rdc.obj.isRDC h.cellShape.top).isGlobular.boundary_boundary_eq_of_le
            zero_le_one (.inl zero_lt_one)).trans hx₀)
          (((h.cellShape.rdc.obj.isRDC h.cellShape.top).isGlobular.boundary_boundary_eq_of_le
            zero_le_one (.inl zero_lt_one)).trans hx₁) :=
    (Map.mapPath_pathOf_of_isInclusion (incl _) _ (hN.boundary 1 false)
      ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one) _ _).trans (pathOf_congr hb)
  rw [← e₂, Labelling.dom_pathCell]
  exact key.symm

private theorem pathComp_heq_of_heq {a b a' b' : B} {p : Quiver.Path a b}
    {p' : Quiver.Path a' b'} (ha : a = a') (hb : b = b') (hp : p ≍ p') :
    pathComp (𝟭q B) p ≍ pathComp (𝟭q B) p' := by
  subst ha hb
  obtain rfl := eq_of_heq hp
  rfl

private theorem eq_top_of_not_mem {x : h.cellShape.rdc.obj.toOGP}
    (hx : x ∉ h.cellShape.ogp.bdryFull ⊤) : x = h.cellShape.top :=
  not_not.1 fun h' => hx ((Atom.mem_bdryFull_top_iff _ _).2 h')

private theorem boundary_top_of_boundary_Iic {x y : h.cellShape.rdc.obj.toOGP}
    (hx : x ∉ h.cellShape.ogp.bdryFull ⊤) {β : Bool}
    (hy : h.cellShape.rdc.obj.toOGP.boundary (.Iic x) 0 β = .Iic y) :
    h.cellShape.rdc.obj.toOGP.boundary ⊤ 0 β = .Iic y := by
  rw [← h.cellShape.Iic_top, ← h.eq_top_of_not_mem hx]
  exact hy

private def edgeOne (hs : s.dim = 1) (b₀ : B) {v w : EdgeQuiver h.cellShape.rdc.obj.toOGP}
    (e : v ⟶ w) (he : e.1 ∉ h.cellShape.ogp.bdryFull ⊤) :
    h.sphereLabelling.extendObj (P := h.cellShape.rdc.obj.toOGP)
      (hP := h.cellShape.rdc.obj.isRDC) b₀ v ⟶
        h.sphereLabelling.extendObj (hP := h.cellShape.rdc.obj.isRDC) b₀ w :=
  absurd (e.2.1.symm.trans (h.grade_of_not_mem_bdryFull he)) (by omega)

private theorem pathComp_cond_heq (hs : s.dim = 1) (α : Bool) (hd : (cond α t s).dim ≤ 2)
    (b₀ : B) {x : h.cellShape.rdc.obj.toOGP} (hxM : x ∉ h.cellShape.ogp.bdryFull ⊤)
    {x₀ x₁ : h.cellShape.rdc.obj.toOGP}
    (hx₀ : h.cellShape.rdc.obj.toOGP.boundary (.Iic x) 0 false = .Iic x₀)
    (hx₁ : h.cellShape.rdc.obj.toOGP.boundary (.Iic x) 0 true = .Iic x₁) :
    pathComp (𝟭q B) ((cond α t s).nerveComposite hd).dom ≍
      pathComp (h.sphereLabelling.extendPrefunctor (hP := h.cellShape.rdc.obj.isRDC) b₀
          (fun e he => h.edgeOne hs b₀ e he))
        (pathOf (P := h.cellShape.rdc.obj.toOGP) (h.cellShape.rdc.obj.toOGP.boundary
          (.Iic x) 1 α) ((h.cellShape.rdc.obj.isRDC x).boundary 1 α)
          ((krullDim_boundary_le _ 1 α).trans_eq Nat.cast_one)
          (((h.cellShape.rdc.obj.isRDC x).isGlobular.boundary_boundary_eq_of_le
            zero_le_one (.inl zero_lt_one)).trans hx₀)
          (((h.cellShape.rdc.obj.isRDC x).isGlobular.boundary_boundary_eq_of_le
            zero_le_one (.inl zero_lt_one)).trans hx₁)) := by
  have h₀ := h.boundary_top_of_boundary_Iic hxM hx₀
  have h₁ := h.boundary_top_of_boundary_Iic hxM hx₁
  obtain rfl := h.eq_top_of_not_mem hxM
  refine (pathComp_heq_of_heq ?_ ?_ (h.dom_nerveComposite_cond_heq hs α hd b₀
    (fun e he => h.edgeOne hs b₀ e he) hx₀ hx₁)).trans (heq_of_eq (pathComp_mapPath _ _))
  · exact ((h.extendObj_sphereLabelling _ _).trans (h.sphereLabelling_obj_vertex (β := false)
      (.inl (by omega)) hd h₀)).symm
  · exact ((h.extendObj_sphereLabelling _ _).trans (h.sphereLabelling_obj_vertex (β := true)
      (.inl (by omega)) hd h₁)).symm

private noncomputable def labellingOne (hs : s.dim = 1) {a b : B} {P Q : Quiver.Path a b}
    (hsd : s.dim ≤ 2) (htd : t.dim ≤ 2) (hs' : s.nerveComposite hsd = ⟨a, b, P, P, 𝟙 _⟩)
    (ht' : t.nerveComposite htd = ⟨a, b, Q, Q, 𝟙 _⟩)
    (φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q) :
    Labelling B h.cellShape.rdc.obj.toOGP h.cellShape.rdc.obj.isRDC :=
  h.sphereLabelling.extend (P := h.cellShape.rdc.obj.toOGP) (hP := h.cellShape.rdc.obj.isRDC) a
    (fun e he => h.edgeOne hs a e he)
    (fun _ _ _ _ hs₀ ht₀ hxM => Labelling.castHom (f := pathComp (𝟭q B) P)
      (g := pathComp (𝟭q B) Q)
      ((congrArg PathCell.src hs' : (s.nerveComposite hsd).src = a).symm.trans
        ((h.sphereLabelling_obj_vertex (α := false)
        (β := false) (.inr rfl) hsd (h.boundary_top_of_boundary_Iic hxM hs₀)).symm.trans
          (h.extendObj_sphereLabelling _ _).symm))
      ((congrArg PathCell.tgt hs' : (s.nerveComposite hsd).tgt = b).symm.trans
        ((h.sphereLabelling_obj_vertex (α := false)
        (β := true) (.inl (by omega)) hsd (h.boundary_top_of_boundary_Iic hxM ht₀)).symm.trans
          (h.extendObj_sphereLabelling _ _).symm))
      ((congr_arg_heq (fun c : PathCell B => pathComp (𝟭q B) c.dom) hs' :
        pathComp (𝟭q B) (s.nerveComposite hsd).dom ≍ pathComp (𝟭q B) P).symm.trans
        (h.pathComp_cond_heq hs false hsd a hxM hs₀ ht₀))
      ((congr_arg_heq (fun c : PathCell B => pathComp (𝟭q B) c.dom) ht' :
        pathComp (𝟭q B) (t.nerveComposite htd).dom ≍ pathComp (𝟭q B) Q).symm.trans
        (h.pathComp_cond_heq hs true htd a hxM hs₀ ht₀)) φ)

private theorem labellingOne_cell (hs : s.dim = 1) {a b : B} {P Q : Quiver.Path a b}
    (hsd : s.dim ≤ 2) (htd : t.dim ≤ 2) (hs' : s.nerveComposite hsd = ⟨a, b, P, P, 𝟙 _⟩)
    (ht' : t.nerveComposite htd = ⟨a, b, Q, Q, 𝟙 _⟩)
    (φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q) {x : h.cellShape.rdc.obj.toOGP}
    (hxM : x ∉ h.cellShape.ogp.bdryFull ⊤) (hx : grade ℕ x = 2) {x₀ x₁ : h.cellShape.rdc.obj.toOGP}
    (hx₀ : h.cellShape.rdc.obj.toOGP.boundary (.Iic x) 0 false = .Iic x₀)
    (hx₁ : h.cellShape.rdc.obj.toOGP.boundary (.Iic x) 0 true = .Iic x₁) :
    (h.labellingOne hs hsd htd hs' ht' φ).cell x hx hx₀ hx₁ ≍ φ := by
  unfold labellingOne
  exact (heq_of_eq (dif_neg hxM)).trans (Labelling.castHom_heq _ _ _ _ _)

private theorem comap_labellingOne (hs : s.dim = 1) {a b : B} {P Q : Quiver.Path a b}
    (hsd : s.dim ≤ 2) (htd : t.dim ≤ 2) (hs' : s.nerveComposite hsd = ⟨a, b, P, P, 𝟙 _⟩)
    (ht' : t.nerveComposite htd = ⟨a, b, Q, Q, 𝟙 _⟩)
    (φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q) :
    (h.labellingOne hs hsd htd hs' ht' φ).comap (P := (h.cellShape.rdc.restrict
        (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP)
      (inclMap (P := h.cellShape.rdc.obj.toOGP) (h.cellShape.ogp.bdryFull ⊤))
      (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.isRDC = h.sphereLabelling :=
  Labelling.comap_extend _ _ _ _

theorem exists_nerveFiller_one {a b : B} {P Q : Quiver.Path a b} (hs : s.dim = 1)
    (hsd : s.dim ≤ 2) (htd : t.dim ≤ 2) (hs' : s.nerveComposite hsd = ⟨a, b, P, P, 𝟙 _⟩)
    (ht' : t.nerveComposite htd = ⟨a, b, Q, Q, 𝟙 _⟩)
    (φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q) :
    ∃ x : diagram (bicategoryNerve.{w, v, u} B) h.cellShape,
      HasRoundType (PastingDiagram.ofCell x) s t ∧ ∀ hd,
        (PastingDiagram.ofCell x).nerveComposite hd = ⟨a, b, P, Q, φ⟩ := by
  have hU : h.cellShape.dimension = 2 := h.dimension_cellShape.trans (by rw [hs])
  have hcomm : (h.labellingOne hs hsd htd hs' ht' φ).IsCommutative := fun y hy => absurd
    ((h.cellShape.grade_le_dimension y).trans_eq hU) (by omega)
  refine ⟨PastingDiagram.nerveCellOf ⟨_, hcomm⟩, h.hasRoundType_nerveCellOf _
    (h.comap_labellingOne hs hsd htd hs' ht' φ), fun hd => ?_⟩
  have hM : IsMoleculeIn h.cellShape.rdc.obj.toOGP ⊤ := h.cellShape.toMoleculeShape.isMolecule
  have hT : (LowerSet.Iic h.cellShape.top : LowerSet h.cellShape.rdc.obj.toOGP) = ⊤ :=
    h.cellShape.Iic_top
  have hg : grade ℕ h.cellShape.top = 2 := h.cellShape.dimension_eq.symm.trans hU
  have hA := h.cellShape.rdc.obj.isRDC h.cellShape.top
  obtain ⟨ys, hys⟩ := exists_isLayerOrder_of_krullDim_le hM (by
    rw [LowerSet.krullDim_top]
    exact h.cellShape.krullDim_eq_dimension.trans_le (by rw [hU]; rfl))
  have hs₀ := boundary_zero_eq_Iic_vertex (P := h.cellShape.rdc.obj.toOGP) _ hA false
  have ht₀ := boundary_zero_eq_Iic_vertex (P := h.cellShape.rdc.obj.toOGP) _ hA true
  rw [PastingDiagram.nerveComposite_eq_pathCell _ hd (boundary_zero_eq_Iic_vertex _ hM false)
    (boundary_zero_eq_Iic_vertex _ hM true) hys,
    PastingDiagram.bicategoryNerveHomEquiv_ofCell_nerveCellOf]
  refine (@Labelling.pathCell_congr _ _ _ _ _ _ _ _ _ _ _ hT.symm _ hA _ _ _
    (isLayerOrder_Iic hA hg) _ _ _ _ _ _ hs₀ ht₀).trans ?_
  have hnm : h.cellShape.top ∉ h.cellShape.ogp.bdryFull ⊤ :=
    fun hm => (Atom.mem_bdryFull_top_iff _ _).1 hm rfl
  refine PathCell.ext ?_ ?_ ?_ ?_ ?_
  · exact (h.extendObj_sphereLabelling _ _).trans ((h.sphereLabelling_obj_vertex (α := false)
      (β := false) (.inr rfl) hsd (h.boundary_top_of_boundary_Iic hnm hs₀)).trans
        (congrArg PathCell.src hs' : (s.nerveComposite hsd).src = a))
  · exact (h.extendObj_sphereLabelling _ _).trans ((h.sphereLabelling_obj_vertex (α := false)
      (β := true) (.inl (by omega)) hsd (h.boundary_top_of_boundary_Iic hnm ht₀)).trans
        (congrArg PathCell.tgt hs' : (s.nerveComposite hsd).tgt = b))
  · rw [Labelling.dom_pathCell]
    exact (h.dom_nerveComposite_cond_heq hs false hsd a (fun e he => h.edgeOne hs a e he) hs₀
      ht₀).symm.trans (congr_arg_heq PathCell.dom hs' : (s.nerveComposite hsd).dom ≍ P)
  · rw [Labelling.cod_pathCell]
    exact (h.dom_nerveComposite_cond_heq hs true htd a (fun e he => h.edgeOne hs a e he) hs₀
      ht₀).symm.trans (congr_arg_heq PathCell.dom ht' : (t.nerveComposite htd).dom ≍ Q)
  · refine (Labelling.hom_pathCell_heq _ _ _ _ _).trans ?_
    refine (heq_of_eq (Labelling.compositeAlong_Iic (P := h.cellShape.rdc.obj.toOGP) _ hg hs₀
      ht₀)).trans ?_
    exact h.labellingOne_cell hs hsd htd hs' ht' φ hnm hg hs₀ ht₀

end Parallel

namespace PastingDiagram

theorem nerveComposite_nervePointCell (b : B)
    (hd : (ofCell (nervePointCell.{w, v, u} b)).dim ≤ 2) :
    (ofCell (nervePointCell.{w, v, u} b)).nerveComposite hd = ⟨b, b, .nil, .nil, 𝟙 _⟩ := by
  have hd₀ : (ofCell (nervePointCell.{w, v, u} b)).dim = 0 := dimension_atomPoint
  have hM : IsMoleculeIn (ofCell (nervePointCell.{w, v, u} b)).shape.rdc.obj.toOGP ⊤ :=
    (ofCell (nervePointCell.{w, v, u} b)).shape.isMolecule
  have hs := boundary_zero_eq_Iic_vertex _ hM false
  have ht := boundary_zero_eq_Iic_vertex _ hM true
  rw [nerveComposite_of_dim_le_one _ (by omega) hd hs ht]
  have hsub : Subsingleton atomPoint.ogp :=
    atomPoint.toMoleculeShape.subsingleton_of_dimension_eq_zero dimension_atomPoint
  have hobj (y : (ofCell (nervePointCell.{w, v, u} b)).shape.rdc.obj.toOGP) :
      (bicategoryNerveHomEquiv B (ofCell (nervePointCell.{w, v, u} b)).shape.rdc
        (ofCell (nervePointCell.{w, v, u} b)).map).1.toPrefunctor.obj y = b :=
    obj_ofCell _ y
  have hp : ∀ {y z : (ofCell (nervePointCell.{w, v, u} b)).shape.rdc.obj.toOGP}
      (p : Quiver.Path (V := EdgeQuiver _) y z),
      (bicategoryNerveHomEquiv B (ofCell (nervePointCell.{w, v, u} b)).shape.rdc
        (ofCell (nervePointCell.{w, v, u} b)).map).1.toPrefunctor.mapPath p ≍
        (Quiver.Path.nil : Quiver.Path b b) := by
    intro y z p
    cases p with
    | nil => rw [Prefunctor.mapPath_nil, hobj y]
    | cons q e =>
      exact absurd (atomPoint.grade_le_dimension e.1) (by
        rw [dimension_atomPoint, e.2.1]
        omega)
  exact pathCell_nil_ext (hobj (vertex ⊤ hM false)) (hobj (vertex ⊤ hM true))
    (hp (y := vertex ⊤ hM false) (z := vertex ⊤ hM true) _)

end PastingDiagram

namespace Layered.Signature.BicatInterp

variable {S : Signature.{v'}} [DecidableEq S.Pt] {hS : S.WellFormed} (F : S.BicatInterp hS B)

private theorem parallel_nervePointCell (a b : B) :
    Parallel (cellRound (nervePointCell.{w, v, u} a)) (cellRound (nervePointCell.{w, v, u} b)) :=
  ⟨rfl, .inl dimension_atomPoint⟩

private theorem exists_edgeCell (e : S.Ed) :
    ∃ x : diagram (bicategoryNerve.{w, v, u} B) (parallel_nervePointCell
        (F.toPrefunctor.obj (S.edgeSource e)) (F.toPrefunctor.obj (S.edgeTarget e))).cellShape,
      HasRoundType (PastingDiagram.ofCell x)
        (cellRound (nervePointCell.{w, v, u} (F.toPrefunctor.obj (S.edgeSource e))))
        (cellRound (nervePointCell.{w, v, u} (F.toPrefunctor.obj (S.edgeTarget e)))) ∧ ∀ hd,
        (PastingDiagram.ofCell x).nerveComposite hd =
          ⟨_, _, (F.toPrefunctor.map (⟨e, rfl, rfl⟩ : Quiver.Hom (V := S.GenQuiver)
            (S.edgeSource e) (S.edgeTarget e))).toPath, (F.toPrefunctor.map (⟨e, rfl, rfl⟩ :
              Quiver.Hom (V := S.GenQuiver) (S.edgeSource e) (S.edgeTarget e))).toPath, 𝟙 _⟩ :=
  (parallel_nervePointCell _ _).exists_nerveFiller_zero dimension_atomPoint
    (dimension_atomPoint.trans_le (Nat.zero_le 2)) (dimension_atomPoint.trans_le (Nat.zero_le 2))
    (PastingDiagram.nerveComposite_nervePointCell _ _)
    (PastingDiagram.nerveComposite_nervePointCell _ _) _

noncomputable def toPathInterp : S.PathInterp (bicategoryNerve.{w, v, u} B) where
  point x := nervePointCell (F.toPrefunctor.obj x)
  edge e := ⟨_, (F.exists_edgeCell e).choose⟩
  hasRoundType_edge e := (F.exists_edgeCell e).choose_spec.1

private theorem map_toGenPrefunctor_toPathInterp (g : S.Ed) :
    F.toPathInterp.toGenPrefunctor.map (⟨g, rfl, rfl⟩ : Quiver.Hom (V := S.GenQuiver)
      (S.edgeSource g) (S.edgeTarget g)) =
    F.toPrefunctor.map (⟨g, rfl, rfl⟩ : Quiver.Hom (V := S.GenQuiver)
      (S.edgeSource g) (S.edgeTarget g)) := by
  have hd : (F.toPathInterp.ofEdge (.gen g)).dim ≤ 2 :=
    (F.toPathInterp.dim_ofEdge (.gen g)).trans_le one_le_two
  have e := (F.toPathInterp.nerveComposite_ofEdge_gen g hd).symm.trans
    ((F.exists_edgeCell g).choose_spec.2 hd)
  obtain ⟨-, -, hP, -, -⟩ := PathCell.mk.inj e
  exact eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons (eq_of_heq hP))

theorem toGenPrefunctor_toPathInterp : F.toPathInterp.toGenPrefunctor = F.toPrefunctor := by
  refine Prefunctor.hext (fun _ => rfl) fun x y g => ?_
  obtain ⟨g, rfl, rfl⟩ := g
  exact heq_of_eq (F.map_toGenPrefunctor_toPathInterp g)

private theorem pathComp_label_toPathInterp {x y : S.Pt} (p : Quiver.Path (V := S.PathQuiver) x y) :
    pathComp F.toPathInterp.label p = pathComp F.label p :=
  eq_of_heq (congr_arg_heq (fun G => pathComp (S.freePrefunctor ⋙q (lift G).toPrefunctor) p)
    F.toGenPrefunctor_toPathInterp)

private theorem pathEnds_cellSource (c : S.Ce) :
    S.pathEnds (S.cellSource c) = some (S.cellEnds hS c) :=
  (Option.some_get _).symm

private theorem isPath_cellTarget_of (hS : S.WellFormed) (c : S.Ce) :
    S.IsPath (S.cellTarget c) := by
  rw [IsPath, ← (hS c).2]
  exact (hS c).1

private theorem parallel_pathRound (c : S.Ce) :
    Parallel (F.toPathInterp.pathRound _ (hS c).1)
      (F.toPathInterp.pathRound _ (isPath_cellTarget_of hS c)) :=
  HasRoundType.parallel (F.toPathInterp.hasRoundType_path _ (pathEnds_cellSource (hS := hS) c))
    (F.toPathInterp.hasRoundType_path _ ((hS c).2.symm.trans (pathEnds_cellSource (hS := hS) c)))

private noncomputable def cellHom (c : S.Ce) :
    pathComp (𝟭q B) (F.toPathInterp.label.mapPath (S.toPath _ (S.walk_cellSource hS c))) ⟶
      pathComp (𝟭q B) (F.toPathInterp.label.mapPath (S.toPath _ (S.walk_cellTarget hS c))) :=
  eqToHom ((pathComp_mapPath F.toPathInterp.label _).trans (F.pathComp_label_toPathInterp _)) ≫
    F.cell c ≫ eqToHom ((pathComp_mapPath F.toPathInterp.label _).trans
      (F.pathComp_label_toPathInterp _)).symm

private theorem exists_cellCell (c : S.Ce) :
    ∃ x : diagram (bicategoryNerve.{w, v, u} B) (F.parallel_pathRound c).cellShape,
      HasRoundType (PastingDiagram.ofCell x) (F.toPathInterp.pathRound _ (hS c).1)
        (F.toPathInterp.pathRound _ (isPath_cellTarget_of hS c)) ∧ ∀ hd,
        (PastingDiagram.ofCell x).nerveComposite hd = ⟨_, _, _, _, F.cellHom c⟩ :=
  (F.parallel_pathRound c).exists_nerveFiller_one (F.toPathInterp.dim_path (hS c).1)
    ((F.toPathInterp.dim_path (hS c).1).trans_le one_le_two)
    ((F.toPathInterp.dim_path (isPath_cellTarget_of hS c)).trans_le one_le_two)
    (F.toPathInterp.nerveComposite_path _ (pathEnds_cellSource (hS := hS) c)
      ((F.toPathInterp.dim_path (hS c).1).trans_le one_le_two))
    (F.toPathInterp.nerveComposite_path _ ((hS c).2.symm.trans (pathEnds_cellSource (hS := hS) c))
      ((F.toPathInterp.dim_path (isPath_cellTarget_of hS c)).trans_le one_le_two))
    (F.cellHom c)

noncomputable def toInterp : S.Interp (bicategoryNerve.{w, v, u} B) where
  toPathInterp := F.toPathInterp
  cell c := ⟨_, (F.exists_cellCell c).choose⟩
  hasRoundType_cell c _ _ := (F.exists_cellCell c).choose_spec.1

theorem reading_toInterp : F.toInterp.reading hS = F := by
  refine BicatInterp.ext F.toGenPrefunctor_toPathInterp fun c => ?_
  have hd := (F.toInterp.dim_cell hS c).le
  have e := (F.toInterp.nerveComposite_cell hS c hd).symm.trans
    ((F.exists_cellCell c).choose_spec.2 hd)
  obtain ⟨-, -, -, -, hh⟩ := PathCell.mk.inj e
  exact (((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm.trans hh).trans
    ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _))

end Layered.Signature.BicatInterp

namespace Layered

variable {S : RelSignature.{v'}} [DecidableEq S.Pt] [DecidableEq S.Ed] {hS : S.WellFormed}

def Signature.BicatInterp.Satisfies (hS : S.WellFormed) (F : S.toSignature.BicatInterp hS.1 B) :
    Prop :=
  ∀ (r : S.Rel) {x y : S.Pt} (hx : S.pathEnds (S.relSource r).source = some (x, y))
    {q : List (Edge S.Pt S.Ed)} (hq : S.target (S.relSource r) = some q),
    let hx' := (congrArg S.pathEnds (hS.2 r).source_eq).symm.trans hx
    let hq' := (hS.2 r).target_eq.symm.trans hq
    PathCell.ofHom F.label (S.toPath _ (S.walk_of_pathEnds hx))
        (S.toPath q (S.walk_of_pathEnds (S.pathEnds_target hS.1 hq hx)))
        (F.evalB (S.relSource r) hx hq) =
      PathCell.ofHom F.label (S.toPath _ (S.walk_of_pathEnds hx'))
        (S.toPath q (S.walk_of_pathEnds (S.pathEnds_target hS.1 hq' hx')))
        (F.evalB (S.relTarget r) hx' hq')

theorem Signature.BicatInterp.satisfies_rel_of_heq (hS : S.WellFormed)
    (F : S.toSignature.BicatInterp hS.1 B) {r : S.Rel}
    {d d' : Diagram S.Pt S.Ed S.Ce} (hd : S.relSource r = d) (hd' : S.relTarget r = d')
    {x₀ y₀ : S.Pt} {q₀ : List (Edge S.Pt S.Ed)} (hx₀ : S.pathEnds d.source = some (x₀, y₀))
    (hx₀' : S.pathEnds d'.source = some (x₀, y₀)) (hq₀ : S.target d = some q₀)
    (hq₀' : S.target d' = some q₀) (h : F.evalB d hx₀ hq₀ ≍ F.evalB d' hx₀' hq₀') {x y : S.Pt}
    (hx : S.pathEnds (S.relSource r).source = some (x, y)) {q : List (Edge S.Pt S.Ed)}
    (hq : S.target (S.relSource r) = some q) :
    PathCell.ofHom F.label (S.toPath _ (S.walk_of_pathEnds hx))
        (S.toPath q (S.walk_of_pathEnds (S.pathEnds_target hS.1 hq hx)))
        (F.evalB (S.relSource r) hx hq) =
      PathCell.ofHom F.label (S.toPath _ (S.walk_of_pathEnds
          ((congrArg S.pathEnds (hS.2 r).source_eq).symm.trans hx)))
        (S.toPath q (S.walk_of_pathEnds (S.pathEnds_target hS.1 ((hS.2 r).target_eq.symm.trans hq)
          ((congrArg S.pathEnds (hS.2 r).source_eq).symm.trans hx))))
        (F.evalB (S.relTarget r) ((congrArg S.pathEnds (hS.2 r).source_eq).symm.trans hx)
          ((hS.2 r).target_eq.symm.trans hq)) := by
  subst hd hd'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hx.symm.trans hx₀))
  obtain rfl := Option.some.inj (hq.symm.trans hq₀)
  exact PathCell.ofHom_congr_heq (S.toPath_congr (hS.2 r).source_eq _ _) rfl h

namespace Signature.BicatInterp

variable (F : S.toSignature.BicatInterp hS.1 B)

private theorem nerveComposite_sideRound (r : S.Rel) (α : Bool) {x y : S.Pt}
    (hx : S.pathEnds (S.side r α).source = some (x, y)) {q : List (Edge S.Pt S.Ed)}
    (hq : S.target (S.side r α) = some q)
    (hd : (RelSignature.sideRound F.toInterp hS r α).dim ≤ 2) :
    (RelSignature.sideRound F.toInterp hS r α).nerveComposite hd =
      PathCell.ofHom F.label (S.toPath _ (S.walk_of_pathEnds hx))
        (S.toPath q (S.walk_of_pathEnds (S.pathEnds_target hS.1 hq hx)))
        (F.evalB (S.side r α) hx hq) := by
  have h := F.toInterp.nerveComposite_diagram hS.1 hx hq _ hd
  rw [F.reading_toInterp] at h
  exact h

private theorem exists_relCell (hF : F.Satisfies hS) (r : S.Rel) :
    ∃ x : diagram (bicategoryNerve.{w, v, u} B)
        (RelSignature.parallel_sideRound F.toInterp hS r).cellShape,
      HasRoundType (PastingDiagram.ofCell x) (RelSignature.sideRound F.toInterp hS r false)
        (RelSignature.sideRound F.toInterp hS r true) := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (hS.2 r).isSome_target
  obtain ⟨x, y, hx⟩ := S.exists_pathEnds_of_isPath (RelSignature.isPath_source_side hS r)
  have hd (α : Bool) : (RelSignature.sideRound F.toInterp hS r α).dim = 2 :=
    F.toInterp.dim_diagram hS.1 ((RelSignature.target_side hS r α).trans hq) _
  refine ((RelSignature.parallel_sideRound F.toInterp hS r).exists_nerveFiller_two_iff (hd false)
    (hd false).le (hd true).le).2 ?_
  rw [F.nerveComposite_sideRound r false hx hq,
    F.nerveComposite_sideRound r true ((congrArg S.pathEnds (hS.2 r).source_eq).symm.trans hx)
      ((hS.2 r).target_eq.symm.trans hq)]
  exact hF r hx hq

noncomputable def toNerve (hF : F.Satisfies hS) : S.Interp hS (bicategoryNerve.{w, v, u} B) where
  toInterp := F.toInterp
  rel r := ⟨_, (F.exists_relCell hF r).choose⟩
  hasRoundType_rel r := (F.exists_relCell hF r).choose_spec

theorem reading_toNerve (hF : F.Satisfies hS) : (F.toNerve hF).toInterp.reading hS.1 = F :=
  F.reading_toInterp

end Signature.BicatInterp

end Layered

end Atoms.Diagrammatic
