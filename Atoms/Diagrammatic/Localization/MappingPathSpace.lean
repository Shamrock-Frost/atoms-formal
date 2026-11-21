import Atoms.Diagrammatic.Localization.PathSpace

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra
open Atoms.Homotopical Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open scoped ReversiblePathSpace

variable {X Y Z : DiagSet.{u}}

private theorem ofCell_map_uliftYonedaEquiv {U : Atom} (φ : ball.{u} U ⟶ Z) :
    (PastingDiagram.ofCell (uliftYonedaEquiv φ)).map = (realizeAtomIso U).hom ≫ φ := by
  rw [PastingDiagram.ofCell_map, Equiv.symm_apply_apply]

private theorem boundary_ofCell_eq_sphereBoundary {U : Atom} (hU : 0 < U.dimension)
    (z : diagram Z U) (α : Bool) :
    (PastingDiagram.ofCell z).boundary (U.dimension - 1) α =
      sphereBoundary U hU (realize.map (U.toMoleculeShape.rdc.restrictIncl (U.ogp.bdryFull ⊤)) ≫
        (PastingDiagram.ofCell z).map) α :=
  (restrictAlong_restrictIncl _ _ _ _).symm

private def sphereRound (U : Atom) (hU : 0 < U.dimension)
    (σ : realize.obj (U.toMoleculeShape.rdc.restrict (U.ogp.bdryFull ⊤)) ⟶ Z) (α : Bool) :
    RoundPastingDiagram Z :=
  ⟨sphereBoundary U hU σ α, U.toMoleculeShape.isRound_boundary U.isAtom.isRound _ α⟩

private theorem dim_sphereRound (U : Atom) (hU : 0 < U.dimension)
    (σ : realize.obj (U.toMoleculeShape.rdc.restrict (U.ogp.bdryFull ⊤)) ⟶ Z) (α : Bool) :
    (sphereRound U hU σ α).dim = U.dimension - 1 :=
  U.toMoleculeShape.dimension_boundary (by omega) α

private theorem sphereRound_mapTo (U : Atom) (hU : 0 < U.dimension)
    (σ : realize.obj (U.toMoleculeShape.rdc.restrict (U.ogp.bdryFull ⊤)) ⟶ Z) (f : Z ⟶ Y)
    (α : Bool) : (sphereRound U hU σ α).mapTo f = sphereRound U hU (σ ≫ f) α :=
  RoundPastingDiagram.ext (congrArg (PastingDiagram.mk _) (Category.assoc _ _ _))

private theorem parallel_of_mapTo_mono {u v : RoundPastingDiagram Z} (m : Z ⟶ Y) [Mono m]
    (h : Parallel (u.mapTo m) (v.mapTo m)) : Parallel u v := by
  obtain ⟨hd, h2⟩ := h
  refine ⟨hd, h2.imp id fun hb α => ?_⟩
  obtain ⟨φ, hφ⟩ := hb α
  refine ⟨φ, (cancel_mono m).1 ?_⟩
  simp only [Category.assoc]
  exact hφ

private theorem parallel_sphereRound (U : Atom) (hU : 0 < U.dimension)
    (σ : realize.obj (U.toMoleculeShape.rdc.restrict (U.ogp.bdryFull ⊤)) ⟶ Z) :
    Parallel (sphereRound U hU σ false) (sphereRound U hU σ true) := by
  let m := realize.{u}.map (U.toMoleculeShape.rdc.restrictIncl (U.ogp.bdryFull ⊤)) ≫
    (realizeAtomIso U).hom
  have : Mono (realize.{u}.map (U.toMoleculeShape.rdc.restrictIncl (U.ogp.bdryFull ⊤))) :=
    mono_realize_map _ Subtype.val_injective
  let t : diagram (ball.{u} U) U := uliftYonedaEquiv (𝟙 _)
  have ht : realize.map (U.toMoleculeShape.rdc.restrictIncl (U.ogp.bdryFull ⊤)) ≫
      (PastingDiagram.ofCell t).map = m := by
    rw [ofCell_map_uliftYonedaEquiv, Category.comp_id]
  have hP := parallel_boundary (P := PastingDiagram.ofCell t) U.isAtom.isRound
    (k := U.dimension - 1) (by change U.toMoleculeShape.dimension = _; omega) false true
  have e (α : Bool) : (⟨(PastingDiagram.ofCell t).boundary (U.dimension - 1) α,
      PastingDiagram.isRound_boundary_of_isRound (u := PastingDiagram.ofCell t)
        (cellRound t).isRound _ α⟩ : RoundPastingDiagram _) =
      (sphereRound U hU (𝟙 _) α).mapTo m := by
    rw [sphereRound_mapTo, Category.id_comp]
    exact RoundPastingDiagram.ext
      ((boundary_ofCell_eq_sphereBoundary hU t α).trans (by rw [ht]; rfl))
  rw [e, e] at hP
  have h := (parallel_of_mapTo_mono m hP).mapTo σ
  rwa [sphereRound_mapTo, sphereRound_mapTo, Category.id_comp] at h

private theorem comp_eq_of_hasRoundType {U : Atom} (hU : 0 < U.dimension)
    {σ : realize.obj (U.toMoleculeShape.rdc.restrict (U.ogp.bdryFull ⊤)) ⟶ Z} {x : diagram Z U}
    (hx : HasRoundType (PastingDiagram.ofCell x) (sphereRound U hU σ false)
      (sphereRound U hU σ true)) :
    realize.map (U.toMoleculeShape.rdc.restrictIncl (U.ogp.bdryFull ⊤)) ≫
      (PastingDiagram.ofCell x).map = σ := by
  obtain ⟨e, he⟩ := exists_iso_extends_of_equiv_boundary hU rfl σ x fun α => by
    have := hx.equiv_boundary_cond (dim_sphereRound U hU σ false) α
    cases α <;> exact this
  rwa [Atom.iso_eq e (Iso.refl U), Iso.refl_hom, op_id, Functor.map_id_apply] at he

private theorem map_eq_of_equiv {S : MoleculeShape} {f g : realize.obj S.rdc ⟶ Z}
    (h : (⟨S, f⟩ : PastingDiagram Z).Equiv ⟨S, g⟩) : f = g := by
  obtain ⟨φ, hφ⟩ := h
  obtain rfl : φ = Iso.refl _ := @Subsingleton.elim _ S.isMolecule.subsingleton_iso _ _
  have e : (RDCpx.isoOfIso (P := S.rdc) (Q := S.rdc) (Iso.refl S.ogp)).hom = 𝟙 _ := by
    ext x
    rfl
  rw [e, realize.map_id, Category.id_comp] at hφ
  exact hφ.symm

private theorem nonempty_iso_toMergerAtom {U : Atom} (hU : 0 < U.toRoundShape.dimension)
    {a b : diagram Z U}
    (h : Parallel (cellRound a) (cellRound b)) :
    Nonempty (h.cellShape ≅ toMergerAtom U.toRoundShape hU) := by
  have hdW : h.cellShape.toMoleculeShape.dimension = U.dimension + 1 := h.dimension_cellShape
  have φ (α : Bool) : Nonempty ((h.cellShape.toMoleculeShape.boundary U.dimension α).ogp ≅
      ((toMergerAtom U.toRoundShape hU).toMoleculeShape.boundary U.dimension α).ogp) := by
    obtain ⟨ψ⟩ := nonempty_iso_boundary_toMergerAtom U hU α
    have hI : map (h.cellShapeEmb α) ⊤ = h.cellShape.ogp.bdry ⊤ α :=
      (h.map_cellShapeEmb α).trans (h.bdry_cellShape α).symm
    refine ⟨h.cellShape.toMoleculeShape.bdryIso hdW α ≪≫
      (isoRestrictOfFintype (h.cellShapeEmb α) hI).symm ≪≫ ?_ ≪≫ ψ.symm⟩
    cases α <;> exact Iso.refl _
  obtain ⟨Θ⟩ := MoleculeShape.nonempty_iso_of_boundary_iso h.cellShape.toMoleculeShape
    (toMergerAtom U.toRoundShape hU).toMoleculeShape (fun α => (φ α).some) h.cellShape.isAtom
    (toMergerAtom U.toRoundShape hU).isAtom hdW (dimension_toMergerAtom _ hU)
  exact ⟨Atom.isoOfOGPIso Θ⟩

private noncomputable def faceIncl {U : Atom} {a b : diagram Z U}
    (h : Parallel (cellRound a) (cellRound b)) :
    Bool → (realize.{u}.obj U.toMoleculeShape.rdc ⟶ ball.{u} h.cellShape)
  | false => realize.map (@RDCpx.ofInclusion U.toMoleculeShape.rdc h.cellShape.toMoleculeShape.rdc
      (h.cellShapeEmb false) (h.instIsInclusionCellShapeEmb false)) ≫ (realizeAtomIso _).hom
  | true => realize.map (@RDCpx.ofInclusion U.toMoleculeShape.rdc h.cellShape.toMoleculeShape.rdc
      (h.cellShapeEmb true) (h.instIsInclusionCellShapeEmb true)) ≫ (realizeAtomIso _).hom

private theorem toMergerInclusion_eq {U : Atom} (hU : 0 < U.toRoundShape.dimension)
    {a b : diagram Z U} (h : Parallel (cellRound a) (cellRound b))
    (e : h.cellShape ≅ toMergerAtom U.toRoundShape hU) :
    faceIncl h false ≫ uliftYoneda.{u}.map e.hom = toMergerInclusion U.toRoundShape hU := by
  let M := toMergerAtom U.toRoundShape hU
  have : IsInclusion (P := U.ogp) (h.cellShapeEmb false) := h.instIsInclusionCellShapeEmb false
  have : IsInclusion (P := U.ogp) (h.cellShapeEmb false ≫ (Atom.isoOGP e).hom) :=
    IsInclusion.comp _ _
  have hd : U.toRoundShape.dimension = (U.dimension - 1) + 1 := (Nat.sub_add_cancel hU).symm
  have hnat : realize.{u}.map (atomToRDCpx.map e.hom) ≫ (realizeAtomIso M).hom =
      (realizeAtomIso h.cellShape).hom ≫ uliftYoneda.{u}.map e.hom := by
    ext T c
    rfl
  have hc : RDCpx.ofInclusion (P := U.toMoleculeShape.rdc) (Q := M.toMoleculeShape.rdc)
      (h.cellShapeEmb false ≫ (Atom.isoOGP e).hom) =
      RDCpx.ofInclusion (P := U.toMoleculeShape.rdc) (Q := h.cellShape.toMoleculeShape.rdc)
        (h.cellShapeEmb false) ≫ atomToRDCpx.map e.hom := by
    ext x
    rfl
  refine map_eq_of_equiv (@PastingDiagram.equiv_of_emb_of_image_eq _ _ _ M.toMoleculeShape.rdc
    (realizeAtomIso M).hom (h.cellShapeEmb false ≫ (Atom.isoOGP e).hom)
    (toMergerInputIncl U.toRoundShape hU) this
    (by exact inferInstanceAs (IsInclusion (U.toRoundShape.inputIncl hd))) ?_ rfl ?_)
  · refine (congrArg (fun t => realize.map t ≫ (realizeAtomIso M).hom) hc).trans ?_
    rw [realize.map_comp, Category.assoc, hnat]
    simp only [faceIncl, Category.assoc]
  · have himg : OGP.map (P := U.ogp) (Q := M.ogp) (h.cellShapeEmb false ≫ (Atom.isoOGP e).hom) ⊤ =
        OGP.map (P := U.ogp) (Q := M.ogp) (U.toRoundShape.inputIncl hd) ⊤ := by
      refine (map_comp (h.cellShapeEmb false) (Atom.isoOGP e).hom ⊤).trans ?_
      rw [(h.map_cellShapeEmb false).trans (h.bdry_cellShape false).symm, map_bdry,
        map_top_of_isIso]
      exact (U.toRoundShape.map_inputIncl hd).symm
    exact himg

private theorem hasLiftingProperty_cellShapeEmb {U : Atom} (hU : 0 < U.toRoundShape.dimension)
    {a b : diagram Z U} (h : Parallel (cellRound a) (cellRound b)) (hW : 0 < h.cellShape.dimension)
    {E B : DiagSet.{u}} (q : E ⟶ B) (hq : compositorGenerators.rlp q) :
    HasLiftingProperty (faceIncl h false ≫ toWalkingEquivalence h.cellShape hW) q := by
  obtain ⟨e⟩ := nonempty_iso_toMergerAtom hU h
  have hM := pos_dimension_toMergerAtom U.toRoundShape hU
  have := hq _ (MorphismProperty.ofHoms.mk (⟨U.toRoundShape, hU⟩ :
    {R : RoundShape // 0 < R.dimension}))
  have w : toMergerInclusion _ hU ≫ toWalkingEquivalence _ hM ≫
      walkingEquivalenceMap hW hM e.symm =
        faceIncl h false ≫ toWalkingEquivalence h.cellShape hW := by
    rw [toWalkingEquivalence_walkingEquivalenceMap]
    refine (congrArg (· ≫ uliftYoneda.{u}.map e.symm.hom ≫ toWalkingEquivalence h.cellShape hW)
      (toMergerInclusion_eq hU h e).symm).trans ?_
    refine (Category.assoc _ _ _).trans (congrArg (faceIncl h false ≫ ·) ?_)
    rw [← CategoryTheory.Functor.map_comp_assoc, Iso.symm_hom, e.hom_inv_id,
      CategoryTheory.Functor.map_id,
      Category.id_comp]
  exact HasLiftingProperty.of_arrow_iso_left (Arrow.isoMk'
    (toMergerInclusion _ hU ≫ toWalkingEquivalence _ hM) _ (Iso.refl _)
    (walkingEquivalenceIso hM hW e).symm ((Category.id_comp _).trans (w.symm.trans
      (Category.assoc _ _ _).symm))) q

private theorem equiv_mapTo_id (v : PastingDiagram Z) : v.Equiv (v.mapTo (𝟙 Z)) := by
  rw [v.mapTo_id]

private theorem exists_walkingEquivalence_faceIncl {U : Atom} (hY : HasWeakComposites Y)
    {a b : diagram Y U} (h : Parallel (cellRound a) (cellRound b))
    (he : Equivalent (cellRound a) (cellRound b)) (hW : 0 < h.cellShape.dimension) :
    ∃ g : walkingEquivalence h.cellShape hW ⟶ Y,
      faceIncl h false ≫ toWalkingEquivalence h.cellShape hW ≫ g = (PastingDiagram.ofCell a).map ∧
      faceIncl h true ≫ toWalkingEquivalence h.cellShape hW ≫ g =
        (PastingDiagram.ofCell b).map := by
  obtain ⟨H, c, hc, hdH, hs, ht⟩ := exists_equivalence_cell_side hY false _ _ he
  have hcT : HasRoundType (PastingDiagram.ofCell c)
      ⟨(cellRound a).toPastingDiagram.mapTo (𝟙 Y), (cellRound a).isRound⟩
      ⟨(cellRound b).toPastingDiagram.mapTo (𝟙 Y), (cellRound b).isRound⟩ :=
    { dim_eq := hdH
      dim_eq_dim := h.1
      source := hs.trans (equiv_mapTo_id _)
      target := ht.trans (equiv_mapTo_id _) }
  let c' := h.reindexCell (𝟙 Y) c hcT
  have hc' : IsEquivalence Y c' := by
    obtain ⟨e, -⟩ := h.exists_iso_hasRoundType (𝟙 Y) c hcT
    have he' : c' = Y.map e.hom.op c := h.reindexCell_eq (𝟙 Y) c hcT e
    rw [he']
    exact (isEquivalence_map_iso_iff e c).2 hc
  have hsq := (h.hasRoundType_ofCell_iff (𝟙 Y) c').1 (h.hasRoundType_reindexCell (𝟙 Y) c hcT)
  rw [Category.comp_id] at hsq
  obtain ⟨g, hg⟩ := (exists_toWalkingEquivalence_comp_eq_iff _ hW hY c').2 hc'
  refine ⟨g, ?_, ?_⟩
  · obtain ⟨-, hm⟩ := PastingDiagram.mk.inj (h.restrictAlong_sphere false)
    refine Eq.trans ?_ (eq_of_heq hm)
    rw [hg, ← hsq, ← realize.map_comp_assoc]
    rfl
  · obtain ⟨-, hm⟩ := PastingDiagram.mk.inj (h.restrictAlong_sphere true)
    refine Eq.trans ?_ (eq_of_heq hm)
    rw [hg, ← hsq, ← realize.map_comp_assoc]
    rfl

private theorem hasRoundType_sphereRound {U : Atom} (hU : 0 < U.dimension) (z : diagram Z U) :
    HasRoundType (PastingDiagram.ofCell z)
      (sphereRound U hU (realize.map (U.toMoleculeShape.rdc.restrictIncl (U.ogp.bdryFull ⊤)) ≫
        (PastingDiagram.ofCell z).map) false)
      (sphereRound U hU (realize.map (U.toMoleculeShape.rdc.restrictIncl (U.ogp.bdryFull ⊤)) ≫
        (PastingDiagram.ofCell z).map) true) where
  dim_eq := by
    rw [dim_sphereRound]
    change U.dimension = _
    omega
  dim_eq_dim := (dim_sphereRound U hU _ false).trans (dim_sphereRound U hU _ true).symm
  source := by
    rw [dim_sphereRound, boundary_ofCell_eq_sphereBoundary hU z false]
    rfl
  target := by
    rw [dim_sphereRound, boundary_ofCell_eq_sphereBoundary hU z true]
    rfl

private theorem hasRoundType_faceIncl {U : Atom} {a b : diagram Z U}
    (h : Parallel (cellRound a) (cellRound b)) {t : diagram X h.cellShape} {x z : diagram X U}
    (hx : faceIncl h false ≫ uliftYonedaEquiv.symm t = (PastingDiagram.ofCell x).map)
    (hz : faceIncl h true ≫ uliftYonedaEquiv.symm t = (PastingDiagram.ofCell z).map) :
    HasRoundType (PastingDiagram.ofCell t) (cellRound x) (cellRound z) where
  dim_eq := h.dimension_cellShape
  dim_eq_dim := rfl
  source := @PastingDiagram.equiv_of_emb_of_image_eq _ _ _ h.cellShape.toMoleculeShape.rdc
    (PastingDiagram.ofCell t).map (h.cellShape.toMoleculeShape.boundaryIncl U.dimension false)
    (h.cellShapeEmb false)
    (inferInstanceAs (IsInclusion (h.cellShape.toMoleculeShape.boundaryIncl U.dimension false)))
    (h.instIsInclusionCellShapeEmb false) rfl
    (by rw [PastingDiagram.ofCell_map, ← Category.assoc]; exact hx)
    ((h.cellShape.toMoleculeShape.map_boundaryIncl_top _ _).trans (h.map_cellShapeEmb false).symm)
  target := @PastingDiagram.equiv_of_emb_of_image_eq _ _ _ h.cellShape.toMoleculeShape.rdc
    (PastingDiagram.ofCell t).map (h.cellShape.toMoleculeShape.boundaryIncl U.dimension true)
    (h.cellShapeEmb true)
    (inferInstanceAs (IsInclusion (h.cellShape.toMoleculeShape.boundaryIncl U.dimension true)))
    (h.instIsInclusionCellShapeEmb true) rfl
    (by rw [PastingDiagram.ofCell_map, ← Category.assoc]; exact hz)
    ((h.cellShape.toMoleculeShape.map_boundaryIncl_top _ _).trans (h.map_cellShapeEmb true).symm)

private theorem exists_lift_of_pos {p : X ⟶ Y} (hJ : compositorGenerators.rlp p)
    (hp : IsOmegaEquivalence p) (hY : HasWeakComposites Y) {U : Atom} (hU : 0 < U.dimension)
    (σ : realize.obj (U.toMoleculeShape.rdc.restrict (U.ogp.bdryFull ⊤)) ⟶ X) (y : diagram Y U)
    (w : σ ≫ p = realize.map (U.toMoleculeShape.rdc.restrictIncl (U.ogp.bdryFull ⊤)) ≫
      (PastingDiagram.ofCell y).map) :
    ∃ z : diagram X U, realize.map (U.toMoleculeShape.rdc.restrictIncl (U.ogp.bdryFull ⊤)) ≫
      (PastingDiagram.ofCell z).map = σ ∧ p.app (op U) z = y := by
  let ι := realize.{u}.map (U.toMoleculeShape.rdc.restrictIncl (U.ogp.bdryFull ⊤))
  have hy : HasRoundType (PastingDiagram.ofCell y) ((sphereRound U hU σ false).mapTo p)
      ((sphereRound U hU σ true).mapTo p) := by
    rw [sphereRound_mapTo, sphereRound_mapTo, w]
    exact hasRoundType_sphereRound hU y
  obtain ⟨x, hx, hxy⟩ := hp.exists_equivalent_of_hasRoundType _ _ (parallel_sphereRound U hU σ) U
    y hy
  have hxσ : ι ≫ (PastingDiagram.ofCell x).map = σ := comp_eq_of_hasRoundType hU hx
  have hpx : ι ≫ (PastingDiagram.ofCell (p.app (op U) x)).map = σ ≫ p := by
    rw [ofCell_app_map, ← hxσ, Category.assoc]
  have hab : Parallel (cellRound (p.app (op U) x)) (cellRound y) := by
    have h₁ := hasRoundType_sphereRound hU (p.app (op U) x)
    have h₂ := hasRoundType_sphereRound hU y
    rw [hpx] at h₁
    rw [← w] at h₂
    exact h₁.parallel h₂
  have hW : 0 < hab.cellShape.dimension := by
    rw [hab.dimension_cellShape]
    exact Nat.succ_pos _
  obtain ⟨g, hg₀, hg₁⟩ := exists_walkingEquivalence_faceIncl hY hab (equivalent_symm hxy) hW
  have := hasLiftingProperty_cellShapeEmb hU hab hW p hJ
  have sq : CommSq (PastingDiagram.ofCell x).map
      (faceIncl hab false ≫ toWalkingEquivalence hab.cellShape hW) p g :=
    ⟨by rw [← ofCell_app_map, Category.assoc, hg₀]⟩
  let T := toWalkingEquivalence hab.cellShape hW ≫ sq.lift
  let z : diagram X U := uliftYonedaEquiv ((realizeAtomIso U).inv ≫ faceIncl hab true ≫ T)
  have hz : (PastingDiagram.ofCell z).map = faceIncl hab true ≫ T := by
    rw [ofCell_map_uliftYonedaEquiv, Iso.hom_inv_id_assoc]
  have ht₀ : faceIncl hab false ≫ uliftYonedaEquiv.symm (uliftYonedaEquiv T) =
      (PastingDiagram.ofCell x).map := by
    rw [Equiv.symm_apply_apply, ← sq.fac_left, Category.assoc]
  have ht₁ : faceIncl hab true ≫ uliftYonedaEquiv.symm (uliftYonedaEquiv T) =
      (PastingDiagram.ofCell z).map := by
    rw [Equiv.symm_apply_apply, hz]
  refine ⟨z, ?_, PastingDiagram.ofCell_map_injective ?_⟩
  · have hT := hasRoundType_faceIncl hab ht₀ ht₁
    have hxz : Parallel (cellRound x) (cellRound z) :=
      ((parallel_boundary (P := PastingDiagram.ofCell (uliftYonedaEquiv T)) (cellRound _).isRound
        (k := U.dimension) hab.dimension_cellShape false true).of_equiv_left
          hT.source.symm).of_equiv_right hT.target.symm
    have hd : (cellRound x).dim = (U.dimension - 1) + 1 := by
      change U.dimension = _
      omega
    refine comp_eq_of_hasRoundType hU
      { dim_eq := by rw [dim_sphereRound]; exact hd
        dim_eq_dim := (dim_sphereRound U hU _ false).trans (dim_sphereRound U hU _ true).symm
        source := ?_
        target := ?_ }
    · rw [dim_sphereRound]
      refine (hxz.equiv_boundary_pred hd false).symm.trans ?_
      change ((PastingDiagram.ofCell x).boundary _ false).Equiv _
      rw [boundary_ofCell_eq_sphereBoundary hU x false, hxσ]
      rfl
    · rw [dim_sphereRound]
      refine (hxz.equiv_boundary_pred hd true).symm.trans ?_
      change ((PastingDiagram.ofCell x).boundary _ true).Equiv _
      rw [boundary_ofCell_eq_sphereBoundary hU x true, hxσ]
      rfl
  · rw [ofCell_app_map, hz, Category.assoc, Category.assoc, sq.fac_right, hg₁]

private theorem subsingleton_of_dimension_eq_zero {U : Atom} (h : U.dimension = 0) :
    Subsingleton U.ogp := by
  have := isIso_toAtomPoint_of_dimension_eq_zero h
  refine ⟨fun x y => ?_⟩
  rw [← Iso.hom_inv_id_apply (asIso (toAtomPoint U)) x,
    ← Iso.hom_inv_id_apply (asIso (toAtomPoint U)) y]
  exact congrArg _ (Subsingleton.elim _ _)

private theorem nonempty_iso_of_dimension_eq_zero {P Q : MoleculeShape} (hP : P.dimension = 0)
    (hQ : Q.dimension = 0) : Nonempty (P.ogp ≅ Q.ogp) := by
  let A := Atom.ofIsAtom P.toFiniteOGP (P.isAtom_of_dimension_eq_zero hP)
  let B := Atom.ofIsAtom Q.toFiniteOGP (Q.isAtom_of_dimension_eq_zero hQ)
  have := isIso_toAtomPoint_of_dimension_eq_zero (U := A) hP
  have := isIso_toAtomPoint_of_dimension_eq_zero (U := B) hQ
  exact ⟨Atom.isoOGP (asIso (toAtomPoint A) ≪≫ (asIso (toAtomPoint B)).symm)⟩

private theorem exists_walkingEquivalence_comp_eq {V W : Atom} (hV : 0 < V.dimension)
    (hW : 0 < W.dimension) (hW₁ : W.dimension = 1) (g : V ⟶ W) :
    ∃ l : walkingEquivalence.{u} V hV ⟶ walkingEquivalence W hW,
      toWalkingEquivalence V hV ≫ l = uliftYoneda.map g ≫ toWalkingEquivalence W hW := by
  by_cases hg : grade ℕ (g V.top) < V.dimension
  · exact ⟨degenerateLift hV g (degenerate_of_grade_lt g hg) ≫ toWalkingEquivalence W hW, by
      rw [← Category.assoc, toWalkingEquivalence_degenerateLift]⟩
  · obtain ⟨W', q, i, hq, hi, rfl⟩ := exists_collapse_inclusion_factorization g
    have h₁ : grade ℕ (i (q V.top)) = W'.dimension := by
      rw [grade_eq_of_isInclusionHom i hi, hq.apply_top, W'.dimension_eq]
    have h₂ : grade ℕ (i (q V.top)) ≤ W.dimension := by
      rw [W.dimension_eq]
      exact grade_mono (W.le_top _)
    have h₃ : grade ℕ (i (q V.top)) ≤ V.dimension := grade_apply_top_le (q ≫ i)
    have h₄ : ¬ grade ℕ (i (q V.top)) < V.dimension := hg
    have : IsIso q := isIso_of_isCollapseHom_of_dimension_eq q hq (by omega)
    have : IsIso i := isIso_of_isInclusionHom_of_dimension_eq i hi (by omega)
    exact ⟨walkingEquivalenceMap hW hV (asIso (q ≫ i)),
      toWalkingEquivalence_walkingEquivalenceMap hW hV _⟩

private theorem uliftYonedaEquiv_symm_up {V W : Atom} (g : V ⟶ W) :
    uliftYonedaEquiv.symm (ULift.up g : diagram (ball.{u} W) V) = uliftYoneda.map g := by
  ext
  rfl

theorem exists_reversibleCylinder_map {U W : Atom} (hW : 0 < W.dimension)
    (hW₁ : W.dimension = 1) (θ : grayCylinder.obj U ≅ W) :
    ∃ h : reversibleCylinder.{u}.I.obj (ball U) ⟶ walkingEquivalence W hW, ∀ ε,
      (reversibleCylinder.endpoint ε).app (ball U) ≫ h =
        uliftYoneda.{u}.map ((grayEndpoint ε).app U ≫ θ.hom) ≫ toWalkingEquivalence W hW := by
  let P := (MarkedPresheaf.flat atomMarking).obj (ball.{u} U)
  let φ : (markedCylinder.obj P).underlying ⟶ ball (grayCylinder.obj U) :=
    markedCylinderForgetIso.hom.app P ≫ grayCylinderFunctorYonedaIso.hom.app U
  let f := φ ≫ uliftYoneda.map θ.hom ≫ toWalkingEquivalence W hW
  have key (V : Atom) (x : (markedCylinder.obj P).underlying.obj (op V)) :
      uliftYonedaEquiv.symm x ≫ f =
        uliftYoneda.map ((φ.app _ x).down ≫ θ.hom) ≫ toWalkingEquivalence W hW := by
    rw [uliftYonedaEquiv_symm_comp_assoc, uliftYoneda.map_comp, Category.assoc]
    exact congrArg (· ≫ _) (uliftYonedaEquiv_symm_up (φ.app _ x).down)
  obtain ⟨h, hh, -⟩ := exists_toLoc_comp_eq (markedCylinder.obj P) f
    (fun V hV x _ _ => (exists_walkingEquivalence_comp_eq hV hW hW₁
      ((φ.app _ x).down ≫ θ.hom)).choose)
    (fun V hV x _ _ => by
      rw [(exists_walkingEquivalence_comp_eq hV hW hW₁ ((φ.app _ x).down ≫ θ.hom)).choose_spec,
        key])
  refine ⟨h, fun ε => ?_⟩
  have e₂ : MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app P) ≫
      markedCylinderForgetIso.hom.app P = (grayCylinderEndpoint ε).app (ball U) :=
    NatTrans.congr_app (whiskerRight_endpoint_forget_comp_markedCylinderForgetIso_hom ε) P
  have s₁ : (toLoc P ≫ Loc.map ((markedExactCylinder.endpoint ε).app P)) ≫ h =
      MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app P) ≫ f := by
    refine (congrArg (· ≫ h) (toLoc_naturality ((markedExactCylinder.endpoint ε).app P))).trans ?_
    exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hh)
  have s₂ : MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app P) ≫ f =
      ((grayCylinderEndpoint ε).app (ball U) ≫ grayCylinderFunctorYonedaIso.hom.app U) ≫
        uliftYoneda.map θ.hom ≫ toWalkingEquivalence W hW := by
    rw [← e₂]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Category.assoc _ _ _).symm)
  rw [grayCylinderEndpoint_app_ball, ← Category.assoc, ← uliftYoneda.map_comp] at s₂
  exact s₁.trans s₂

private noncomputable def faceHom {U : Atom} {a b : diagram Z U}
    (h : Parallel (cellRound a) (cellRound b)) :
    Bool → (U ⟶ h.cellShape)
  | false => @Atom.ofInclusion U h.cellShape (h.cellShapeEmb false)
      (h.instIsInclusionCellShapeEmb false)
  | true => @Atom.ofInclusion U h.cellShape (h.cellShapeEmb true)
      (h.instIsInclusionCellShapeEmb true)

private theorem realizeAtomIso_inv_comp_faceIncl {U : Atom} {a b : diagram Z U}
    (h : Parallel (cellRound a) (cellRound b)) (α : Bool) :
    (realizeAtomIso U).inv ≫ faceIncl h α = uliftYoneda.{u}.map (faceHom h α) := by
  rw [Iso.inv_comp_eq]
  cases α <;> rfl

private theorem eq_faceHom_or_eq_faceHom {U : Atom} (hU : U.dimension = 0) {a b : diagram Z U}
    (h : Parallel (cellRound a) (cellRound b)) (hW : h.cellShape.dimension = 1)
    (v : U ⟶ h.cellShape)
    (hv : grade ℕ (v U.top) = 0) : v = faceHom h false ∨ v = faceHom h true := by
  have := subsingleton_of_dimension_eq_zero hU
  have hne : v U.top ≠ h.cellShape.top := fun e => by
    rw [e, ← h.cellShape.dimension_eq] at hv
    omega
  have key (α : Bool) (hm : v U.top ∈ h.cellShape.ogp.bdry ⊤ α) : v = faceHom h α := by
    rw [h.bdry_cellShape α, ← h.map_cellShapeEmb α] at hm
    obtain ⟨y, -, hy⟩ := hm
    refine Atom.hom_ext fun x => ?_
    rw [Subsingleton.elim x U.top]
    cases α
    · exact hy.symm.trans (congrArg (h.cellShapeEmb false) (Subsingleton.elim (α := U.ogp) _ _))
    · exact hy.symm.trans (congrArg (h.cellShapeEmb true) (Subsingleton.elim (α := U.ogp) _ _))
  rcases (h.cellShape.mem_bdryFull_top_iff _).2 hne with hm | hm
  · exact Or.inl (key false hm)
  · exact Or.inr (key true hm)

private theorem exists_lift_of_eq_zero {p : X ⟶ Y} {U : Atom}
    (hI : ∀ ε, HasLiftingProperty ((reversibleCylinder.{u}.endpoint ε).app (ball U)) p)
    (hp : IsOmegaEquivalence p) (hY : HasWeakComposites Y) (hU : U.dimension = 0)
    (y : diagram Y U) : ∃ z : diagram X U, p.app (op U) z = y := by
  obtain ⟨x, hx⟩ := hp.exists_equivalent_of_dimension_eq_zero U hU y
  have hab : Parallel (cellRound (p.app (op U) x)) (cellRound y) := ⟨rfl, Or.inl hU⟩
  have hW₁ : hab.cellShape.dimension = 1 := by
    rw [hab.dimension_cellShape]
    exact congrArg (· + 1) hU
  have hW : 0 < hab.cellShape.dimension := by omega
  obtain ⟨g, hg₀, hg₁⟩ := exists_walkingEquivalence_faceIncl hY hab (equivalent_symm hx) hW
  obtain ⟨θ⟩ : Nonempty (grayCylinder.obj U ≅ hab.cellShape) := by
    have hG : (grayCylinder.obj U).toMoleculeShape.dimension = 0 + 1 :=
      (dimension_grayCylinder_obj U).trans (congrArg (· + 1) hU)
    obtain ⟨Θ⟩ := MoleculeShape.nonempty_iso_of_boundary_iso (grayCylinder.obj U).toMoleculeShape
      hab.cellShape.toMoleculeShape (n := 0) (fun α => (nonempty_iso_of_dimension_eq_zero
        (MoleculeShape.dimension_boundary _ (Nat.zero_le _) α)
        (MoleculeShape.dimension_boundary _ (Nat.zero_le _) α)).some)
      (grayCylinder.obj U).isAtom hab.cellShape.isAtom hG hW₁
    exact ⟨Atom.isoOfOGPIso Θ⟩
  obtain ⟨h, hh⟩ := exists_reversibleCylinder_map.{u} hW hW₁ θ
  have hv (ε : Bool) : grade ℕ (((grayEndpoint ε).app U ≫ θ.hom) U.top) = 0 := by
    change grade ℕ (θ.hom ((grayEndpoint ε).app U U.top)) = 0
    rw [grade_eq_of_isInclusionHom θ.hom (Function.LeftInverse.injective (Iso.hom_inv_id_apply θ)),
      grade_eq_of_isInclusionHom _ (isInclusionHom_grayEndpoint ε U), ← U.dimension_eq, hU]
  have hne : (grayEndpoint false).app U ≫ θ.hom ≠ (grayEndpoint true).app U ≫ θ.hom := fun e => by
    have h₁ := congrArg (fun φ : U ⟶ hab.cellShape => θ.inv (φ U.top)) e
    change θ.inv (θ.hom ((grayEndpoint false).app U U.top)) =
      θ.inv (θ.hom ((grayEndpoint true).app U U.top)) at h₁
    rw [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply] at h₁
    have h₂ := congrArg (cylAtomIso U).inv h₁
    rw [symm_grayEndpoint_apply, symm_grayEndpoint_apply] at h₂
    exact Bool.false_ne_true (SuspCarrier.pole.inj (Prod.mk.inj h₂).1)
  obtain ⟨ε, hε, hε'⟩ : ∃ ε, (grayEndpoint ε).app U ≫ θ.hom = faceHom hab false ∧
      (grayEndpoint (!ε)).app U ≫ θ.hom = faceHom hab true := by
    rcases eq_faceHom_or_eq_faceHom hU hab hW₁ _ (hv false) with h₀ | h₀ <;>
      rcases eq_faceHom_or_eq_faceHom hU hab hW₁ _ (hv true) with h₁ | h₁
    · exact absurd (h₀.trans h₁.symm) hne
    · exact ⟨false, h₀, h₁⟩
    · exact ⟨true, h₁, h₀⟩
    · exact absurd (h₀.trans h₁.symm) hne
  have he (β α : Bool) (hβ : (grayEndpoint β).app U ≫ θ.hom = faceHom hab α) :
      (reversibleCylinder.endpoint β).app (ball U) ≫ h ≫ g =
        (realizeAtomIso U).inv ≫ faceIncl hab α ≫ toWalkingEquivalence hab.cellShape hW ≫ g := by
    rw [← Category.assoc, hh, hβ, ← realizeAtomIso_inv_comp_faceIncl, Category.assoc,
      Category.assoc]
    rfl
  have sq : CommSq (uliftYonedaEquiv.symm x) ((reversibleCylinder.endpoint ε).app (ball U)) p
      (h ≫ g) := ⟨by
    rw [he ε false hε, hg₀, PastingDiagram.ofCell_map, Iso.inv_hom_id_assoc,
      uliftYonedaEquiv_symm_comp]⟩
  have := hI ε
  refine ⟨uliftYonedaEquiv ((reversibleCylinder.endpoint (!ε)).app (ball U) ≫ sq.lift), ?_⟩
  rw [← uliftYonedaEquiv_comp, Category.assoc, sq.fac_right, he (!ε) true hε', hg₁,
    PastingDiagram.ofCell_map, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

private theorem nonempty_arrow_iso_sphereInclusion (U : Atom) :
    Nonempty (Arrow.mk (realize.{u}.map (U.toMoleculeShape.rdc.restrictIncl (U.ogp.bdryFull ⊤))) ≅
      Arrow.mk (sphereInclusion.{u} U)) := by
  have key : ∀ B : Subfunctor (ball.{u} U), closedSubpresheaf U (U.ogp.bdryFull ⊤) = B →
      Nonempty (Arrow.mk (realize.{u}.map (U.toMoleculeShape.rdc.restrictIncl
        (U.ogp.bdryFull ⊤))) ≅ Arrow.mk B.ι) := by
    rintro B rfl
    exact ⟨Arrow.isoMk (realizeRestrictIso (atomToRDCpx.obj U) _ _ rfl ≪≫
      realizeSubsetAtomIso U _) (realizeAtomIso U) (by ext T g; rfl)⟩
  exact key _ (closedSubpresheaf_univ_erase_top U)

private theorem realize_hom_ext_of_dimension_eq_zero {U : Atom} (hU : U.dimension = 0)
    (f g : realize.{u}.obj (U.toMoleculeShape.rdc.restrict (U.ogp.bdryFull ⊤)) ⟶ Z) : f = g := by
  have := subsingleton_of_dimension_eq_zero hU
  ext T c
  exfalso
  have h := (ConcreteCategory.hom c.down.hom T.unop.top).2
  exact (U.mem_bdryFull_top_iff _).1 h (Subsingleton.elim _ _)

theorem trivialFibration_of_isOmegaEquivalence (n : ℕ∞) {p : X ⟶ Y}
    [Fibration ((DiagSet.toInfty n).map p)] (hp : IsOmegaEquivalence p)
    (hY : HasWeakComposites Y) : (monomorphisms DiagSet.{u}).rlp p := by
  have hS := inftyGenerators_le_monomorphisms.{u} n
  have hA : ∀ {A B : DiagSet.{u}} (j : A ⟶ B),
      reversibleCylinder.{u}.anodyne (inftyGenerators.{u} n) j → HasLiftingProperty j p := by
    intro A B j hj
    have hF := (fibration_iff ((DiagSet.toInfty n).map p)).1 inferInstance
    rw [← trivialCofibrations_rlp] at hF
    exact hF j
      ⟨reversibleCylinder.anodyne_le_monomorphisms _ hS j hj,
        reversibleCylinder.anodyne_le_weakEquivalences _ hS j hj⟩
  have hJ : compositorGenerators.rlp p := fun _ _ j hj =>
    hA j (reversibleCylinder.le_anodyne _ j (Or.inl hj))
  suffices h : ∀ U : Atom, HasLiftingProperty (sphereInclusion.{u} U) p by
    rw [monomorphisms_eq_saturation_sphereInclusions, MorphismProperty.rlp_saturation]
    rintro _ _ _ ⟨U⟩
    exact h U
  intro U
  obtain ⟨e⟩ := nonempty_arrow_iso_sphereInclusion.{u} U
  suffices HasLiftingProperty
      (realize.{u}.map (U.toMoleculeShape.rdc.restrictIncl (U.ogp.bdryFull ⊤))) p from
    HasLiftingProperty.of_arrow_iso_left e p
  refine ⟨fun {f g} sq => ?_⟩
  let y : diagram Y U := uliftYonedaEquiv ((realizeAtomIso U).inv ≫ g)
  have hy : (PastingDiagram.ofCell y).map = g := by
    rw [ofCell_map_uliftYonedaEquiv, Iso.hom_inv_id_assoc]
  have key : ∀ z : diagram X U, (realize.map (U.toMoleculeShape.rdc.restrictIncl
      (U.ogp.bdryFull ⊤)) ≫ (PastingDiagram.ofCell z).map = f) → p.app (op U) z = y →
        sq.HasLift := fun z hz hpz =>
    CommSq.HasLift.mk' ⟨(PastingDiagram.ofCell z).map, hz, by rw [← ofCell_app_map, hpz, hy]⟩
  rcases Nat.eq_zero_or_pos U.dimension with hU | hU
  · obtain ⟨z, hz⟩ := exists_lift_of_eq_zero (fun ε =>
      hA _ (reversibleCylinder.{u}.anodyne_endpoint_app (S := inftyGenerators.{u} n) ε
        (ball.{u} U))) hp hY hU y
    exact key z (realize_hom_ext_of_dimension_eq_zero hU _ _) hz
  · obtain ⟨z, hz, hpz⟩ := exists_lift_of_pos hJ hp hY hU f y (by rw [hy]; exact sq.w)
    exact key z hz hpz

section MappingPathSpace

variable (f : X ⟶ Y)

noncomputable abbrev reversibleMappingPathSpace : DiagSet.{u} :=
  pullback f ((π̃ false).app Y)

noncomputable def reversibleMappingPathSpaceIncl : X ⟶ reversibleMappingPathSpace f :=
  pullback.lift (𝟙 X) (f ≫ (ν̃).app Y) (by
    rw [Category.assoc, reversibleCylinder.pathConstant_app_comp_pathEndpoint_app, Category.comp_id,
      Category.id_comp])

noncomputable def reversibleMappingPathSpaceProj : reversibleMappingPathSpace f ⟶ Y :=
  pullback.snd _ _ ≫ (π̃ true).app Y

@[reassoc (attr := simp)]
theorem reversibleMappingPathSpaceIncl_fst :
    reversibleMappingPathSpaceIncl f ≫ pullback.fst _ _ = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem reversibleMappingPathSpaceIncl_proj :
    reversibleMappingPathSpaceIncl f ≫ reversibleMappingPathSpaceProj f = f := by
  rw [reversibleMappingPathSpaceProj, reversibleMappingPathSpaceIncl, pullback.lift_snd_assoc,
    Category.assoc, reversibleCylinder.pathConstant_app_comp_pathEndpoint_app, Category.comp_id]

theorem rlp_monomorphisms_reversibleMappingPathSpace_fst (n : ℕ∞) (hY : IsInftyCategory n Y) :
    (monomorphisms DiagSet.{u}).rlp (pullback.fst f ((π̃ false).app Y)) :=
  (monomorphisms DiagSet.{u}).rlp.of_isPullback (IsPullback.of_hasPullback _ _).flip
    (rlp_monomorphisms_reversiblePathEndpoint_app n hY false)

theorem isOmegaEquivalence_reversibleMappingPathSpaceIncl (n : ℕ∞) (hX : HasWeakComposites X)
    (hY : IsInftyCategory n Y) : IsOmegaEquivalence (reversibleMappingPathSpaceIncl f) :=
  isOmegaEquivalence_of_comp_eq_id (rlp_monomorphisms_reversibleMappingPathSpace_fst f n hY) hX
    (reversibleMappingPathSpaceIncl_fst f)

theorem weakEquivalence_reversibleMappingPathSpaceIncl (n : ℕ∞) (hY : IsInftyCategory n Y) :
    WeakEquivalence ((DiagSet.toInfty n).map (reversibleMappingPathSpaceIncl f)) := by
  have hp : trivialFibrations (DiagSet.Infty.{u} n)
      ((DiagSet.toInfty n).map (pullback.fst f ((π̃ false).app Y))) := by
    rw [← cofibrations_rlp]
    exact rlp_monomorphisms_reversibleMappingPathSpace_fst f n hY
  have : WeakEquivalence ((DiagSet.toInfty n).map (pullback.fst f ((π̃ false).app Y))) :=
    (weakEquivalence_iff _).2 hp.2
  have : WeakEquivalence ((DiagSet.toInfty n).map (reversibleMappingPathSpaceIncl f) ≫
      (DiagSet.toInfty n).map (pullback.fst f ((π̃ false).app Y))) := by
    rw [← Functor.map_comp, reversibleMappingPathSpaceIncl_fst, CategoryTheory.Functor.map_id]
    infer_instance
  exact weakEquivalence_of_postcomp _ ((DiagSet.toInfty n).map (pullback.fst _ _))

private noncomputable def reversibleMappingPathSpaceEnds :
    reversibleMappingPathSpace f ⟶ X ⨯ Y :=
  prod.lift (pullback.fst _ _) (reversibleMappingPathSpaceProj f)

private theorem isPullback_reversibleMappingPathSpaceEnds :
    IsPullback (pullback.snd _ _) (reversibleMappingPathSpaceEnds f)
      (reversibleCylinder.pathEndpoints reversiblePathSpaceAdjunction Y) (prod.map f (𝟙 Y)) := by
  have hl : reversibleMappingPathSpaceEnds f ≫ prod.fst = pullback.fst _ _ := prod.lift_fst _ _
  have hr : reversibleCylinder.pathEndpoints reversiblePathSpaceAdjunction Y ≫ prod.fst =
      (π̃ false).app Y := prod.lift_fst _ _
  refine IsPullback.of_bot (v₂₁ := prod.fst) (v₂₂ := prod.fst) (h₃₁ := f) ?_ ?_ ?_
  · rw [hl, hr]
    exact (IsPullback.of_hasPullback f ((π̃ false).app Y)).flip
  · refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, hr, Category.assoc, prod.map_fst, ← Category.assoc, hl,
        pullback.condition]
    · rw [Category.assoc, Category.assoc, prod.map_snd, Category.comp_id,
        ExactCylinder.pathEndpoints, prod.lift_snd]
      exact (prod.lift_snd _ _).symm
  · refine IsPullback.of_right (h₁₂ := prod.snd) (v₁₃ := terminal.from Y)
      (h₂₂ := terminal.from Y) ?_ (prod.map_fst _ _) ?_
    · rw [prod.map_snd, Category.comp_id, terminal.comp_from]
      exact (IsPullback.of_hasBinaryProduct' X Y).flip
    · exact (IsPullback.of_hasBinaryProduct' Y Y).flip

theorem fibration_reversibleMappingPathSpaceProj (n : ℕ∞) (hX : IsInftyCategory n X)
    (hY : IsInftyCategory n Y) :
    Fibration ((DiagSet.toInfty n).map (reversibleMappingPathSpaceProj f)) := by
  have h₁ : Fibration ((DiagSet.toInfty n).map (reversibleMappingPathSpaceEnds f)) :=
    (fibration_iff _).2 ((fibrations (DiagSet.Infty.{u} n)).of_isPullback
      (isPullback_reversibleMappingPathSpaceEnds f) (fibrations_reversiblePathEndpoints_app n hY))
  have hXf : IsFibrant ((DiagSet.toInfty n).obj X) := (isFibrant_infty_iff n X).2 hX
  have h₂ : Fibration ((DiagSet.toInfty n).map (prod.snd : X ⨯ Y ⟶ Y)) :=
    (fibration_iff _).2 ((fibrations (DiagSet.Infty.{u} n)).of_isPullback
      (IsPullback.of_hasBinaryProduct' X Y) ((fibration_iff _).1 hXf))
  have e : reversibleMappingPathSpaceProj f = reversibleMappingPathSpaceEnds f ≫ prod.snd :=
    (prod.lift_snd _ _).symm
  rw [e, Functor.map_comp]
  infer_instance

theorem weakEquivalence_reversibleMappingPathSpaceProj (n : ℕ∞) (hY : IsInftyCategory n Y)
    [WeakEquivalence ((DiagSet.toInfty n).map f)] :
    WeakEquivalence ((DiagSet.toInfty n).map (reversibleMappingPathSpaceProj f)) :=
  have := weakEquivalence_reversibleMappingPathSpaceIncl f n hY
  weakEquivalence_of_precomp_of_fac (f := (DiagSet.toInfty n).map
    (reversibleMappingPathSpaceIncl f))
    (by rw [← Functor.map_comp, reversibleMappingPathSpaceIncl_proj])

theorem rlp_monomorphisms_reversibleMappingPathSpaceProj (n : ℕ∞) (hX : IsInftyCategory n X)
    (hY : IsInftyCategory n Y) [WeakEquivalence ((DiagSet.toInfty n).map f)] :
    (monomorphisms DiagSet.{u}).rlp (reversibleMappingPathSpaceProj f) :=
  have := fibration_reversibleMappingPathSpaceProj f n hX hY
  have := weakEquivalence_reversibleMappingPathSpaceProj f n hY
  rlp_monomorphisms_of_trivialFibration_toInfty_map n

private theorem equiv_of_equiv_mapTo_pullback {A B C : DiagSet.{u}} {g : A ⟶ C} {h : B ⟶ C}
    {u v : PastingDiagram (pullback g h)}
    (h₁ : (u.mapTo (pullback.fst g h)).Equiv (v.mapTo (pullback.fst g h)))
    (h₂ : (u.mapTo (pullback.snd g h)).Equiv (v.mapTo (pullback.snd g h))) : u.Equiv v := by
  obtain ⟨φ, e₁⟩ := h₁
  obtain ⟨ψ, e₂⟩ := h₂
  obtain rfl : ψ = φ := @Subsingleton.elim _ u.shape.isMolecule.subsingleton_iso _ _
  refine ⟨ψ, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc]
    exact e₁
  · rw [Category.assoc]
    exact e₂

private theorem hasRoundType_of_mapTo_pullback {A B C : DiagSet.{u}} {g : A ⟶ C} {h : B ⟶ C}
    {a : PastingDiagram (pullback g h)} {v w : RoundPastingDiagram (pullback g h)}
    (h₁ : HasRoundType (a.mapTo (pullback.fst g h)) (v.mapTo (pullback.fst g h))
      (w.mapTo (pullback.fst g h)))
    (h₂ : HasRoundType (a.mapTo (pullback.snd g h)) (v.mapTo (pullback.snd g h))
      (w.mapTo (pullback.snd g h))) : HasRoundType a v w where
  dim_eq := h₁.dim_eq
  dim_eq_dim := h₁.dim_eq_dim
  source := equiv_of_equiv_mapTo_pullback
    (by rw [← PastingDiagram.boundary_mapTo]; exact h₁.source)
    (by rw [← PastingDiagram.boundary_mapTo]; exact h₂.source)
  target := equiv_of_equiv_mapTo_pullback
    (by rw [← PastingDiagram.boundary_mapTo]; exact h₁.target)
    (by rw [← PastingDiagram.boundary_mapTo]; exact h₂.target)

private theorem mapTo_mapTo_eq_mapTo_comp {A B C : DiagSet.{u}} (a : RoundPastingDiagram A)
    (g : A ⟶ B) (h : B ⟶ C) : a.mapTo (g ≫ h) = (a.mapTo g).mapTo h :=
  RoundPastingDiagram.ext (PastingDiagram.mapTo_comp _ g h)

private theorem isOmegaEquivalence_reversibleMappingPathSpaceProj (n : ℕ∞)
    (hY : IsInftyCategory n Y) (hf : IsOmegaEquivalence f) :
    IsOmegaEquivalence (reversibleMappingPathSpaceProj f) where
  exists_equivalent_of_dimension_eq_zero V hV y := by
    obtain ⟨x, hx⟩ := hf.exists_equivalent_of_dimension_eq_zero V hV y
    refine ⟨(reversibleMappingPathSpaceIncl f).app _ x, ?_⟩
    have e : (reversibleMappingPathSpaceProj f).app _ ((reversibleMappingPathSpaceIncl f).app _ x) =
        f.app _ x := by
      rw [← NatTrans.comp_app_apply, reversibleMappingPathSpaceIncl_proj]
    rw [e]
    exact hx
  exists_equivalent_of_hasRoundType a b hab V v hv := by
    let fst := pullback.fst f ((π̃ false).app Y)
    let snd := pullback.snd f ((π̃ false).app Y)
    have hc (c : RoundPastingDiagram (reversibleMappingPathSpace f)) :
        (c.mapTo snd).mapTo ((π̃ false).app Y) = (c.mapTo fst).mapTo f := by
      rw [← mapTo_mapTo_eq_mapTo_comp, ← mapTo_mapTo_eq_mapTo_comp, pullback.condition]
    have hv' : HasRoundType (PastingDiagram.ofCell v) ((a.mapTo snd).mapTo ((π̃ true).app Y))
        ((b.mapTo snd).mapTo ((π̃ true).app Y)) := by
      rwa [← mapTo_mapTo_eq_mapTo_comp, ← mapTo_mapTo_eq_mapTo_comp]
    obtain ⟨γ, hγ, hγv⟩ := exists_hasRoundType_app_eq
      (rlp_monomorphisms_reversiblePathEndpoint_app n hY true) (hab.mapTo snd) v hv'
    have hγ' := hγ.mapTo ((π̃ false).app Y)
    rw [← PastingDiagram.ofCell_app, hc, hc] at hγ'
    obtain ⟨x, hx, hxγ⟩ := hf.exists_equivalent_of_hasRoundType _ _ (hab.mapTo fst) V _ hγ'
    have hfx := hx.mapTo f
    rw [← PastingDiagram.ofCell_app, ← hc, ← hc] at hfx
    obtain ⟨γ', hγ'', hγ'x⟩ := exists_hasRoundType_app_eq
      (rlp_monomorphisms_reversiblePathEndpoint_app n hY false) (hab.mapTo snd) _ hfx
    let w : diagram (reversibleMappingPathSpace f) V := uliftYonedaEquiv
      (pullback.lift (uliftYonedaEquiv.symm x) (uliftYonedaEquiv.symm γ') (by
        rw [uliftYonedaEquiv_symm_comp, uliftYonedaEquiv_symm_comp, hγ'x]))
    have hw₁ : fst.app _ w = x := by
      rw [← uliftYonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]
    have hw₂ : snd.app _ w = γ' := by
      rw [← uliftYonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]
    refine ⟨w, hasRoundType_of_mapTo_pullback ?_ ?_, ?_⟩
    · rw [← PastingDiagram.ofCell_app]
      exact hw₁ ▸ hx
    · rw [← PastingDiagram.ofCell_app]
      exact hw₂ ▸ hγ''
    · have h := equivalent_reversiblePathEndpoint_of_equivalent n hY (hγ.parallel hγ'') false
        (by rw [hγ'x]; exact hxγ)
      have e : (reversibleMappingPathSpaceProj f).app _ w = ((π̃ true).app Y).app _ γ' := by
        rw [← hw₂]
        rfl
      rw [e, ← hγv]
      exact h

theorem isOmegaEquivalence_iff_rlp_reversibleMappingPathSpaceProj (n : ℕ∞)
    (hX : IsInftyCategory n X) (hY : IsInftyCategory n Y) :
    IsOmegaEquivalence f ↔ (monomorphisms DiagSet.{u}).rlp (reversibleMappingPathSpaceProj f) := by
  constructor
  · intro hf
    have := fibration_reversibleMappingPathSpaceProj f n hX hY
    exact trivialFibration_of_isOmegaEquivalence n
      (isOmegaEquivalence_reversibleMappingPathSpaceProj f n hY hf) hY.1
  · intro h
    have h' : trivialFibrations (DiagSet.Infty.{u} n)
        ((DiagSet.toInfty n).map (reversibleMappingPathSpaceProj f)) := by
      rw [← cofibrations_rlp]
      exact h
    have := (fibration_iff _).2 h'.1
    have := (weakEquivalence_iff _).2 h'.2
    rw [← reversibleMappingPathSpaceIncl_proj f]
    exact (isOmegaEquivalence_reversibleMappingPathSpaceIncl f n hX.1 hY).comp
      (isOmegaEquivalence_of_trivialFibration n
        ((DiagSet.toInfty n).map (reversibleMappingPathSpaceProj f)))

end MappingPathSpace

end Atoms.Diagrammatic
