import Atoms.Diagrammatic.Marked.HornMaps
import Atoms.Shape.ComparisonHorn

open Atoms.Molecule Atoms.Molecule.OGP Atoms.Molecule.OGP.PartialCylinder
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

theorem ofCell_app_realize {R : RDCpx.{0}} {Y : DiagSet.{u}} (w : realize.obj R ⟶ Y) {T : Atom}
    (c : atomToRDCpx.obj T ⟶ R) : (ofCell (w.app (op T) ⟨c⟩)).map = realize.map c ≫ w := by
  ext ⟨S⟩ ⟨g : atomToRDCpx.obj S ⟶ atomToRDCpx.obj T⟩
  change Y.map (Atom.fullyFaithful.preimage g).op (w.app _ ⟨c⟩) = w.app (op S) ⟨g ≫ c⟩
  exact (NatTrans.naturality_apply w (Atom.fullyFaithful.preimage g).op ⟨c⟩).symm

theorem mem_marked_iff_of_equiv_ofCell {X : MarkedDiagSet.{u}} {U V : Atom}
    {x : diagram X.underlying U} {y : diagram X.underlying V} (h : (ofCell x).Equiv (ofCell y)) :
    x ∈ X.marked U ↔ y ∈ X.marked V := by
  obtain ⟨φ, hφ⟩ := h
  let e : U ≅ V := Atom.fullyFaithful.preimageIso
    (RDCpx.isoOfIso (P := U.toMoleculeShape.rdc) (Q := V.toMoleculeShape.rdc) φ)
  have he : atomToRDCpx.map e.hom = (RDCpx.isoOfIso (P := U.toMoleculeShape.rdc)
      (Q := V.toMoleculeShape.rdc) φ).hom :=
    Atom.fullyFaithful.map_preimage _
  have hx : x = X.underlying.map e.hom.op y := ofCell_map_injective (hφ.symm.trans
    ((congrArg (fun t => realize.map t ≫ (ofCell y).map) he.symm).trans
      (ofCell_map_op_map e.hom y).symm))
  rw [hx]
  exact (X.transport e y).symm

end Atoms.Diagrammatic

namespace Atoms.Shape.MarkedHornData

open Atoms.Diagrammatic

variable (m : MarkedHornData) (hd : 2 ≤ m.atom.dimension) {Y : DiagSet.{u}}

private theorem ofInclusion_incl_hornSet :
    RDCpx.ofInclusion (P := m.hornRDC) (Q := m.atom.toMoleculeShape.rdc) (incl m.hornSet) =
      m.hornIncl := by
  ext
  rfl

private theorem coverCompatible_comparison (z z' : diagram Y m.atom)
    (h : realize.map m.hornIncl ≫ (ofCell z).map = realize.map m.hornIncl ≫ (ofCell z').map) :
    CoverCompatible (R := (m.comparisonMarkedHorn hd).hornRDC) (U := m.atom.toMoleculeShape.rdc)
      (V := m.atom.toMoleculeShape.rdc) (m.comparisonHornEndpoint hd false)
      (m.comparisonHornEndpoint hd true) (ofCell z).map (ofCell z').map :=
  coverCompatible_of_emb (R := (m.comparisonMarkedHorn hd).hornRDC)
    (U := m.atom.toMoleculeShape.rdc) (V := m.atom.toMoleculeShape.rdc) _ _ _ _
    (C := m.hornRDC) (incl m.hornSet) (incl m.hornSet) (m.comparisonHornEndpoint_incl hd)
    (m.map_incl_comp_comparisonHornEndpoint hd) (by rw [m.ofInclusion_incl_hornSet]; exact h)

noncomputable def comparisonHornMap (z z' : diagram Y m.atom)
    (h : realize.map m.hornIncl ≫ (ofCell z).map = realize.map m.hornIncl ≫ (ofCell z').map) :
    realize.obj (m.comparisonMarkedHorn hd).hornRDC ⟶ Y :=
  coverDesc (R := (m.comparisonMarkedHorn hd).hornRDC) (U := m.atom.toMoleculeShape.rdc)
    (V := m.atom.toMoleculeShape.rdc) (m.comparisonHornEndpoint hd false)
    (m.comparisonHornEndpoint hd true) (m.comparisonHornEndpoint_cover hd) (ofCell z).map
    (ofCell z').map (m.coverCompatible_comparison hd z z' h)

theorem ofInclusion_comparisonHornEndpoint_comparisonHornMap (z z' : diagram Y m.atom)
    (h : realize.map m.hornIncl ≫ (ofCell z).map = realize.map m.hornIncl ≫ (ofCell z').map)
    (β : Bool) :
    realize.map (RDCpx.ofInclusion (P := m.atom.toMoleculeShape.rdc)
        (Q := (m.comparisonMarkedHorn hd).hornRDC) (m.comparisonHornEndpoint hd β)) ≫
      m.comparisonHornMap hd z z' h = (ofCell (cond β z' z)).map := by
  cases β
  · exact ofInclusion_coverDesc_left (R := (m.comparisonMarkedHorn hd).hornRDC)
      (U := m.atom.toMoleculeShape.rdc) (V := m.atom.toMoleculeShape.rdc) _ _ _ _ _ _
  · exact ofInclusion_coverDesc_right (R := (m.comparisonMarkedHorn hd).hornRDC)
      (U := m.atom.toMoleculeShape.rdc) (V := m.atom.toMoleculeShape.rdc) _ _ _ _ _ _

private theorem equiv_comparisonHornMap_app (z z' : diagram Y m.atom)
    (h : realize.map m.hornIncl ≫ (ofCell z).map = realize.map m.hornIncl ≫ (ofCell z').map)
    (β : Bool) (v : m.atom.ogp) {a : (m.comparisonMarkedHorn hd).atom.ogp}
    (ha : a ∈ (m.comparisonMarkedHorn hd).hornSet)
    (hav : cylEndpoint m.atom.toMoleculeShape m.hornSet β v = a) :
    (ofCell ((m.comparisonHornMap hd z z' h).app (op _)
      ⟨principalInclusionIn (m.comparisonMarkedHorn hd).atom (m.comparisonMarkedHorn hd).hornSet
        ha⟩)).Equiv (ofCell (Y.map (Atom.closureIncl m.atom v).op (cond β z' z))) := by
  have hmem : ∀ t, Atom.closureInclOGP (m.comparisonMarkedHorn hd).atom a t ∈
      (m.comparisonMarkedHorn hd).hornSet := fun t =>
    (m.comparisonMarkedHorn hd).hornSet.lower
      (closureIncl_mem_closure (m.comparisonMarkedHorn hd).atom a t) ha
  let f := codRestrict (Atom.closureInclOGP (m.comparisonMarkedHorn hd).atom a)
    (m.comparisonMarkedHorn hd).hornSet hmem
  have hf : IsInclusion f := ⟨fun _ _ e => IsInclusion.injective
    (f := Atom.closureInclOGP (m.comparisonMarkedHorn hd).atom a) (congrArg Subtype.val e :)⟩
  let g := Atom.closureInclOGP m.atom v ≫ m.comparisonHornEndpoint hd β
  have hg : IsInclusion g := ⟨fun _ _ e => IsInclusion.injective
    (f := Atom.closureInclOGP m.atom v) (IsInclusion.injective
      (f := m.comparisonHornEndpoint hd β) e)⟩
  refine @equiv_of_emb_of_image_eq _ _ _ (m.comparisonMarkedHorn hd).hornRDC
    (m.comparisonHornMap hd z z' h) f g hf hg ?_ ?_ ?_
  · have H : RDCpx.ofInclusion (P := (Atom.ofClosure (m.comparisonMarkedHorn hd).atom a).rdc)
        (Q := (m.comparisonMarkedHorn hd).hornRDC) f =
        principalInclusionIn (m.comparisonMarkedHorn hd).atom (m.comparisonMarkedHorn hd).hornSet
          ha := by
      ext; rfl
    exact (congrArg (fun t => realize.map t ≫ m.comparisonHornMap hd z z' h) H).trans
      (ofCell_app_realize _ _).symm
  · rw [ofCell_map_op_map, ← m.ofInclusion_comparisonHornEndpoint_comparisonHornMap hd z z' h β,
      ← Category.assoc, ← realize.map_comp]
    exact congrArg (fun t => realize.map t ≫ m.comparisonHornMap hd z z' h) (by ext; rfl)
  · refine map_injective (f := incl (m.comparisonMarkedHorn hd).hornSet) ?_
    have h₁ : f ≫ incl (m.comparisonMarkedHorn hd).hornSet =
        Atom.closureInclOGP (m.comparisonMarkedHorn hd).atom a := by ext; rfl
    have h₂ : g ≫ incl (m.comparisonMarkedHorn hd).hornSet =
        Atom.closureInclOGP m.atom v ≫ cylEndpoint m.atom.toMoleculeShape m.hornSet β := by
      ext; rfl
    have e₁ : map (incl (m.comparisonMarkedHorn hd).hornSet) (map f ⊤) = .Iic a :=
      (map_comp f _ ⊤).symm.trans ((congrArg (map · ⊤) h₁).trans
        (Atom.map_closureInclOGP_top _ _))
    have e₂ : map (incl (m.comparisonMarkedHorn hd).hornSet) (map g ⊤) = .Iic a := by
      refine (map_comp g _ ⊤).symm.trans ((congrArg (map · ⊤) h₂).trans ?_)
      exact (map_comp _ _ ⊤).trans ((congrArg (map _) (Atom.map_closureInclOGP_top _ _)).trans
        ((map_Iic _ _).trans (congrArg LowerSet.Iic hav)))
    exact e₁.trans e₂.symm

theorem marksHorn_comparisonHornMap {X : MarkedDiagSet.{u}} (z z' : diagram X.underlying m.atom)
    (h : realize.map m.hornIncl ≫ (ofCell z).map = realize.map m.hornIncl ≫ (ofCell z').map)
    (hw : m.MarksHorn X (realize.map m.hornIncl ≫ (ofCell z).map)) (hz : z ∈ X.marked m.atom)
    (hz' : z' ∈ X.marked m.atom) :
    (m.comparisonMarkedHorn hd).MarksHorn X (m.comparisonHornMap hd z z' h) := by
  intro a ha
  have hc : m.comparisonIso.hom (m.comparisonIso.inv a) = a := Iso.inv_hom_id_apply _ _
  rcases ha.2 with hT | ⟨β, hβ⟩
  · have hvK : partialCylinderProj _ _ (m.comparisonIso.inv a) ∈ m.hornSet :=
      (m.marking_mem _ hT).1
    have hav : cylEndpoint m.atom.toMoleculeShape m.hornSet false
        (partialCylinderProj _ _ (m.comparisonIso.inv a)) = a :=
      (congrArg m.comparisonIso.hom (eq_endpoint_of_proj_mem _ hvK false)).symm.trans hc
    exact (mem_marked_iff_of_equiv_ofCell
      (m.equiv_comparisonHornMap_app hd z z' h false _ ha.1 hav)).2 (hw _ hT)
  · have hav : cylEndpoint m.atom.toMoleculeShape m.hornSet β m.atom.top = a :=
      (congrArg m.comparisonIso.hom
        ((endpoint_of_notMem β m.top_notMem_hornSet).trans hβ.symm)).trans hc
    refine (mem_marked_iff_of_equiv_ofCell
      (m.equiv_comparisonHornMap_app hd z z' h β _ ha.1 hav)).2 ?_
    obtain ⟨e', he'⟩ := exists_iso_comp_closureIncl (a := m.atom.top) (𝟙 m.atom)
      (Atom.map_top_eq_Iic_iff.1 (Atom.map_top _)) m.atom.dimension_eq
    have hι : Atom.closureIncl m.atom m.atom.top = e'.inv := by
      rw [← Category.id_comp (Atom.closureIncl m.atom m.atom.top), ← e'.inv_hom_id,
        Category.assoc, he', Category.comp_id]
    rw [hι]
    exact (X.transport e'.symm _).1 (by cases β; exacts [hz, hz'])

private theorem equiv_boundary_comparisonFace (z z' : diagram Y m.atom)
    (h : realize.map m.hornIncl ≫ (ofCell z).map = realize.map m.hornIncl ≫ (ofCell z').map)
    (Z : diagram Y m.comparisonAtom)
    (hZ : realize.map (m.comparisonMarkedHorn hd).hornIncl ≫ (ofCell Z).map =
      m.comparisonHornMap hd z z' h) (β : Bool) :
    ((ofCell (Y.map (Atom.closureIncl m.comparisonAtom m.comparisonFace).op Z)).boundary
      (grade ℕ m.face) β).Equiv
      (ofCell (Y.map (Atom.closureIncl m.atom m.face).op (cond β z' z))) := by
  let w := Y.map (Atom.closureIncl m.comparisonAtom m.comparisonFace).op Z
  let f := (ofCell w).shape.boundaryIncl (grade ℕ m.face) β ≫
    Atom.closureInclOGP m.comparisonAtom m.comparisonFace
  have : IsInclusion f := ⟨fun _ _ e => IsInclusion.injective
    (f := (ofCell w).shape.boundaryIncl (grade ℕ m.face) β) (IsInclusion.injective
      (f := Atom.closureInclOGP m.comparisonAtom m.comparisonFace) e)⟩
  let g := Atom.closureInclOGP m.atom m.face ≫ cylEndpoint m.atom.toMoleculeShape m.hornSet β
  have : IsInclusion g := ⟨fun _ _ e => IsInclusion.injective
    (f := Atom.closureInclOGP m.atom m.face) (IsInclusion.injective
      (f := cylEndpoint m.atom.toMoleculeShape m.hornSet β) e)⟩
  refine equiv_of_emb_of_image_eq (C := m.comparisonAtom.toMoleculeShape.rdc) (ofCell Z).map f g
    ?_ ?_ ?_
  · rw [← boundary_comm, ofCell_map_op_map, ← Category.assoc, ← realize.map_comp]
    exact congrArg (fun t => realize.map t ≫ (ofCell Z).map) (by ext; rfl)
  · have e₁ : realize.map (RDCpx.ofInclusion g) ≫ (ofCell Z).map =
        realize.map (atomToRDCpx.map (Atom.closureIncl m.atom m.face) ≫
          RDCpx.ofInclusion (P := m.atom.toMoleculeShape.rdc)
            (Q := (m.comparisonMarkedHorn hd).hornRDC) (m.comparisonHornEndpoint hd β)) ≫
          (realize.map (m.comparisonMarkedHorn hd).hornIncl ≫ (ofCell Z).map) :=
      (congrArg (fun t => realize.map t ≫ (ofCell Z).map)
        (by ext; rfl : RDCpx.ofInclusion (P := (Atom.ofClosure m.atom m.face).toMoleculeShape.rdc)
          (Q := m.comparisonAtom.toMoleculeShape.rdc) g =
          (atomToRDCpx.map (Atom.closureIncl m.atom m.face) ≫
          RDCpx.ofInclusion (P := m.atom.toMoleculeShape.rdc)
            (Q := (m.comparisonMarkedHorn hd).hornRDC) (m.comparisonHornEndpoint hd β)) ≫
            (m.comparisonMarkedHorn hd).hornIncl)).trans
        ((congrArg (· ≫ (ofCell Z).map) (realize.map_comp _ _)).trans (Category.assoc _ _ _))
    rw [e₁, hZ, realize.map_comp, Category.assoc,
      m.ofInclusion_comparisonHornEndpoint_comparisonHornMap hd z z' h β, ← ofCell_map_op_map]
  · rw [map_comp, map_comp, MoleculeShape.map_boundaryIncl_top, map_boundary,
      Atom.map_closureInclOGP_top, Atom.map_closureInclOGP_top]
    exact m.boundary_Iic_comparisonFace hd β

end Atoms.Shape.MarkedHornData

namespace Atoms.Diagrammatic

theorem exists_marked_comparisonCell {X : MarkedDiagSet.{u}} (hH : HasMarkedRLP markedHorns X)
    (m : MarkedHornData) (hd : 2 ≤ m.atom.dimension) {z z' : diagram X.underlying m.atom}
    (h : realize.map m.hornIncl ≫ (ofCell z).map = realize.map m.hornIncl ≫ (ofCell z').map)
    (hw : m.MarksHorn X (realize.map m.hornIncl ≫ (ofCell z).map)) (hz : z ∈ X.marked m.atom)
    (hz' : z' ∈ X.marked m.atom) :
    ∃ w : diagram X.underlying (Atom.ofClosure m.comparisonAtom m.comparisonFace),
      w ∈ X.marked _ ∧
      HasRoundType (ofCell w) (cellRound (X.underlying.map (Atom.closureIncl m.atom m.face).op z))
        (cellRound (X.underlying.map (Atom.closureIncl m.atom m.face).op z')) := by
  obtain ⟨Z, hZ, -, hZf⟩ := hasMarkedRLP_markedHorns_iff_fills.1 hH (m.comparisonMarkedHorn hd)
    (m.comparisonHornMap hd z z' h) (m.marksHorn_comparisonHornMap hd z z' h hw hz hz')
  refine ⟨_, hZf (m.faces_comparisonMarkedHorn_subset_marking hd), ?_⟩
  have hdim : (cellRound (X.underlying.map (Atom.closureIncl m.atom m.face).op z)).dim =
      grade ℕ m.face :=
    Atom.dimension_ofClosure _ _
  refine ⟨?_, rfl, ?_, ?_⟩
  · rw [hdim]
    change (Atom.ofClosure m.comparisonAtom m.comparisonFace).dimension = _
    rw [Atom.dimension_ofClosure, MarkedHornData.comparisonFace,
      (isMorphism m.comparisonIso.hom).grade_eq,
      PartialCylinder.grade_mkI_none]
  · rw [hdim]
    exact m.equiv_boundary_comparisonFace hd z z' h Z hZ false
  · rw [hdim]
    exact m.equiv_boundary_comparisonFace hd z z' h Z hZ true

end Atoms.Diagrammatic
