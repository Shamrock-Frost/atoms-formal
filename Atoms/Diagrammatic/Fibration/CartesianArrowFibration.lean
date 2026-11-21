import Atoms.Diagrammatic.Fibration.CartesianArrowVertices
import Atoms.Diagrammatic.Localization.PathSpace
import Atoms.Diagrammatic.Joyal.GrayTensorModel

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra
open Atoms.Shape Atoms.Homotopical Atoms.Molecule Atoms.Molecule.OGP

universe u

namespace Atoms.Diagrammatic

private theorem cellularExtension_incl_app_point_surjective {X : DiagSet.{u}}
    (c : CellularExtensionData X) : Function.Surjective (c.incl.app (op atomPoint)) := by
  intro y
  rcases c.cell_cases y with h | hd | ⟨e, f, hf⟩
  · exact h
  · have := dimension_pos_of_isDegenerate hd
    rw [dimension_atomPoint] at this
    omega
  · have he := Atom.dimension_eq_of_iso f
    rw [dimension_atomPoint, c.dimension_shape] at he
    omega

private theorem inversion_stepIncl_app_point_surjective {X : DiagSet.{u}} (A : InversionData X) :
    Function.Surjective (A.stepIncl.app (op atomPoint)) :=
  (cellularExtension_incl_app_point_surjective A.invertorExtension).comp
    (cellularExtension_incl_app_point_surjective A.inverseExtension)

private theorem inversion_toLocalization_app_point_surjective {X : DiagSet.{u}}
    (A : InversionData X) :
    Function.Surjective (A.toLocalization.app (op atomPoint)) := by
  let F : ℕ ⥤ DiagSet.{u} := Functor.ofSequence fun n => (A.stage n).2.stepIncl
  have hs : ∀ (n : ℕ) (y : (A.stage n).1.Vertex),
      ∃ x : X.Vertex, (A.stageι n).app (op atomPoint) y =
        A.toLocalization.app (op atomPoint) x := by
    intro n
    induction n with
    | zero =>
      intro y
      exact ⟨y, rfl⟩
    | succ n ih =>
      intro y
      obtain ⟨z, rfl⟩ := inversion_stepIncl_app_point_surjective (A.stage n).2 y
      obtain ⟨x, hx⟩ := ih z
      exact ⟨x, (ConcreteCategory.congr_hom
        (NatTrans.congr_app (A.stepIncl_stageι n) (op atomPoint)) z).trans hx⟩
  intro y
  have hc := isColimitOfPreserves ((evaluation Atomᵒᵖ (Type u)).obj (op atomPoint))
    (colimit.isColimit F)
  obtain ⟨n, z, hz⟩ := Types.jointly_surjective_of_isColimit hc y
  obtain ⟨x, hx⟩ := hs n z
  exact ⟨x, hx.symm.trans hz⟩

private theorem locSite_map_toSelf_app_point_surjective (U : MarkedSite atomMarking) :
    Function.Surjective
      ((locSite.map (MarkedSite.toSelf U)).app (op atomPoint)) := by
  rcases U with ⟨U, ε, hU⟩
  cases ε with
  | false =>
    intro y
    exact ⟨y, rfl⟩
  | true =>
    exact inversion_toLocalization_app_point_surjective (topInversionData U (hU rfl))

private theorem toLoc_app_point_surjective (X : MarkedDiagSet.{u}) :
    Function.Surjective ((toLoc X).app (op atomPoint)) := by
  let L := uliftYoneda.{u}.leftKanExtension locSite.{u}
  let α := uliftYoneda.{u}.leftKanExtensionUnit locSite.{u}
  let η := (Presheaf.uliftYonedaAdjunction L α).unit.app X.obj
  have hc := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α X.obj
  have hv := isColimitOfPreserves ((evaluation Atomᵒᵖ (Type u)).obj (op atomPoint)) hc
  intro y
  obtain ⟨j, z, hz⟩ := Types.jointly_surjective_of_isColimit hv y
  obtain ⟨v, hv⟩ := locSite_map_toSelf_app_point_surjective j.left z
  let x := uliftYonedaEquiv j.hom
  have hη : (η.app (op j.left) x).down = α.app j.left ≫ L.map j.hom := by
    dsimp only [η]
    rw [Presheaf.uliftYonedaAdjunction_unit_app_app]
    dsimp only [x]
    rw [Equiv.symm_apply_apply]
  have hn := ConcreteCategory.congr_hom
    (η.naturality (MarkedSite.toSelf j.left).op).symm x
  change ULift.up (locSite.map (MarkedSite.toSelf j.left) ≫
      (η.app (op j.left) x).down) =
    η.app (op ((MarkedSite.unmarked atomMarking).obj j.left.obj))
      (X.obj.map (MarkedSite.toSelf j.left).op x) at hn
  have hn' := congrArg (fun t => t.down.app (op atomPoint) v) hn
  refine ⟨X.underlying.map v.down.op
    (X.obj.map (MarkedSite.toSelf j.left).op x), ?_⟩
  have ht := (toLoc X).naturality v.down.op
  have ht' := ConcreteCategory.congr_hom ht
    (X.obj.map (MarkedSite.toSelf j.left).op x)
  let t := (η.app (op ((MarkedSite.unmarked atomMarking).obj j.left.obj))
    (X.obj.map (MarkedSite.toSelf j.left).op x)).down
  have ht'' : (Loc.obj X).map v.down.op (uliftYonedaEquiv t) =
      t.app (op atomPoint) v :=
    (NatTrans.naturality_apply t v.down.op ⟨𝟙 _⟩).symm
  refine ht'.trans (ht''.trans (hn'.symm.trans ?_))
  rw [hη]
  change (α.app j.left ≫ L.map j.hom).app (op atomPoint)
    ((locSite.map (MarkedSite.toSelf j.left)).app (op atomPoint) v) = y
  rw [hv]
  exact hz

private theorem exists_eq_comp_grayContraction_comp_grayEndpoint (U : Atom)
    (f : atomPoint ⟶ grayCylinder.obj U) :
    ∃ ε : Bool, f = f ≫ grayContraction.app U ≫ (grayEndpoint ε).app U := by
  have hg := ((Atoms.Molecule.OGP.isMap_of_isInclusion (cylAtomIso U).inv).grade_le
    (f atomPoint.top)).trans ((Atom.isMap f).grade_le atomPoint.top)
  have hp := atomPoint.grade_le_dimension atomPoint.top
  rw [dimension_atomPoint] at hp
  have hz := hg.trans hp
  rw [Prod.grade_eq_add] at hz
  cases h : ((cylAtomIso U).inv (f atomPoint.top)).1 with
  | pole ε =>
    refine ⟨ε, Atom.hom_ext fun x => ?_⟩
    apply (Atoms.Molecule.OGP.orderIsoOfIso (cylAtomIso U)).symm.injective
    change (cylAtomIso U).inv (f x) =
      (cylAtomIso U).inv ((grayEndpoint ε).app U (grayContraction.app U (f x)))
    rw [symm_grayEndpoint_apply, grayContraction_app_apply]
    have hx : x = atomPoint.top := Subsingleton.elim _ _
    rw [hx]
    exact Prod.ext h rfl
  | susp a =>
    rw [h, Atoms.Molecule.OGP.SuspCarrier.grade_susp] at hz
    omega

private theorem exists_grayCylinderEndpoint_app_eq (X : DiagSet.{u})
    (y : (grayCylinderFunctor.obj X).Vertex) :
    ∃ (ε : Bool) (x : X.Vertex), ((grayCylinderEndpoint ε).app X).app (op atomPoint) x = y := by
  have hc := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    (grayCylinderFunctor.obj X) (grayCylinderUnit X) (op atomPoint)
  obtain ⟨j, z, hz⟩ := Types.jointly_surjective_of_isColimit hc y
  obtain ⟨ε, hε⟩ := exists_eq_comp_grayContraction_comp_grayEndpoint j.left.unop j.hom.unop
  refine ⟨ε, X.map (j.hom.unop ≫ grayContraction.app j.left.unop).op z, ?_⟩
  change (grayCylinderFunctor.obj X).map ((grayEndpoint ε).app atomPoint).op
    ((grayCylinderUnit X).app (op atomPoint)
      (X.map (j.hom.unop ≫ grayContraction.app j.left.unop).op z)) = y
  have hn := NatTrans.naturality_apply (grayCylinderUnit X)
    (j.hom.unop ≫ grayContraction.app j.left.unop).op z
  refine (congrArg ((grayCylinderFunctor.obj X).map
    ((grayEndpoint ε).app atomPoint).op) hn).trans ?_
  have hh : (grayEndpoint ε).app atomPoint ≫
      grayCylinder.map (j.hom.unop ≫ grayContraction.app j.left.unop) = j.hom.unop :=
    ((grayEndpoint ε).naturality
      (j.hom.unop ≫ grayContraction.app j.left.unop)).symm.trans
        ((Category.assoc _ _ _).trans hε.symm)
  have ht := Functor.map_comp_apply (grayCylinderFunctor.obj X)
    (grayCylinder.map (j.hom.unop ≫ grayContraction.app j.left.unop)).op
    ((grayEndpoint ε).app atomPoint).op ((grayCylinderUnit X).app j.left z)
  refine ht.symm.trans ?_
  change (grayCylinderFunctor.obj X).map
    (((grayEndpoint ε).app atomPoint ≫
      grayCylinder.map (j.hom.unop ≫ grayContraction.app j.left.unop)).op)
    ((grayCylinderUnit X).app j.left z) = y
  rw [hh]
  exact hz

private theorem exists_reversibleCylinder_endpoint_app_eq (X : DiagSet.{u})
    (y : (reversibleCylinder.I.obj X).Vertex) :
    ∃ (ε : Bool) (x : X.Vertex),
      ((reversibleCylinder.endpoint ε).app X).app (op atomPoint) x = y := by
  let P := (MarkedPresheaf.flat atomMarking).obj X
  obtain ⟨z, hz⟩ := toLoc_app_point_surjective (markedCylinder.obj P) y
  obtain ⟨ε, x, hx⟩ := exists_grayCylinderEndpoint_app_eq X
    ((markedCylinderForgetIso.hom.app P).app (op atomPoint) z)
  have he := NatTrans.congr_app
    (whiskerRight_endpoint_forget_comp_markedCylinderForgetIso_hom ε) P
  have hx' : (MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app P)).app
      (op atomPoint) x = z := by
    apply (Iso.app (markedCylinderForgetIso.app P) (op atomPoint)).toEquiv.injective
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app he (op atomPoint)) x).trans hx
  refine ⟨ε, x, ?_⟩
  have ht : (reversibleCylinder.endpoint ε).app X =
      MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app P) ≫
        toLoc (markedCylinder.obj P) :=
    toLoc_naturality ((markedExactCylinder.endpoint ε).app P)
  rw [ht]
  change (toLoc (markedCylinder.obj P)).app (op atomPoint)
    ((MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app P)).app
      (op atomPoint) x) = y
  rw [hx']
  exact hz

private theorem isEquivalence_toLoc_app_of_mem_marked (X : MarkedDiagSet.{u}) {U : Atom}
    (hU : 0 < U.dimension) {x : diagram X.underlying U} (hx : x ∈ X.marked U) :
    IsEquivalence (Loc.obj X) ((toLoc X).app (op U) x) := by
  have h := ((topInversionData U hU).isEquivalence_toLocalization ⟨⟩).map (locCell X hU hx)
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toWalkingEquivalence_locCell X hU hx) (op U)) ⟨𝟙 U⟩
  have he' : (locCell X hU hx).app (op U)
      ((topInversionData U hU).toLocalization.app (op U) ⟨𝟙 U⟩) =
        (toLoc X).app (op U) x :=
    he.trans (congrArg ((toLoc X).app (op U)) (uliftYonedaEquiv.apply_symm_apply x))
  exact he' ▸ h

private noncomputable def intervalToPointCylinder :
    markedInterval.{u} ≅ markedCylinder.obj markedTensorUnit.{u} :=
  (markedTensorRightUnitor false markedInterval).symm ≪≫
    ((markedCylinderIsoTensorLeft false).app markedTensorUnit).symm

private theorem intervalToPointCylinder_endpoint (ε : Bool) :
    markedIntervalVertex.{u} ε ≫ intervalToPointCylinder.hom =
      (markedExactCylinder.endpoint ε).app markedTensorUnit := by
  have h : (markedTensorRightUnitor false markedTensorUnit.{u}).hom =
      (markedTensorLeftUnitor false markedTensorUnit).hom :=
    isTerminalMarkedTensorUnit.hom_ext _ _
  have ht : (markedTensorLeftUnitor false markedTensorUnit.{u}).inv ≫
      markedTensorMap false (markedIntervalVertex ε) (𝟙 markedTensorUnit) =
        markedIntervalVertex ε ≫ (markedTensorRightUnitor false markedInterval).inv := by
    apply (cancel_mono (markedTensorRightUnitor false markedInterval).hom).1
    rw [Category.assoc, markedTensorRightUnitor_naturality, h,
      Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hk : intervalToPointCylinder.{u}.hom ≫
      ((markedCylinderIsoTensorLeft false).app markedTensorUnit).hom =
        (markedTensorRightUnitor false markedInterval).inv :=
    (Category.assoc _ _ _).trans
      ((congrArg ((markedTensorRightUnitor false markedInterval).inv ≫ ·)
        ((markedCylinderIsoTensorLeft false).app markedTensorUnit).inv_hom_id).trans
          (Category.comp_id _))
  apply (cancel_mono ((markedCylinderIsoTensorLeft false).hom.app markedTensorUnit)).1
  exact (Category.assoc _ _ _).trans ((congrArg (markedIntervalVertex ε ≫ ·) hk).trans
    (ht.symm.trans (markedExactCylinder_endpoint_app_comp_markedCylinderIsoTensorLeft_hom_app
      false ε markedTensorUnit).symm))

private theorem exists_isEquivalence_reversibleCylinder_point :
    ∃ e : diagram (reversibleCylinder.{u}.I.obj (ball atomPoint)) (atomGlobe 1),
      IsEquivalence _ e ∧ ∀ ε : Bool,
        (reversibleCylinder.I.obj (ball atomPoint)).map (atomGlobeVertex ε).op e =
          ((reversibleCylinder.endpoint ε).app (ball atomPoint)).app (op atomPoint) ⟨𝟙 _⟩ := by
  let f := intervalBallIso.{u}.hom ≫
    MarkedPresheaf.forget.map intervalToPointCylinder.hom ≫
      toLoc (markedCylinder.obj markedTensorUnit)
  refine ⟨uliftYonedaEquiv f, ?_, ?_⟩
  · exact isEquivalence_toLoc_app_of_mem_marked _ markable_atomGlobe_one
      (MarkedPresheaf.map_mem_marked intervalToPointCylinder.hom
        intervalBallIso_top_mem_marked)
  · intro ε
    have h := congrArg (fun k => MarkedPresheaf.forget.map k)
      (intervalToPointCylinder_endpoint.{u} ε)
    have he := congrArg (fun k => k ≫ toLoc (markedCylinder.obj markedTensorUnit)) h
    rw [Functor.map_comp, forget_map_markedIntervalVertex] at he
    have ht : (MarkedPresheaf.forget.map
        ((markedExactCylinder.endpoint ε).app markedTensorUnit.{u})) ≫
          toLoc (markedCylinder.obj markedTensorUnit) =
            (reversibleCylinder.endpoint ε).app (ball atomPoint) :=
      (toLoc_naturality ((markedExactCylinder.endpoint ε).app markedTensorUnit)).symm
    have hm : uliftYoneda.map (atomGlobeVertex ε) ≫ f =
        (reversibleCylinder.endpoint ε).app (ball atomPoint) :=
      (Category.assoc _ _ _).symm.trans
        ((Category.assoc _ _ _).symm.trans (he.trans ht))
    have hn := NatTrans.naturality_apply f (atomGlobeVertex ε).op ⟨𝟙 (atomGlobe 1)⟩
    change (Loc.obj (markedCylinder.obj markedTensorUnit)).map (atomGlobeVertex ε).op
      (f.app (op (atomGlobe 1)) ⟨𝟙 (atomGlobe 1)⟩) = _
    calc
      _ = f.app (op atomPoint) ⟨atomGlobeVertex ε⟩ := hn.symm
      _ = _ := ConcreteCategory.congr_hom (NatTrans.congr_app hm (op atomPoint))
        ⟨𝟙 atomPoint⟩

attribute [local irreducible] reversibleCylinder

private theorem bothBox_app_point_surjective {A B : DiagSet.{u}} (j : A ⟶ B) :
    Function.Surjective ((reversibleCylinder.bothBox j).app (op atomPoint)) := by
  intro y
  obtain ⟨ε, x, hx⟩ := exists_reversibleCylinder_endpoint_app_eq B y
  let t : B ⨿ B ⟶ reversibleCylinder.{u}.bothBoxSource j := pushout.inr _ _
  have ht : t ≫ reversibleCylinder.bothBox j = reversibleCylinder.endpoints B :=
    reversibleCylinder.inr_bothBox j
  have hε : ∃ k : B ⟶ B ⨿ B,
      k ≫ reversibleCylinder.endpoints B = (reversibleCylinder.endpoint ε).app B := by
    cases ε with
    | false => exact ⟨coprod.inl, coprod.inl_desc _ _⟩
    | true => exact ⟨coprod.inr, coprod.inr_desc _ _⟩
  obtain ⟨k, hk⟩ := hε
  have h : (k ≫ t) ≫ reversibleCylinder.bothBox j =
      (reversibleCylinder.endpoint ε).app B :=
    (Category.assoc _ _ _).trans ((congrArg (k ≫ ·) ht).trans hk)
  exact ⟨(k ≫ t).app (op atomPoint) x,
    (ConcreteCategory.congr_hom (NatTrans.congr_app h (op atomPoint)) x).trans hx⟩

private theorem toMergerInclusion_app_point_surjective (U : RoundShape) (hU : 0 < U.dimension) :
    Function.Surjective ((toMergerInclusion.{u} U hU).app (op atomPoint)) := by
  intro y
  let m := compositorMarkedHorn U hU
  let v : atomPoint ⟶ toMergerAtom U hU := y.down
  have hg : ∀ t : atomPoint.ogp, v t ∈ m.hornSet := by
    intro t
    have hz := (Atom.isMap v).grade_le t
    have hp := atomPoint.grade_le_dimension t
    rw [dimension_atomPoint] at hp
    have hzero : grade ℕ (v t) = 0 := Nat.eq_zero_of_le_zero (hz.trans hp)
    have hd : m.atom.dimension = U.dimension + 1 := dimension_toMergerAtom U hU
    have hf := m.dim_face_add_one
    apply m.mem_hornSet_iff.2
    constructor
    · apply (m.atom.mem_bdryFull_top_iff _).2
      intro ht
      have htop := m.atom.dimension_eq
      have hz : grade ℕ m.atom.top = 0 := ht ▸ hzero
      omega
    · intro ht
      have hz : grade ℕ m.face = 0 := ht ▸ hzero
      omega
  let g := ((realizeAtomIso (toMergerAtom U hU)).inv.app (op atomPoint) y).down
  let r := restrictLift (atomToRDCpx.obj (toMergerAtom U hU)) m.hornSet g hg
  refine ⟨⟨r ≫ (RDCpx.isoOfIso (compositorHornIso U hU).symm).hom⟩, ?_⟩
  apply ULift.ext
  apply Atom.hom_ext
  intro t
  exact congrArg Subtype.val (ConcreteCategory.congr_hom
    (compositorHornIso U hU).inv_hom_id ⟨v t, hg t⟩)

private theorem app_endpoint_false_iff_app_endpoint_true {X B : DiagSet.{u}} (P : X.Vertex → Prop)
    (hP : ∀ {x y : X.Vertex} (e : X.Edge x y),
      IsEquivalence X e.cell → (P x ↔ P y))
    (b : reversibleCylinder.I.obj B ⟶ X) (x : B.Vertex) :
    P (b.app _ (((reversibleCylinder.endpoint false).app B).app _ x)) ↔
      P (b.app _ (((reversibleCylinder.endpoint true).app B).app _ x)) := by
  obtain ⟨e, he, hend⟩ := exists_isEquivalence_reversibleCylinder_point.{u}
  let f := reversibleCylinder.I.map (uliftYonedaEquiv.symm x) ≫ b
  have he' := he.map f
  have hε : ∀ ε : Bool, X.map (atomGlobeVertex ε).op (f.app _ e) =
      b.app _ (((reversibleCylinder.endpoint ε).app B).app _ x) := by
    intro ε
    rw [← NatTrans.naturality_apply, hend]
    have hn := ConcreteCategory.congr_hom (NatTrans.congr_app
      ((reversibleCylinder.endpoint ε).naturality (uliftYonedaEquiv.symm x))
        (op atomPoint)) ⟨𝟙 atomPoint⟩
    change b.app _ ((reversibleCylinder.I.map (uliftYonedaEquiv.symm x)).app _
      (((reversibleCylinder.endpoint ε).app (ball atomPoint)).app _ ⟨𝟙 atomPoint⟩)) = _
    exact (congrArg (b.app (op atomPoint)) hn.symm).trans
      (congrArg (fun z => b.app _ (((reversibleCylinder.endpoint ε).app B).app _ z))
        (uliftYonedaEquiv.apply_symm_apply x))
  exact (hε false) ▸ (hε true) ▸ hP (DiagSet.Edge.ofCell (f.app _ e)) he'

private theorem hasLiftingProperty_endpointBox_fullSubpresheaf_ι {X A B : DiagSet.{u}}
    (P : X.Vertex → Prop)
    (hP : ∀ {x y : X.Vertex} (e : X.Edge x y),
      IsEquivalence X e.cell → (P x ↔ P y)) (ε : Bool) (j : A ⟶ B) :
    HasLiftingProperty (reversibleCylinder.endpointBox ε j) (X.fullSubpresheaf P).ι := by
  apply DiagSet.hasLiftingProperty_fullSubpresheaf_ι
  intro b hb y
  obtain ⟨δ, x, rfl⟩ := exists_reversibleCylinder_endpoint_app_eq B y
  let t : B ⟶ reversibleCylinder.{u}.endpointBoxSource ε j := pushout.inr _ _
  have ht : t ≫ reversibleCylinder.endpointBox ε j =
      (reversibleCylinder.endpoint ε).app B := reversibleCylinder.inr_endpointBox ε j
  have hx := hb (t.app _ x)
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app ht (op atomPoint)) x
  change P (b.app _ ((reversibleCylinder.endpointBox ε j).app _ (t.app _ x))) at hx
  change (reversibleCylinder.endpointBox ε j).app _ (t.app _ x) =
    ((reversibleCylinder.endpoint ε).app B).app _ x at he
  rw [he] at hx
  have hi := app_endpoint_false_iff_app_endpoint_true P hP b x
  cases ε <;> cases δ
  · exact hx
  · exact hi.mp hx
  · exact hi.mpr hx
  · exact hx

theorem DiagSet.fibration_fullSubpresheaf_ι {X : DiagSet.{u}}
    [IsFibrant ((DiagSet.toInfty 1).obj X)] (P : X.Vertex → Prop)
    (hP : ∀ {x y : X.Vertex} (e : X.Edge x y),
      IsEquivalence X e.cell → (P x ↔ P y)) :
    Fibration ((DiagSet.toInfty 1).map (X.fullSubpresheaf P).ι) := by
  let T := (ofHoms fun _ : Unit => (X.fullSubpresheaf P).ι).llp
  have hT {A B : DiagSet.{u}} (j : A ⟶ B)
      (h : HasLiftingProperty j (X.fullSubpresheaf P).ι) : T j :=
    (llp_ofHoms_iff_hasLiftingProperty Unit j _).2 h
  have hg : inftyGenerators.{u} 1 ≤ T := by
    refine sup_le ((ofHoms_le_iff _ _).2 fun U => ?_)
      ((ofHoms_le_iff _ _).2 fun U => ?_)
    · exact hT _ (DiagSet.hasLiftingProperty_fullSubpresheaf_ι_of_surjective P _
        ((inversion_toLocalization_app_point_surjective (topInversionData _ _)).comp
          (toMergerInclusion_app_point_surjective U.1 U.2)))
    · exact hT _ (DiagSet.hasLiftingProperty_fullSubpresheaf_ι_of_surjective P _
        (inversion_toLocalization_app_point_surjective (topInversionData _ _)))
  have hs : ∀ n, reversibleCylinder.{u}.anodyneGeneratorsStage (inftyGenerators 1) n ≤ T := by
    intro n
    cases n with
    | zero =>
      refine sup_le hg (iSup_le fun ε => arrowImage_le _ fun A B j hj => ?_)
      exact hT _ (hasLiftingProperty_endpointBox_fullSubpresheaf_ι P hP ε j)
    | succ n =>
      exact arrowImage_le _ fun A B j hj =>
        hT _ (DiagSet.hasLiftingProperty_fullSubpresheaf_ι_of_surjective P _
          (bothBox_app_point_surjective j))
  have hn : reversibleCylinder.{u}.naiveFibrations (inftyGenerators 1)
      (X.fullSubpresheaf P).ι := by
    rw [reversibleCylinder.{u}.naiveFibrations_eq_rlp_anodyneGenerators _
      (inftyGenerators_le_monomorphisms 1)]
    intro A B j hj
    exact (iSup_le hs j hj) _ ⟨()⟩
  have hf : reversibleCylinder.{u}.IsFibrant (inftyGenerators 1) X :=
    (ExactCylinder.modelCategory.isFibrant_iff reversibleCylinder.{u} (inftyGenerators.{u} 1)
      (inftyGenerators_le_monomorphisms 1) X).1
      ((isFibrant_infty_iff 1 X).2 (isInftyCategory_of_isFibrant 1
        ((DiagSet.toInfty 1).obj X) inferInstance))
  exact ⟨reversibleCylinder.{u}.rlp_trivialCofibrations_of_rlp_anodyne _
    (inftyGenerators_le_monomorphisms 1) _ hn hf⟩

theorem DiagSet.isFibrant_cartesianArrowTarget {E S : DiagSet.{u}} (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    IsFibrant ((DiagSet.toInfty 1).obj (Functor.PullbackObjObj.ofHasPullback
      grayHomRightBifunctor.{u}
      ((MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex true)) p).pt) := by
  let i := (MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex.{u} true)
  let q := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u} i p
  have : Mono i := isTerminalBallAtomPoint.mono_from i
  have hS : IsInftyCategory 1 S :=
    isInftyCategory_of_isFibrant 1 ((DiagSet.toInfty 1).obj S) inferInstance
  have hE : IsInftyCategory 1 E := isInftyCategory_of_isFibrant 1
    ((DiagSet.toInfty 1).obj E) (isFibrant_of_fibration ((DiagSet.toInfty 1).map p))
  have : IsFibrant ((DiagSet.toInfty 1).obj ((grayHomRightBifunctor.obj
      (op (MarkedPresheaf.forget.obj markedTensorUnit.{u}))).obj E)) :=
    (isFibrant_infty_iff 1 _).2 (isInftyCategory_grayHomRight _ hE)
  have hr := fibration_toInfty_one_grayHomRestrict i hS
  have : Fibration ((DiagSet.toInfty 1).map q.fst) :=
    (fibration_iff _).2 ((fibrations (DiagSet.Infty.{u} 1)).of_isPullback q.isPullback.flip
      ((fibration_iff _).1 hr))
  exact isFibrant_of_fibration ((DiagSet.toInfty 1).map q.fst)

theorem DiagSet.fibration_cartesianArrows {E S : DiagSet.{u}} (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    Fibration ((DiagSet.toInfty 1).map
      ((DiagSet.fullSubpresheaf ((grayHomRight markedInterval.{u}.underlying).obj E)
        (fun z => DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell
          (DiagSet.grayArrowVertexEquiv E z)))).ι ≫
        (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u}
          ((MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex true)) p).π)) := by
  let i := (MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex.{u} true)
  have : Mono i := isTerminalBallAtomPoint.mono_from i
  have hE : IsInftyCategory 1 E := isInftyCategory_of_isFibrant 1
    ((DiagSet.toInfty 1).obj E) (isFibrant_of_fibration ((DiagSet.toInfty 1).map p))
  have : IsFibrant ((DiagSet.toInfty 1).obj
      ((grayHomRight markedInterval.{u}.underlying).obj E)) :=
    (isFibrant_infty_iff 1 _).2 (isInftyCategory_grayHomRight _ hE)
  have := DiagSet.fibration_fullSubpresheaf_ι
    (fun z => DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell
      (DiagSet.grayArrowVertexEquiv E z)))
    (fun e he => DiagSet.isCartesianEdge_grayArrowVertex_iff_of_isEquivalence p e he)
  have := fibration_toInfty_one_grayHomRight_pullbackObjObj i p
  exact (fibration_iff _).2 ((fibrations (DiagSet.Infty.{u} 1)).comp_mem _ _
    ((fibration_iff _).1 ‹_›) ((fibration_iff _).1 this))

end Atoms.Diagrammatic
