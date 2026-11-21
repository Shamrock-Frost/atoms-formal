import Atoms.Diagrammatic.Marked.HornLike
import Atoms.Diagrammatic.Marked.InvertorTransport
import Atoms.Diagrammatic.Marked.NaturalMarking
import Atoms.Homotopical.Marked.Cellular

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra
open Atoms.Homotopical Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

theorem mem_equivalences_of_evalFrames {X : DiagSet.{u}} {fs : ContextFrames X}
    {v w b : RoundPastingDiagram X} (hE : FrameEquivalences fs)
    (h : RoundContextEquation fs v w b) {a c : RoundPastingDiagram X}
    (ha : HasRoundType a.toPastingDiagram v w)
    (hev : EvalFrames fs 0 a.toPastingDiagram c.toPastingDiagram) (hc : c ∈ equivalences X) :
    a ∈ equivalences X := by
  obtain ⟨ℓ, r, rest, rfl, hdv, hfo, hr, hb⟩ := h.spec
  obtain ⟨E', hW, hP⟩ := exists_isWeakInvCtx_ofFramesRev ℓ r rest (H' := hb.roundHom) hdv rfl hfo
    hr (frameEqvRev_of_frameEquivalences _ hE)
  have haIn : IsRoundIn (RoundHom.ofParallel h.1) a.toPastingDiagram :=
    ⟨InHom.of_hasRoundType ha h.1, ha.dim_eq, a.isRound⟩
  have hev' := evalFrames_ofFramesRev ℓ r rest hdv hfo _ haIn.inHom
  have heq := EvalFrames.unique hev hev' (.refl _)
  have hEa := hW.round.isRoundIn haIn
  exact (mem_equivalences_iff_of_equivalent (hW.left.equivalent_app haIn _ a.isRound)).1
    (hP _ hEa (mem_equivalences_of_equiv heq hc) (hW.round'.isRoundIn hEa).isRound)

theorem sphereBoundary_eq_boundary_ofCell {Y : DiagSet.{u}} {A : Atom} (hA : 0 < A.dimension)
    (z : diagram Y A) (α : Bool) :
    sphereBoundary A hA (realize.map (A.toMoleculeShape.rdc.restrictIncl (A.ogp.bdryFull ⊤)) ≫
      (ofCell z).map) α = (ofCell z).boundary (A.dimension - 1) α :=
  (restrictAlong_restrictIncl _ _ _ _).trans
    (congrArg (PastingDiagram.mk _) (boundary_comm (ofCell z) _ α))

theorem isEquivalence_face_of_isEquivalence (m : MarkedHornData) (hk : 2 ≤ m.atom.dimension)
    {Y : DiagSet.{u}} (z : diagram Y m.atom) (hz : IsEquivalence Y z)
    (hw : m.MarksHorn (MarkedDiagSet.natural.obj Y) (realize.map m.hornIncl ≫ (ofCell z).map))
    (hsub : m.atom.ogp.faces (!m.side) m.atom.top ⊆ m.marking) :
    IsEquivalence Y (Y.map (Atom.closureIncl m.atom m.face).op z) := by
  classical
  have hdA := m.dimension_faceAtom_add_one
  have hA : 0 < m.faceAtom.dimension := by omega
  have hΛ := m.hornSet_subset_bdryFull
  have hsS : m.atom.ogp.bdry ⊤ m.side ≤ m.atom.ogp.bdryFull ⊤ := bdry_le_bdryFull _ _
  let σ := realize.map (m.atom.toMoleculeShape.rdc.restrictIncl (m.atom.ogp.bdryFull ⊤)) ≫
    (ofCell z).map
  have hσ₁ : realize.map (RDCpx.inclusion m.atom.toMoleculeShape.rdc hΛ) ≫ σ =
      realize.map m.hornIncl ≫ (ofCell z).map :=
    (realize.map_comp_assoc _ _ _).symm.trans (congrArg (fun t => realize.map t ≫ (ofCell z).map)
      (RDCpx.inclusion_restrictIncl _ hΛ))
  have hev := m.evalFrames_restrictIn σ hΛ hsS
  rw [← m.frames_inclusion hΛ σ le_rfl, hσ₁] at hev
  have hcl : (restrictIn σ (P := m.atom.toMoleculeShape) (m.atom.isRDC m.face)
      (m.closure_face_subset_bdry.trans hsS)).Equiv
        (ofCell (Y.map (Atom.closureIncl m.atom m.face).op z)) := by
    refine (equiv_restrictAlong_of_image_eq σ _ m.faceEmb _
      (m.image_faceEmb.le.trans (m.closure_face_subset_bdry.trans hsS)) ?_).trans ?_
    · exact (m.atom.toMoleculeShape.map_subIncl_top _).trans m.image_faceEmb.symm
    · have hfs : RDCpx.ofInclusion (P := m.faceAtom.toMoleculeShape.rdc)
          (Q := m.atom.toMoleculeShape.rdc.restrict (m.atom.ogp.bdryFull ⊤)) m.faceToSphere ≫
            m.atom.toMoleculeShape.rdc.restrictIncl (m.atom.ogp.bdryFull ⊤) =
          atomToRDCpx.map (Atom.closureIncl m.atom m.face) := by ext; rfl
      have h3 : realize.map (RDCpx.ofInclusion (P := m.faceAtom.toMoleculeShape.rdc)
          (Q := m.atom.toMoleculeShape.rdc.restrict (m.atom.ogp.bdryFull ⊤)) m.faceToSphere) ≫ σ =
            (ofCell (Y.map (Atom.closureIncl m.atom m.face).op z)).map :=
        (realize.map_comp_assoc _ _ _).symm.trans ((congrArg (fun t => realize.map t ≫ _) hfs).trans
          (ofCell_map_op_map (Atom.closureIncl m.atom m.face) z).symm)
      have h2 : restrictAlong σ m.faceAtom.toMoleculeShape m.faceEmb
          (m.image_faceEmb.le.trans (m.closure_face_subset_bdry.trans hsS)) =
            ofCell (Y.map (Atom.closureIncl m.atom m.face).op z) :=
        congrArg (PastingDiagram.mk m.faceAtom.toMoleculeShape) h3
      rw [h2]
  have hev' := EvalFrames.of_equiv hev hcl (.refl _)
  have hround : ∀ α, (restrictIn σ (P := m.atom.toMoleculeShape) (m.isMoleculeIn_bdry α)
      (bdry_le_bdryFull _ α)).IsRound :=
    fun α => (m.atom.toMoleculeShape.isRound_sub_iff (m.isMoleculeIn_bdry α)).2 (m.round_bdry α)
  have hsph : ∀ α, ((ofCell z).boundary (m.atom.dimension - 1) α).Equiv
      (restrictIn σ (P := m.atom.toMoleculeShape) (m.isMoleculeIn_bdry α)
        (bdry_le_bdryFull _ α)) :=
    fun α => (sphereBoundary_eq_boundary_ofCell m.positive z α) ▸
      equiv_restrictAlong_of_image_eq _ _ _ _ _
      ((m.atom.toMoleculeShape.map_boundaryIncl_eq_bdry (by omega : m.atom.dimension = _) α).trans
        (m.atom.toMoleculeShape.map_subIncl_top (m.isMoleculeIn_bdry α)).symm)
  have hopp : restrictIn σ (P := m.atom.toMoleculeShape) (m.isMoleculeIn_bdry (!m.side))
      (bdry_le_bdryFull _ _) =
        (m.oppBoundary (realize.map m.hornIncl ≫ (ofCell z).map)).toPastingDiagram := by
    rw [← hσ₁]
    exact (restrictAlong_inclusion hΛ σ _ _ ((MoleculeShape.map_subIncl_top _ _).le.trans
      m.bdry_not_subset_hornSet)).symm
  have hb := m.oppBoundary_mem_equivalences _ hw hsub
  have hdc : ∀ α, (restrictIn σ (P := m.atom.toMoleculeShape) (m.isMoleculeIn_bdry α)
      (bdry_le_bdryFull _ α)).dim = m.atom.dimension - 1 := fun α => by
    have h := m.atom.toMoleculeShape.dimension_sub (m.isMoleculeIn_bdry α)
    rw [m.atom.isMolecule.krullDim_bdry (n := m.atom.dimension - 1) (by
      rw [LowerSet.krullDim_top, m.atom.krullDim_eq_dimension, Nat.sub_add_cancel m.positive])]
      at h
    exact_mod_cast h
  have hzd : (cellRound z).dim = m.atom.dimension - 1 + 1 := by
    change m.atom.dimension = _; omega
  have hc := (mem_equivalences_iff_of_equivalent
    (equivalent_of_mem_equivalences_cond m.side (u := ⟨_, hround m.side⟩)
      (v := m.oppBoundary _) hz (hdc m.side)
      ((congrArg PastingDiagram.dim hopp).symm.trans (hdc _)) hzd (hsph m.side)
      (hopp ▸ hsph (!m.side)))).2 hb
  have hfi : m.faceAtom.toMoleculeShape.rdc.restrictIncl (m.faceAtom.ogp.bdryFull ⊤) ≫
      atomToRDCpx.map (Atom.closureIncl m.atom m.face) =
      RDCpx.ofInclusion (P := m.faceAtom.toMoleculeShape.rdc.restrict (m.faceAtom.ogp.bdryFull ⊤))
        (Q := m.hornRDC) m.faceSphere ≫ m.hornIncl := by ext; rfl
  have he : realize.map (m.faceAtom.toMoleculeShape.rdc.restrictIncl (m.faceAtom.ogp.bdryFull ⊤)) ≫
      (ofCell (Y.map (Atom.closureIncl m.atom m.face).op z)).map =
        realize.map (RDCpx.ofInclusion
          (P := m.faceAtom.toMoleculeShape.rdc.restrict (m.faceAtom.ogp.bdryFull ⊤))
          (Q := m.hornRDC) m.faceSphere) ≫ realize.map m.hornIncl ≫ (ofCell z).map := by
    rw [ofCell_map_op_map, ← realize.map_comp_assoc, hfi, realize.map_comp_assoc]
  have hτ : HasRoundType (ofCell (Y.map (Atom.closureIncl m.atom m.face).op z))
      (m.faceBoundary hk (realize.map m.hornIncl ≫ (ofCell z).map) false)
      (m.faceBoundary hk (realize.map m.hornIncl ≫ (ofCell z).map) true) := by
    refine HasRoundType.of_equiv_boundary (m.dim_faceBoundary hk _ false)
      (m.dim_faceBoundary hk _ true) ?_ ?_
    · change m.faceAtom.dimension = _; omega
    · intro β
      have e1 := sphereBoundary_eq_boundary_ofCell hA
        (Y.map (Atom.closureIncl m.atom m.face).op z) β
      rw [he] at e1
      rw [show m.atom.dimension - 2 = m.faceAtom.dimension - 1 by omega]
      cases β <;> exact e1 ▸ m.sphereBoundary_faceSphere hk _ hA _
  exact mem_equivalences_of_evalFrames (m.frameEquivalences_of_marksHorn _ hw)
    (m.roundContextEquation hk _) (a := cellRound (Y.map (Atom.closureIncl m.atom m.face).op z))
    (c := ⟨_, hround m.side⟩) hτ hev' hc

theorem range_epi_comp {A B C : DiagSet.{u}} (p : A ⟶ B) [Epi p] (f : B ⟶ C) :
    Subfunctor.range (p ≫ f) = Subfunctor.range f := by
  rw [Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top]

theorem range_forget_map_pushout_desc_comp {A B C D : MarkedDiagSet.{u}} {Z : DiagSet.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (a : B ⟶ D) (b : C ⟶ D) (w : f ≫ a = g ≫ b)
    (h : MarkedPresheaf.forget.obj D ⟶ Z) :
    Subfunctor.range (MarkedPresheaf.forget.map (pushout.desc a b w) ≫ h) =
      Subfunctor.range (MarkedPresheaf.forget.map a ≫ h) ⊔
        Subfunctor.range (MarkedPresheaf.forget.map b ≫ h) := by
  rw [← range_epi_comp (pushoutComparison MarkedPresheaf.forget f g), ← Category.assoc,
    pushoutComparison_map_desc]
  exact Subfunctor.range_pushout_desc_comp _ _ _ _ _ h

theorem range_forget_map_coprod_desc_comp {B C D : MarkedDiagSet.{u}} {Z : DiagSet.{u}}
    (a : B ⟶ D) (b : C ⟶ D) (h : MarkedPresheaf.forget.obj D ⟶ Z) :
    Subfunctor.range (MarkedPresheaf.forget.map (coprod.desc a b) ≫ h) =
      Subfunctor.range (MarkedPresheaf.forget.map a ≫ h) ⊔
        Subfunctor.range (MarkedPresheaf.forget.map b ≫ h) := by
  rw [← range_epi_comp (coprodComparison MarkedPresheaf.forget B C), ← Category.assoc,
    coprodComparison, coprod.desc_comp, ← Functor.map_comp, ← Functor.map_comp,
    coprod.inl_desc, coprod.inr_desc]
  exact Subfunctor.range_coprod_desc_comp _ _ h

variable {U : Atom} {M : Set U.ogp} {hM : ∀ z ∈ M, 0 < grade ℕ z}

theorem range_forget_map_markedCylinder_map_comp {K : MarkedDiagSet.{u}}
    (i : K ⟶ markedBall U M hM) :
    Subfunctor.range (MarkedPresheaf.forget.map (markedCylinder.map i) ≫
      (markedCylinderBallForgetIso U M hM).hom) =
      Subfunctor.range (grayCylinderFunctor.map (MarkedPresheaf.forget.map i) ≫
        (grayCylinderFunctorYonedaIso.app U).hom) := by
  have e : MarkedPresheaf.forget.map (markedCylinder.map i) ≫
      (markedCylinderBallForgetIso U M hM).hom = markedCylinderForgetIso.hom.app K ≫
        grayCylinderFunctor.map (MarkedPresheaf.forget.map i) ≫
          (grayCylinderFunctorYonedaIso.app U).hom :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (grayCylinderFunctorYonedaIso.app U).hom)
      (markedCylinderForgetIso.hom.naturality i)).trans (Category.assoc _ _ _))
  exact (congrArg Subfunctor.range e).trans (range_epi_comp _ _)

theorem range_forget_map_endpoint_comp (ε : Bool) :
    Subfunctor.range (MarkedPresheaf.forget.map
      ((markedExactCylinder.{u}.endpoint ε).app (markedBall U M hM)) ≫
        (markedCylinderBallForgetIso U M hM).hom) =
      closedSubpresheaf (grayCylinder.obj U) (endpointSubset ε U) := by
  have e : MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app (markedBall U M hM)) ≫
      (markedCylinderBallForgetIso U M hM).hom = (grayCylinderEndpoint ε).app (ball U) ≫
        (grayCylinderFunctorYonedaIso.app U).hom :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (grayCylinderFunctorYonedaIso.app U).hom)
      (NatTrans.congr_app (whiskerRight_endpoint_forget_comp_markedCylinderForgetIso_hom ε)
        (markedBall U M hM)))
  exact (congrArg Subfunctor.range e).trans (range_grayCylinderEndpoint_app_ball ε U)

theorem range_forget_map_endpointBox_comp (ε : Bool) {K : MarkedDiagSet.{u}}
    (i : K ⟶ markedBall U M hM) :
    Subfunctor.range (MarkedPresheaf.forget.map (markedExactCylinder.endpointBox ε i) ≫
      (markedCylinderBallForgetIso U M hM).hom) =
      Subfunctor.range (grayCylinderFunctor.map (MarkedPresheaf.forget.map i) ≫
        (grayCylinderFunctorYonedaIso.app U).hom) ⊔
      closedSubpresheaf (grayCylinder.obj U) (endpointSubset ε U) :=
  (range_forget_map_pushout_desc_comp _ _ _ _ _ _).trans (congrArg₂ (· ⊔ ·)
    (range_forget_map_markedCylinder_map_comp i) (range_forget_map_endpoint_comp ε))

theorem range_forget_map_bothBox_comp {K : MarkedDiagSet.{u}} (i : K ⟶ markedBall U M hM) :
    Subfunctor.range (MarkedPresheaf.forget.map (markedExactCylinder.bothBox i) ≫
      (markedCylinderBallForgetIso U M hM).hom) =
      Subfunctor.range (grayCylinderFunctor.map (MarkedPresheaf.forget.map i) ≫
        (grayCylinderFunctorYonedaIso.app U).hom) ⊔
      (closedSubpresheaf (grayCylinder.obj U) (endpointSubset false U) ⊔
        closedSubpresheaf (grayCylinder.obj U) (endpointSubset true U)) := by
  refine (range_forget_map_pushout_desc_comp _ _ _ _ _ _).trans (congrArg₂ (· ⊔ ·)
    (range_forget_map_markedCylinder_map_comp i) ?_)
  exact (range_forget_map_coprod_desc_comp _ _ _).trans (congrArg₂ (· ⊔ ·)
    (range_forget_map_endpoint_comp false) (range_forget_map_endpoint_comp true))

theorem exists_mem_marked_markedCylinder_eq {K : MarkedDiagSet.{u}} (i : K ⟶ markedBall U M hM)
    {V : Atom} (c : V ⟶ grayCylinder.obj U)
    (h : ((cylAtomIso U).inv (c V.top)).1 = ⊤)
    (k : K.underlying.obj (op (Atom.ofClosure U ((cylAtomIso U).inv (c V.top)).2)))
    (hk : (MarkedPresheaf.forget.map i).app _ k = ULift.up (Atom.closureIncl U _)) :
    ∃ p ∈ (markedCylinder.obj K).marked V, (markedCylinderBallForgetIso U M hM).hom.app (op V)
      ((MarkedPresheaf.forget.map (markedCylinder.map i)).app (op V) p) = ULift.up c := by
  obtain ⟨q, hq, hqc⟩ := exists_isCollapseHom_comp_grayCylinder_map_closureIncl c h
  refine ⟨(markedCylinder.obj K).underlying.map q.op (markedCylinderUnitCell K k), ?_, ?_⟩
  · by_cases hi : IsIso q
    · exact ((markedCylinder.obj K).transport (asIso q) _).1 (mem_marked_markedCylinderUnitCell K k)
    · exact (markedCylinder.obj K).degenerate q ⟨hq, hi⟩ _
  · refine Eq.trans ?_ ((markedCylinderBallForgetIso_map_unitCell (M := M) (hM := hM) q _).trans
      (congrArg ULift.up hqc))
    refine congrArg ((markedCylinderBallForgetIso U M hM).hom.app (op V))
      ((NatTrans.naturality_apply (MarkedPresheaf.forget.map (markedCylinder.map i)) q.op _).trans
        (congrArg ((markedCylinder.obj (markedBall U M hM)).underlying.map q.op) ?_))
    exact (forget_map_markedCylinder_map_unitCell i k).trans (congrArg _ hk)

theorem endpoint_contraction_eq (ε : Bool) {V : Atom} (c : V ⟶ grayCylinder.obj U)
    (h : ((cylAtomIso U).inv (c V.top)).1 = SuspCarrier.pole ε) :
    (markedCylinderBallForgetIso.{u} U M hM).hom.app (op V)
      ((MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app (markedBall U M hM))).app
        (op V) ⟨c ≫ grayContraction.app U⟩) = ⟨c⟩ :=
  (markedCylinderBallForgetIso_endpoint ε _).trans
    (congrArg ULift.up (eq_comp_grayContraction_comp_grayEndpoint c ε h).symm)

theorem mem_marked_markedCylinder_markedBall_iff_of {V : Atom}
    (T : Set (grayCylinder.obj U).ogp)
    (hT : ∀ z, z ∈ T ↔ z ∈ cylinderBallMarking U M)
    (q : (markedCylinder.{u}.obj (markedBall U M hM)).underlying.obj (op V)) :
    q ∈ (markedCylinder.obj (markedBall U M hM)).marked V ↔
      IsDegenerate (ball (grayCylinder.obj U))
        ((markedCylinderBallForgetIso U M hM).hom.app (op V) q) ∨
        ConcreteCategory.hom ((markedCylinderBallForgetIso U M hM).hom.app (op V) q).down
          V.top ∈ T :=
  (mem_marked_markedCylinder_markedBall_iff q).trans (or_congr Iff.rfl (hT _).symm)

theorem cylAtomIso_pole_top_mem_faces (U : Atom) (γ : Bool) :
    (cylAtomIso U).hom (SuspCarrier.pole γ, U.top) ∈
      (grayCylinder.obj U).ogp.faces γ (grayCylinder.obj U).top := by
  have hrem : map (cylAtomIso U).hom
      (LowerSet.Iic (SuspCarrier.pole (!!γ) : globe.{0} 1) ×ˢ (⊤ : LowerSet U.ogp)) =
      LowerSet.Iic ((cylAtomIso U).hom (SuspCarrier.pole γ, U.top)) := by
    rw [Bool.not_not, Iic_cylAtomIso, U.Iic_top]
  have h := mem_faceSet_top_of_isRewritableSubmolecule (endpointHornData (!γ) U)
    (x := (cylAtomIso U).hom (SuspCarrier.pole γ, U.top)) hrem
  rwa [show (endpointHornData (!γ) U).side = γ from Bool.not_not γ] at h

theorem fst_inv_cylAtomIso_pole_ne_top (U : Atom) (γ : Bool) (x : U.ogp) :
    ((cylAtomIso U).inv ((cylAtomIso U).hom (SuspCarrier.pole γ, x))).1 ≠ ⊤ := fun h => by
  rw [Iso.hom_inv_id_apply] at h
  change (SuspCarrier.pole γ : globe.{0} 1) = ⊤ at h
  cases γ <;> exact absurd h (by decide)

theorem pos_grade_of_mem_empty (U : Atom) : ∀ z ∈ (∅ : Set U.ogp), 0 < grade ℕ z :=
  fun _ h => h.elim

noncomputable def sphereToMarkedBall (U : Atom) :
    (MarkedPresheaf.flat atomMarking).obj (sphere.{u} U) ⟶
      markedBall U ∅ (pos_grade_of_mem_empty U) :=
  MarkedPresheaf.homMk (sphereInclusion U) fun V x hx =>
    (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 (Or.inl (isDegenerate_app _
      ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V x).1 hx)))

noncomputable def flatBallIso (U : Atom) :
    (MarkedPresheaf.flat atomMarking).obj (ball.{u} U) ≅
      markedBall U ∅ (pos_grade_of_mem_empty U) :=
  markedIsoMk (Iso.refl _) fun V x =>
    (MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V x).trans
      (Iff.trans ⟨Or.inl, fun h => h.resolve_right fun h' => h'⟩
        (MarkedPresheaf.mem_marked_ofMarking (ball U)
          (ballMarking U ∅ (pos_grade_of_mem_empty U)) V x).symm)

noncomputable def flatSphereInclusionArrowIso (U : Atom) :
    Arrow.mk ((MarkedPresheaf.flat atomMarking).map (sphereInclusion.{u} U)) ≅
      Arrow.mk (sphereToMarkedBall U) :=
  Arrow.isoMk (Iso.refl _) (flatBallIso U) (MarkedPresheaf.hom_ext (by ext V x; rfl))

theorem closure_cylAtomIso_pole_top (U : Atom) (γ : Bool) :
    LowerSet.Iic ((cylAtomIso U).hom (SuspCarrier.pole γ, U.top)) = endpointSubset γ U := by
  rw [Iic_cylAtomIso, U.Iic_top, endpointSubset_eq_map]

theorem eq_top_of_fst_eq_top_of_snd_eq_top (U : Atom) {z : (grayCylinder.obj U).ogp}
    (h : ((cylAtomIso U).inv z).1 = ⊤) (h' : ((cylAtomIso U).inv z).2 = U.top) :
    z = (grayCylinder.obj U).top := by
  refine IsInclusion.injective (f := (cylAtomIso U).inv) ?_
  rw [symm_cylAtomIso_top]
  exact Prod.ext h h'

theorem hornLike_endpointBox_sphereToMarkedBall (ε : Bool) (U : Atom) :
    HornLike.{u} (markedExactCylinder.endpointBox ε (sphereToMarkedBall U)) := by
  obtain ⟨L, R, Mst, hs, hlast, htops⟩ := exists_isStagedPasting_endpoint U (!ε)
  have hpos : 0 < (grayCylinder.obj U).dimension := by
    simp only [dimension_grayCylinder_obj]; omega
  have hT : ∀ z : (grayCylinder.obj U).ogp, ((cylAtomIso U).inv z).1 = ⊤ → 0 < grade ℕ z :=
    fun z hz => pos_grade_of_mem_cylinderBallMarking U (pos_grade_of_mem_empty U) z (Or.inl hz)
  let m' := MarkedHornData.ofStaged (grayCylinder.obj U) hpos (!ε) _
    (cylAtomIso_pole_top_mem_faces U (!ε)) (fun z => ((cylAtomIso U).inv z).1 = ⊤)
    hT L R Mst hs hlast htops
  have hbd : ∀ z, z ∈ (grayCylinder.obj U).ogp.bdryFull ⊤ ↔ z ≠ (grayCylinder.obj U).top :=
    (grayCylinder.obj U).mem_bdryFull_top_iff
  have htop' := congrArg Prod.fst (symm_cylAtomIso_top U)
  have htm : ∀ z, z ∈ m'.targetMarking ↔ z ∈ cylinderBallMarking U ∅ := by
    intro z
    refine m'.mem_targetMarking_iff.trans ⟨?_, fun hz => ?_⟩
    · rintro (rfl | ⟨hsub, -⟩ | hz)
      · exact Or.inl htop'
      · have hf : (cylAtomIso U).hom (SuspCarrier.pole ε, U.top) ∈
            (grayCylinder.obj U).ogp.faces (!!ε) (grayCylinder.obj U).top :=
          (Bool.not_not ε).symm ▸ cylAtomIso_pole_top_mem_faces U ε
        exact (fst_inv_cylAtomIso_pole_ne_top U ε U.top (hsub hf).2).elim
      · exact Or.inl hz.2
    · have hR : ((cylAtomIso U).inv z).1 = ⊤ := hz.resolve_right fun h => h
      by_cases hzt : z = (grayCylinder.obj U).top
      · exact Or.inl hzt
      · refine Or.inr (Or.inr ⟨m'.mem_hornSet_iff.2 ⟨(hbd z).2 hzt, ?_⟩, hR⟩)
        rintro rfl
        exact fst_inv_cylAtomIso_pole_ne_top U (!ε) U.top hR
  refine hornLike_of_ball m' _ ((MarkedPresheaf.mono_iff _).1
    (markedExactCylinder.mono_endpointBox ε _ ((MarkedPresheaf.mono_iff _).2
      (mono_sphereInclusion U)))) (markedCylinderBallForgetIso U ∅ (pos_grade_of_mem_empty U))
    (fun V q => mem_marked_markedCylinder_markedBall_iff_of _ htm q) ?_ ?_
  · refine (range_forget_map_endpointBox_comp ε (sphereToMarkedBall U)).trans ?_
    have h := range_grayCylinderFunctor_map_closedSubpresheaf_ι U (U.ogp.bdryFull ⊤)
    rw [closedSubpresheaf_univ_erase_top U] at h
    refine (congrArg (· ⊔ _) h).trans ?_
    refine (closedSubpresheaf_union _ _ _).symm.trans ?_
    have e : (endpointHornData ε U).removed =
        LowerSet.Iic ((cylAtomIso U).hom (SuspCarrier.pole (!ε), U.top)) :=
      ((closure_cylAtomIso_pole_top U (!ε)).trans (endpointSubset_eq_map (!ε) U)).symm
    refine congrArg (closedSubpresheaf _) ((hornSubset_endpointHornData ε U).symm.trans
      (SetLike.ext fun z => ?_))
    change z ∈ hornSubset (endpointHornData ε U) ↔ z ∈ hornSubset m'.toHornData
    refine (mem_hornSubset_iff _ z).trans (Iff.trans ?_ (mem_hornSubset_iff m'.toHornData z).symm)
    rw [e]
    exact Iff.rfl
  · intro V c a ha him hd
    obtain ⟨haH, haT⟩ := ha
    have htop := apply_top_eq_of_map_eq c him
    have hR : ((cylAtomIso U).inv (c V.top)).1 = ⊤ := htop ▸ haT
    have hne : ((cylAtomIso U).inv (c V.top)).2 ≠ U.top := fun heq =>
      (hbd a).1 (m'.hornSet_subset_bdryFull haH)
        (htop.symm.trans (eq_top_of_fst_eq_top_of_snd_eq_top U hR heq))
    let k : (sphere U).obj (op (Atom.ofClosure U ((cylAtomIso U).inv (c V.top)).2)) :=
      ⟨⟨Atom.closureIncl U _⟩, closedSubpresheaf_univ_erase_top U ▸
        fun t => closureIncl_mem_of_closed U (U.ogp.bdryFull ⊤)
          ⟨_, (U.mem_bdryFull_top_iff _).2 hne⟩ t⟩
    obtain ⟨p, hp, hpc⟩ := exists_mem_marked_markedCylinder_eq (sphereToMarkedBall U) c hR k rfl
    refine ⟨(MarkedPresheaf.forget.map (pushout.inl _ _)).app _ p,
      MarkedPresheaf.map_mem_marked _ hp, Eq.trans ?_ hpc⟩
    exact congrArg (fun f => (markedCylinderBallForgetIso U ∅ (pos_grade_of_mem_empty U)).hom.app
      (op V) ((MarkedPresheaf.forget.map f).app (op V) p))
      (markedExactCylinder.inl_endpointBox ε (sphereToMarkedBall U))

theorem cylAtomIso_top_top (U : Atom) :
    (cylAtomIso U).hom ((⊤ : globe.{0} 1), U.top) = (grayCylinder.obj U).top :=
  (congrArg (cylAtomIso U).hom (symm_cylAtomIso_top U)).symm.trans (Iso.inv_hom_id_apply _ _)

theorem cylAtomIso_top_mem_faces (U : Atom) {γ : Bool} {x : U.ogp}
    (hx : x ∈ U.ogp.faces γ U.top) :
    (cylAtomIso U).hom ((⊤ : globe.{0} 1), x) ∈
      (grayCylinder.obj U).ogp.faces (!γ) (grayCylinder.obj U).top := by
  rw [← cylAtomIso_top_top U]
  refine (IsInclusion.mem_faces_iff (f := (cylAtomIso U).hom)).2
    (mem_faces_grayProduct.2 (.inr ⟨rfl, ?_⟩))
  rw [grade_top_globe, Nat.bodd_one, Bool.true_xor, Bool.not_not]
  exact hx

theorem cases_of_mem_faces_grayCylinder_top (U : Atom) {γ : Bool}
    {y : (grayCylinder.obj U).ogp}
    (hy : y ∈ (grayCylinder.obj U).ogp.faces γ (grayCylinder.obj U).top) :
    (((cylAtomIso U).inv y).1 ≠ ⊤ ∧ ((cylAtomIso U).inv y).2 = U.top) ∨
      (((cylAtomIso U).inv y).1 = ⊤ ∧ ((cylAtomIso U).inv y).2 ∈ U.ogp.faces (!γ) U.top) := by
  have h1 := (IsInclusion.mem_faces_iff (f := (cylAtomIso U).inv)).2 hy
  rw [symm_cylAtomIso_top] at h1
  rcases mem_faces_grayProduct.1 h1 with ⟨hc, hb⟩ | ⟨ha, hc⟩
  · exact Or.inl ⟨hc.1.lt.ne, hb⟩
  · change ((cylAtomIso U).inv y).2 ∈
      U.ogp.faces (xor (grade ℕ (⊤ : globe.{0} 1)).bodd γ) U.top at hc
    rw [grade_top_globe, Nat.bodd_one, Bool.true_xor] at hc
    exact Or.inr ⟨ha, hc⟩

theorem eq_cylAtomIso_top_of_fst_eq_top (U : Atom) {z : (grayCylinder.obj U).ogp}
    (h : ((cylAtomIso U).inv z).1 = ⊤) :
    z = (cylAtomIso U).hom ((⊤ : globe.{0} 1), ((cylAtomIso U).inv z).2) :=
  (Iso.inv_hom_id_apply (cylAtomIso U) z).symm.trans (congrArg (cylAtomIso U).hom (Prod.ext h rfl))

noncomputable def markedTargetIso (m : MarkedHornData) :
    m.target ≅ markedBall.{u} m.atom m.targetMarking (fun a ha => (m.targetMarking_mem a ha).2) :=
  markedIsoMk (closedSubpresheafUnivIso m.atom) fun V x =>
    (mem_marked_markedClosedSubset_univ_iff _ _ _ x).trans
      (MarkedPresheaf.mem_marked_ofMarking (ball m.atom) (ballMarking _ _ _) V _).symm

theorem exists_comp_bothBox_eq_endpoint {K Y : MarkedDiagSet.{u}} (g : K ⟶ Y) (ε : Bool) :
    ∃ j : Y ⟶ markedExactCylinder.bothBoxSource g,
      j ≫ markedExactCylinder.bothBox g = (markedExactCylinder.endpoint ε).app Y := by
  refine ⟨cond ε coprod.inr coprod.inl ≫ pushout.inr _ _, ?_⟩
  rw [Category.assoc, markedExactCylinder.inr_bothBox, ExactCylinder.endpoints]
  cases ε <;> first | exact coprod.inl_desc _ _ | exact coprod.inr_desc _ _

theorem hornLike_bothBox_markedTargetIso (m : MarkedHornData) :
    HornLike.{u}
      (markedExactCylinder.bothBox (markedHornInclusion m ≫ (markedTargetIso m).hom)) := by
  obtain ⟨L, R, Mst, hs, hlast, htops⟩ := m.exists_isStagedPasting_cylinder
  have hpos : 0 < (grayCylinder.obj m.atom).dimension := by
    simp only [dimension_grayCylinder_obj]; omega
  have hM : ∀ a ∈ m.targetMarking, 0 < grade ℕ a := fun a ha => (m.targetMarking_mem a ha).2
  let m' := MarkedHornData.ofStaged (grayCylinder.obj m.atom) hpos (!m.side) _
    (cylAtomIso_top_mem_faces m.atom m.face_mem)
    (fun z => ((cylAtomIso m.atom).inv z).1 = ⊤ ∨ ((cylAtomIso m.atom).inv z).2 ∈ m.targetMarking)
    (fun z hz => pos_grade_of_mem_cylinderBallMarking m.atom hM z hz) L R Mst hs hlast htops
  have hbd : ∀ z, z ∈ (grayCylinder.obj m.atom).ogp.bdryFull ⊤ ↔
      z ≠ (grayCylinder.obj m.atom).top :=
    (grayCylinder.obj m.atom).mem_bdryFull_top_iff
  have hRface := congrArg Prod.fst (Iso.hom_inv_id_apply (cylAtomIso m.atom) (⊤, m.face))
  have hfaces : ∀ y ∈ (grayCylinder.obj m.atom).ogp.faces m.side
      (grayCylinder.obj m.atom).top, y ∈ m'.marking := by
    intro y hy
    have hne : y ≠ (grayCylinder.obj m.atom).top := hy.1.lt.ne
    rcases cases_of_mem_faces_grayCylinder_top m.atom hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨m'.mem_hornSet_iff.2 ⟨(hbd y).2 hne, ?_⟩,
        Or.inr (h2 ▸ m.mem_targetMarking_iff.2 (Or.inl rfl))⟩
      rintro rfl
      exact h1 hRface
    · refine ⟨m'.mem_hornSet_iff.2 ⟨(hbd y).2 hne, ?_⟩, Or.inl h1⟩
      intro hyf
      have h3 : ((cylAtomIso m.atom).inv y).2 = m.face := by
        rw [hyf]
        exact congrArg Prod.snd (Iso.hom_inv_id_apply (cylAtomIso m.atom) _)
      rw [h3] at h2
      exact Bool.not_ne_self m.side (h2.2.symm.trans m.face_mem.2)
  have htop' := congrArg Prod.fst (symm_cylAtomIso_top m.atom)
  have htm : ∀ z, z ∈ m'.targetMarking ↔ z ∈ cylinderBallMarking m.atom m.targetMarking := by
    intro z
    refine m'.mem_targetMarking_iff.trans ⟨?_, fun hz => ?_⟩
    · rintro (rfl | ⟨-, rfl⟩ | hz)
      · exact Or.inl htop'
      · exact Or.inl hRface
      · exact hz.2
    · by_cases hzt : z = (grayCylinder.obj m.atom).top
      · exact Or.inl hzt
      by_cases hzf : z = m'.face
      · refine Or.inr (Or.inl ⟨fun y hy => hfaces y ?_, hzf⟩)
        change y ∈ (grayCylinder.obj m.atom).ogp.faces (!!m.side) _ at hy
        rwa [Bool.not_not] at hy
      · exact Or.inr (Or.inr ⟨m'.mem_hornSet_iff.2 ⟨(hbd z).2 hzt, hzf⟩, hz⟩)
  have hmono : Mono (markedHornInclusion m) :=
    markedHorns_le_monomorphisms _ (MorphismProperty.ofHoms.mk m)
  refine hornLike_of_ball m' _ ((MarkedPresheaf.mono_iff _).1
    (markedExactCylinder.mono_bothBox _ (mono_comp _ _)))
    (markedCylinderBallForgetIso m.atom _ hM)
    (fun V q => mem_marked_markedCylinder_markedBall_iff_of _ htm q) ?_ ?_
  · refine (range_forget_map_bothBox_comp _).trans ?_
    refine (congrArg (· ⊔ _)
      (range_grayCylinderFunctor_map_closedSubpresheaf_ι m.atom m.hornSet)).trans ?_
    refine (congrArg (_ ⊔ ·) (closedSubpresheaf_union _ _ _).symm).trans ?_
    refine (closedSubpresheaf_union _ _ _).symm.trans ?_
    have e : (cylinderHornData m.toHornData).removed =
        LowerSet.Iic ((cylAtomIso m.atom).hom ((⊤ : globe.{0} 1), m.face)) := by
      change map (cylAtomIso m.atom).hom ((⊤ : LowerSet (globe.{0} 1)) ×ˢ .Iic m.face) = _
      rw [Iic_cylAtomIso, LowerSet.Iic_top]
    refine congrArg (closedSubpresheaf _) ((hornSubset_cylinderHornData m.toHornData).symm.trans
      (SetLike.ext fun z => ?_))
    change z ∈ hornSubset (cylinderHornData m.toHornData) ↔ z ∈ hornSubset m'.toHornData
    refine (mem_hornSubset_iff _ z).trans (Iff.trans ?_ (mem_hornSubset_iff m'.toHornData z).symm)
    rw [e]
    exact Iff.rfl
  · intro V c a ha him hd
    obtain ⟨haH, haT⟩ := ha
    obtain ⟨haB, haF⟩ := m'.mem_hornSet_iff.1 haH
    have htop := apply_top_eq_of_map_eq c him
    by_cases hR : ((cylAtomIso m.atom).inv (c V.top)).1 = ⊤
    · have hy : ((cylAtomIso m.atom).inv (c V.top)).2 ∈ m.hornSet := by
        refine m.mem_hornSet_iff.2 ⟨?_, fun h => haF ?_⟩
        · exact (m.atom.mem_bdryFull_top_iff _).2 fun h => (hbd a).1 haB
            (htop.symm.trans (eq_top_of_fst_eq_top_of_snd_eq_top m.atom hR h))
        · exact htop.symm.trans ((eq_cylAtomIso_top_of_fst_eq_top m.atom hR).trans (by rw [h]; rfl))
      let k : m.source.underlying.obj
          (op (Atom.ofClosure m.atom ((cylAtomIso m.atom).inv (c V.top)).2)) :=
        ⟨⟨Atom.closureIncl m.atom _⟩,
          fun t => closureIncl_mem_of_closed m.atom m.hornSet ⟨_, hy⟩ t⟩
      obtain ⟨p, hp, hpc⟩ := exists_mem_marked_markedCylinder_eq
        (markedHornInclusion m ≫ (markedTargetIso m).hom) c hR k rfl
      refine ⟨(MarkedPresheaf.forget.map (pushout.inl _ _)).app _ p,
        MarkedPresheaf.map_mem_marked _ hp, Eq.trans ?_ hpc⟩
      exact congrArg (fun f => (markedCylinderBallForgetIso m.atom _ hM).hom.app
        (op V) ((MarkedPresheaf.forget.map f).app (op V) p))
        (markedExactCylinder.inl_bothBox (markedHornInclusion m ≫ (markedTargetIso m).hom))
    · obtain ⟨ε, hε⟩ : ∃ ε, ((cylAtomIso m.atom).inv (c V.top)).1 = SuspCarrier.pole ε := by
        rcases hw : ((cylAtomIso m.atom).inv (c V.top)).1 with ε | ⟨⟨⟩⟩
        · exact ⟨ε, rfl⟩
        · exact (hR (by rw [hw]; rfl)).elim
      have hsnd : ((cylAtomIso m.atom).inv (c V.top)).2 ∈ m.targetMarking :=
        (htop ▸ haT).resolve_left hR
      have hd' : ULift.up (c ≫ grayContraction.app m.atom) ∈ (markedBall m.atom _ hM).marked V :=
        (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 (Or.inr hsnd)
      obtain ⟨j, hj⟩ :=
        exists_comp_bothBox_eq_endpoint (markedHornInclusion m ≫ (markedTargetIso m).hom) ε
      refine ⟨(MarkedPresheaf.forget.map j).app _ ⟨c ≫ grayContraction.app m.atom⟩,
        MarkedPresheaf.map_mem_marked _ hd',
        Eq.trans ?_ (endpoint_contraction_eq (M := m.targetMarking) (hM := hM) ε c hε)⟩
      exact congrArg (fun f : markedBall m.atom _ hM ⟶ _ =>
        (markedCylinderBallForgetIso m.atom _ hM).hom.app (op V)
        ((MarkedPresheaf.forget.map f).app (op V) ⟨c ≫ grayContraction.app m.atom⟩)) hj

theorem hornLike_bothBox_markedHornInclusion (m : MarkedHornData) :
    HornLike.{u} (markedExactCylinder.bothBox (markedHornInclusion m)) :=
  (hornLike_bothBox_markedTargetIso m).of_arrow _
    (epi_leibnizSourceMap_endpointsNatTrans (𝟙 _) (markedTargetIso m).inv (by simp))
    (markedExactCylinder.I.mapIso (markedTargetIso m).symm)
    (NatTrans.leibnizSourceMap_leibnizBox markedExactCylinder.endpointsNatTrans (𝟙 _)
      (markedTargetIso m).inv (by simp)).symm

theorem isIso_forget_map_pushout_inl {A B C : MarkedDiagSet.{u}} (f : A ⟶ B) (g : A ⟶ C)
    [IsIso (MarkedPresheaf.forget.map g)] :
    IsIso (MarkedPresheaf.forget.map (pushout.inl f g)) :=
  ((IsPushout.of_hasPushout f g).map MarkedPresheaf.forget).isIso_inl_of_isIso

theorem isIso_forget_map_markedCylinder_map {K Y : MarkedDiagSet.{u}} (g : K ⟶ Y)
    [IsIso (MarkedPresheaf.forget.map g)] :
    IsIso (MarkedPresheaf.forget.map (markedCylinder.map g)) := by
  exact (NatIso.isIso_map_iff markedCylinderForgetIso g).2
    (inferInstanceAs (IsIso (grayCylinderFunctor.map (MarkedPresheaf.forget.map g))))

theorem isIso_forget_map_coprod_map {A B C D : MarkedDiagSet.{u}} (f : A ⟶ C) (g : B ⟶ D)
    [IsIso (MarkedPresheaf.forget.map f)] [IsIso (MarkedPresheaf.forget.map g)] :
    IsIso (MarkedPresheaf.forget.map (coprod.map f g)) := by
  have : IsIso (coprodComparison MarkedPresheaf.forget A B ≫
      MarkedPresheaf.forget.map (coprod.map f g)) := by
    rw [coprodComparison_natural]
    infer_instance
  exact IsIso.of_isIso_comp_left (coprodComparison MarkedPresheaf.forget A B) _

theorem isIso_forget_map_endpointBox (ε : Bool) {K Y : MarkedDiagSet.{u}} (g : K ⟶ Y)
    [IsIso (MarkedPresheaf.forget.map g)] :
    IsIso (MarkedPresheaf.forget.map (markedExactCylinder.endpointBox ε g)) := by
  have := isIso_forget_map_pushout_inl ((markedExactCylinder.endpoint ε).app K) g
  have h2 : MarkedPresheaf.forget.map (pushout.inl _ _) ≫
      MarkedPresheaf.forget.map (markedExactCylinder.endpointBox ε g) =
        MarkedPresheaf.forget.map (markedCylinder.map g) :=
    congrArg MarkedPresheaf.forget.map (markedExactCylinder.inl_endpointBox ε g)
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (MarkedPresheaf.forget.map (pushout.inl _ _)) _
    this (h2.symm ▸ isIso_forget_map_markedCylinder_map g)

theorem isIso_forget_map_bothBox {K Y : MarkedDiagSet.{u}} (g : K ⟶ Y)
    [IsIso (MarkedPresheaf.forget.map g)] :
    IsIso (MarkedPresheaf.forget.map (markedExactCylinder.bothBox g)) := by
  have := isIso_forget_map_coprod_map g g
  have := isIso_forget_map_pushout_inl (markedExactCylinder.endpoints K) (coprod.map g g)
  have h2 : MarkedPresheaf.forget.map (pushout.inl _ _) ≫
      MarkedPresheaf.forget.map (markedExactCylinder.bothBox g) =
        MarkedPresheaf.forget.map (markedCylinder.map g) :=
    congrArg MarkedPresheaf.forget.map (markedExactCylinder.inl_bothBox g)
  have : IsIso (MarkedPresheaf.forget.map (pushout.inl _ _) ≫
      MarkedPresheaf.forget.map (markedExactCylinder.bothBox g)) :=
    h2.symm ▸ isIso_forget_map_markedCylinder_map g
  exact IsIso.of_isIso_comp_left (MarkedPresheaf.forget.map (pushout.inl _ _)) _

theorem isIso_bothBox_of_isIso_forget {K Y : MarkedDiagSet.{u}} (g : K ⟶ Y)
    [IsIso (MarkedPresheaf.forget.map g)] : IsIso (markedExactCylinder.bothBox g) := by
  have := isIso_forget_map_bothBox g
  let B := MarkedPresheaf.forget.map (markedExactCylinder.bothBox g)
  have hφ : ∀ {V : Atom} (p), (inv B).app (op V) (B.app (op V) p) = p :=
    Iso.hom_inv_id_app_apply (asIso B) _
  have key : ∀ (V : Atom) (x), x ∈ (markedCylinder.obj Y).marked V →
      (inv B).app (op V) x ∈ (markedExactCylinder.bothBoxSource g).marked V := by
    intro V x hx
    rcases mem_marked_markedCylinder_obj_cases Y hx with hd | ⟨U, y, e, rfl⟩ |
      ⟨ε, U, m, hm, e, rfl⟩
    · exact MarkedDiagSet.mem_marked_of_isDegenerate _ (isDegenerate_app _ hd)
    · let k := (inv (MarkedPresheaf.forget.map g)).app (op U) y
      have hk : (MarkedPresheaf.forget.map g).app (op U) k = y :=
        congrArg (fun f => f.app (op U) y) (IsIso.inv_hom_id (MarkedPresheaf.forget.map g))
      let q := (markedCylinder.obj K).underlying.map e.hom.op (markedCylinderUnitCell K k)
      have hq : q ∈ (markedCylinder.obj K).marked V :=
        ((markedCylinder.obj K).transport e _).1 (mem_marked_markedCylinderUnitCell K k)
      have e1 := congrArg (fun f => (MarkedPresheaf.forget.map f).app (op V) q)
        (markedExactCylinder.inl_bothBox g)
      have e2 : (MarkedPresheaf.forget.map (markedCylinder.map g)).app (op V) q =
          (markedCylinder.obj Y).underlying.map e.hom.op (markedCylinderUnitCell Y y) :=
        (NatTrans.naturality_apply (MarkedPresheaf.forget.map (markedCylinder.map g)) e.hom.op
          _).trans (congrArg _ ((forget_map_markedCylinder_map_unitCell g k).trans
            (congrArg _ hk)))
      have h4 := (congrArg ((inv B).app (op V)) (e1.trans e2)).symm.trans (hφ _)
      exact h4 ▸ MarkedPresheaf.map_mem_marked _ hq
    · obtain ⟨j, hj⟩ := exists_comp_bothBox_eq_endpoint g ε
      have e1 := congrArg (fun f => (MarkedPresheaf.forget.map f).app (op V)
        (Y.underlying.map e.hom.op m)) hj
      have e2 := NatTrans.naturality_apply
        (MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app Y)) e.hom.op m
      have h4 := (congrArg ((inv B).app (op V)) (e1.trans e2)).symm.trans (hφ _)
      exact h4 ▸ MarkedPresheaf.map_mem_marked _ ((Y.transport e m).1 hm)
  exact ⟨⟨MarkedPresheaf.homMk _ key, MarkedPresheaf.hom_ext (IsIso.hom_inv_id B),
    MarkedPresheaf.hom_ext (IsIso.inv_hom_id B)⟩⟩

theorem pos_grade_of_mem_top (U : Atom) (hU : 0 < U.dimension) :
    ∀ z ∈ ({U.top} : Set U.ogp), 0 < grade ℕ z :=
  fun _ hz => (Set.mem_singleton_iff.1 hz).symm ▸ U.dimension_eq ▸ hU

noncomputable def markingToMarkedBall (U : Atom) (hU : 0 < U.dimension) :
    markedBall.{u} U ∅ (pos_grade_of_mem_empty U) ⟶
      markedBall U {U.top} (pos_grade_of_mem_top U hU) :=
  MarkedPresheaf.homMk (𝟙 _) fun _ _ hx =>
    (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
      (((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hx).imp_right fun h => h.elim)

noncomputable def yonedaUnmarkedIso (U : Atom) :
    (MarkedPresheaf.yoneda atomMarking).obj ((MarkedSite.unmarked atomMarking).obj U) ≅
      markedBall.{u} U ∅ (pos_grade_of_mem_empty U) :=
  markedIsoMk (ballIsoForgetYoneda _).symm fun V g => by
    refine (mem_marked_yoneda_obj_iff _ V g).trans ⟨?_, ?_⟩
    · rintro ⟨-, ⟨h, -⟩ | h⟩
      · exact absurd h Bool.false_ne_true
      · exact (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
          (Or.inl (isDegenerate_ball_of_degenerate h))
    · intro h
      rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 h with
        ⟨W, p, y, hp, hni, hpy⟩ | h
      · exact ⟨dimension_pos_of_isDegenerate ⟨W, p, y, hp, hni, hpy⟩,
          Or.inr ⟨W, p, y.down, ⟨hp, hni⟩, congrArg ULift.down hpy⟩⟩
      · exact h.elim

noncomputable def yonedaMarkedIso (U : Atom) (h : atomMarking.markable U) :
    (MarkedPresheaf.yoneda.{u} atomMarking).obj (MarkedSite.marked U h) ≅
      markedBall U {U.top} (pos_grade_of_mem_top U h) :=
  markedIsoMk (ballIsoForgetYoneda _).symm fun V g => by
    refine (mem_marked_yoneda_obj_iff _ V g).trans ⟨?_, ?_⟩
    · rintro ⟨-, ⟨-, hi⟩ | hd⟩
      · exact (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
          (Or.inr (iso_hom_apply_top (asIso g.down.1)))
      · exact (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
          (Or.inl (isDegenerate_ball_of_degenerate hd))
    · intro hg
      rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hg with
        ⟨W, p, y, hp, hni, hpy⟩ | ht
      · exact ⟨dimension_pos_of_isDegenerate ⟨W, p, y, hp, hni, hpy⟩,
          Or.inr ⟨W, p, y.down, ⟨hp, hni⟩, congrArg ULift.down hpy⟩⟩
      · rcases isIso_or_isDegenerate_map_of_apply_top_eq (Y := ball.{u} U) g.down.1 ht ⟨𝟙 U⟩ with
          hi | hd
        · exact ⟨(Atom.dimension_eq_of_iso
            (@asIso _ _ _ _ (g.down.1 : V ⟶ U) hi)).symm ▸ h, Or.inl ⟨rfl, hi⟩⟩
        · obtain ⟨W, p, y, hp, hni, hpy⟩ := hd
          exact ⟨dimension_pos_of_isDegenerate ⟨W, p, y, hp, hni, hpy⟩,
            Or.inr ⟨W, p, y.down, ⟨hp, hni⟩,
              (congrArg ULift.down hpy).trans (Category.comp_id (g.down.1 : V ⟶ U))⟩⟩

noncomputable def markingMapArrowIso (U : Atom) (h : atomMarking.markable U) :
    Arrow.mk ((MarkedPresheaf.yoneda atomMarking).map
      (MarkedSite.toSelf (MarkedSite.marked U h))) ≅ Arrow.mk (markingToMarkedBall.{u} U h) :=
  Arrow.isoMk (yonedaUnmarkedIso U) (yonedaMarkedIso U h) (MarkedPresheaf.hom_ext (by ext V x; rfl))

theorem eq_cylAtomIso_pole_top (U : Atom) {z : (grayCylinder.obj U).ogp} {δ : Bool}
    (h : ((cylAtomIso U).inv z).1 = SuspCarrier.pole δ) (h' : ((cylAtomIso U).inv z).2 = U.top) :
    z = (cylAtomIso U).hom (SuspCarrier.pole δ, U.top) :=
  (Iso.inv_hom_id_apply (cylAtomIso U) z).symm.trans (congrArg (cylAtomIso U).hom (Prod.ext h h'))

theorem hasLiftingProperty_endpointBox_markingToMarkedBall (ε : Bool) (U : Atom)
    (hU : 0 < U.dimension) {X : MarkedDiagSet.{u}} (hH : HasMarkedRLP markedHorns X)
    (hI : HasMarkedRLP invertorGenerators X) :
    HasLiftingProperty (markedExactCylinder.endpointBox ε (markingToMarkedBall U hU))
      (terminal.from X) := by
  have hTop := pos_grade_of_mem_top U hU
  have : IsIso (MarkedPresheaf.forget.map (markingToMarkedBall U hU)) :=
    inferInstanceAs (CategoryTheory.IsIso (𝟙 _))
  have hb := isIso_forget_map_endpointBox ε (markingToMarkedBall U hU)
  refine ⟨fun {u _} _ => ?_⟩
  let Ψ := markedCylinderBallForgetIso U {U.top} hTop
  let B := MarkedPresheaf.forget.map (markedExactCylinder.endpointBox ε (markingToMarkedBall U hU))
  let l₀ := inv B ≫ MarkedPresheaf.forget.map u
  have hl₀ : ∀ {V : Atom} (p), l₀.app (op V) (B.app (op V) p) =
      (MarkedPresheaf.forget.map u).app (op V) p := fun p =>
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (IsIso.hom_inv_id_assoc B (MarkedPresheaf.forget.map u)) _) p
  have hB : ∀ {V : Atom} (q),
      let a := (cylAtomIso U).inv (ConcreteCategory.hom (Ψ.hom.app (op V) q).down V.top)
      a.1 = ⊤ ∨ (a.1 = SuspCarrier.pole ε ∧ a.2 = U.top) →
        l₀.app (op V) q ∈ X.marked V := by
    intro V q a hq
    suffices h : ∃ p ∈ (markedExactCylinder.endpointBoxSource ε
        (markingToMarkedBall U hU)).marked V, B.app (op V) p = q by
      obtain ⟨p, hp, rfl⟩ := h
      exact (hl₀ p).symm ▸ MarkedPresheaf.map_mem_marked u hp
    rcases hq with hR | ⟨hε, ht⟩
    · obtain ⟨p, hp, hpc⟩ := exists_mem_marked_markedCylinder_eq (markingToMarkedBall U hU)
        (Ψ.hom.app (op V) q).down hR ⟨Atom.closureIncl U _⟩ rfl
      refine ⟨(MarkedPresheaf.forget.map (pushout.inl _ _)).app _ p,
        MarkedPresheaf.map_mem_marked _ hp, (Ψ.app (op V)).toEquiv.injective ?_⟩
      exact (congrArg (fun f => Ψ.hom.app (op V)
        ((MarkedPresheaf.forget.map f).app (op V) p))
          (markedExactCylinder.inl_endpointBox ε (markingToMarkedBall U hU))).trans hpc
    · have hd : ULift.up ((Ψ.hom.app (op V) q).down ≫ grayContraction.app U) ∈
          (markedBall U {U.top} hTop).marked V :=
        (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 (Or.inr ht)
      refine ⟨(MarkedPresheaf.forget.map (pushout.inr _ _)).app _
        ⟨(Ψ.hom.app (op V) q).down ≫ grayContraction.app U⟩,
        MarkedPresheaf.map_mem_marked _ hd, (Ψ.app (op V)).toEquiv.injective ?_⟩
      exact (congrArg (fun f : markedBall U {U.top} hTop ⟶ _ =>
        Ψ.hom.app (op V) ((MarkedPresheaf.forget.map f).app (op V)
        ⟨(Ψ.hom.app (op V) q).down ≫ grayContraction.app U⟩))
          (markedExactCylinder.inr_endpointBox ε (markingToMarkedBall U hU))).trans
            (endpoint_contraction_eq ε _ hε)
  let z := l₀.app (op (grayCylinder.obj U)) (Ψ.inv.app _ ⟨𝟙 (grayCylinder.obj U)⟩)
  have hz : ∀ {V : Atom} (q), l₀.app (op V) q =
      X.underlying.map (Ψ.hom.app (op V) q).down.op z := by
    intro V q
    have h := NatTrans.naturality_apply (Ψ.inv ≫ l₀) (Ψ.hom.app (op V) q).down.op
      (⟨𝟙 (grayCylinder.obj U)⟩ : (ball (grayCylinder.obj U)).obj (op (grayCylinder.obj U)))
    change l₀.app _ (Ψ.inv.app _ ⟨(Ψ.hom.app (op V) q).down ≫ 𝟙 _⟩) = _ at h
    simp only [Category.comp_id] at h
    change l₀.app _ (Ψ.inv.app _ (Ψ.hom.app _ q)) = _ at h
    exact (congrArg (l₀.app _) (Iso.hom_inv_id_app_apply Ψ _ q)).symm.trans h
  have htop' := congrArg Prod.fst (symm_cylAtomIso_top U)
  have hzm : z ∈ X.marked _ := hB _ (Or.inl ((Iso.inv_hom_id_app_apply Ψ _ _).symm ▸ htop'))
  obtain ⟨L, R, Mst, hs, hlast, htops⟩ := exists_isStagedPasting_endpoint U (!ε)
  have hpos : 0 < (grayCylinder.obj U).dimension := by
    simp only [dimension_grayCylinder_obj]; omega
  let m₂ := MarkedHornData.ofStaged (grayCylinder.obj U) hpos (!ε) _
    (cylAtomIso_pole_top_mem_faces U (!ε))
    (fun z => ((cylAtomIso U).inv z).1 = ⊤ ∨ ((cylAtomIso U).inv z).2 = U.top)
    (fun z hz => pos_grade_of_mem_cylinderBallMarking U hTop z hz) L R Mst hs hlast
    (fun i hi y hy hyd => Or.inl (htops i hi y hy hyd))
  have hT : ∀ a : (grayCylinder.obj U).ogp,
      (((cylAtomIso U).inv a).1 = ⊤ ∨ ((cylAtomIso U).inv a).2 = U.top) →
      a ≠ m₂.face → ((cylAtomIso U).inv a).1 = ⊤ ∨
        (((cylAtomIso U).inv a).1 = SuspCarrier.pole ε ∧ ((cylAtomIso U).inv a).2 = U.top) := by
    rintro a (hR | ht) hne
    · exact Or.inl hR
    rcases hδ : ((cylAtomIso U).inv a).1 with δ | ⟨⟨⟩⟩
    · refine Or.inr ⟨?_, ht⟩
      by_cases hδε : δ = ε
      · rw [hδε]
      · exact absurd (eq_cylAtomIso_pole_top U (δ := !ε) (by
          rw [hδ, Bool.eq_not_of_ne hδε]) ht) hne
    · exact Or.inl rfl
  have hk : 2 ≤ m₂.atom.dimension := by
    change 2 ≤ (grayCylinder.obj U).dimension
    rw [dimension_grayCylinder_obj]; omega
  have hw : m₂.MarksHorn X (realize.map m₂.hornIncl ≫ (ofCell z).map) := by
    rintro a ⟨haH, haT⟩
    obtain ⟨-, haF⟩ := m₂.mem_hornSet_iff.1 haH
    let q := Ψ.inv.app (op (Atom.ofClosure (grayCylinder.obj U) a))
      ⟨Atom.closureIncl (grayCylinder.obj U) a⟩
    have hc : Ψ.hom.app _ q = ⟨Atom.closureIncl (grayCylinder.obj U) a⟩ :=
      Iso.inv_hom_id_app_apply Ψ _ _
    have hcl := hB q (by rw [hc]; exact (Atom.closureIncl_top _ a).symm ▸ hT a haT haF)
    rw [hz q, hc] at hcl
    exact hcl
  have hsub : m₂.atom.ogp.faces (!m₂.side) m₂.atom.top ⊆ m₂.marking := by
    intro y hy
    change y ∈ (grayCylinder.obj U).ogp.faces (!!ε) (grayCylinder.obj U).top at hy
    rw [Bool.not_not] at hy
    have hbd : y ∈ (grayCylinder.obj U).ogp.bdryFull ⊤ :=
      ((grayCylinder.obj U).mem_bdryFull_top_iff y).2 hy.1.lt.ne
    refine ⟨m₂.mem_hornSet_iff.2 ⟨hbd, fun hyf => ?_⟩, ?_⟩
    · have hf : m₂.face ∈ (grayCylinder.obj U).ogp.faces (!ε) (grayCylinder.obj U).top :=
        cylAtomIso_pole_top_mem_faces U (!ε)
      rw [← hyf] at hf
      exact Bool.not_ne_self ε (hf.2.symm.trans hy.2)
    · rcases cases_of_mem_faces_grayCylinder_top U hy with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact Or.inr h2
      · exact Or.inl h1
  obtain ⟨z', hz', hz'm, hz'f⟩ :=
    hasMarkedRLP_markedHorns_iff_fills.1 hH m₂ (realize.map m₂.hornIncl ≫ (ofCell z).map) hw
  obtain ⟨c, hc, hct⟩ := exists_marked_comparisonCell hH m₂ hk hz'.symm hw hzm hz'm
  obtain ⟨c', hc', hct'⟩ := exists_marked_comparisonCell hH m₂ hk hz' (hz' ▸ hw) hz'm hzm
  have hface := mem_marked_of_marked_comparison hH hI (hz'f hsub) hc hc' hct hct'
  have hmk : ∀ (V : Atom) (q), q ∈ (markedCylinder.obj (markedBall U {U.top} hTop)).marked V →
      l₀.app (op V) q ∈ X.marked V := by
    intro V q hq
    have hdeg : IsDegenerate (ball (grayCylinder.obj U)) (Ψ.hom.app (op V) q) →
        l₀.app (op V) q ∈ X.marked V := fun hd =>
      X.mem_marked_of_isDegenerate (isDegenerate_app l₀
        ((Iso.hom_inv_id_app_apply Ψ _ q) ▸ isDegenerate_app Ψ.inv hd))
    rcases (mem_marked_markedCylinder_markedBall_iff q).1 hq with hd | hc
    · exact hdeg hd
    by_cases hf : ConcreteCategory.hom (Ψ.hom.app (op V) q).down V.top =
        m₂.face
    · rcases (grade_apply_top_le (Ψ.hom.app (op V) q).down).lt_or_eq with
        hlt | hdim
      · exact hdeg (isDegenerate_ball_of_degenerate (degenerate_of_grade_lt _ hlt))
      obtain ⟨e, he⟩ := exists_iso_comp_closureIncl (Ψ.hom.app (op V) q).down
        (Atom.map_top_eq_Iic_iff.1 ((Atom.map_top _).trans (congrArg LowerSet.Iic hf)))
        (hdim.symm.trans (congrArg (grade ℕ) hf))
      rw [hz q, ← he, op_comp]
      exact (congrArg (· ∈ X.marked V) (Functor.map_comp_apply X.underlying _ _ z)).mpr
        ((X.transport e _).1 hface)
    · exact hB q (hT _ hc hf)
  refine ⟨⟨⟨MarkedPresheaf.homMk l₀ hmk, MarkedPresheaf.hom_ext ?_, terminal.hom_ext _ _⟩⟩⟩
  exact IsIso.hom_inv_id_assoc B (MarkedPresheaf.forget.map u)

inductive fibrancyGenerators (J : MorphismProperty MarkedDiagSet.{u}) :
    MorphismProperty MarkedDiagSet.{u}
  | generator {A B : MarkedDiagSet.{u}} (g : A ⟶ B) (hg : J g) : fibrancyGenerators J g
  | sphere (ε : Bool) (U : Atom) :
      fibrancyGenerators J (markedExactCylinder.endpointBox ε (sphereToMarkedBall U))
  | marking (ε : Bool) (U : Atom) (hU : 0 < U.dimension) :
      fibrancyGenerators J (markedExactCylinder.endpointBox ε (markingToMarkedBall U hU))
  | bothBox {A B : MarkedDiagSet.{u}} (g : A ⟶ B) (hg : fibrancyGenerators J g) :
      fibrancyGenerators J (markedExactCylinder.bothBox g)

theorem hornLike_or_lifting_of_fibrancyGenerators {J : MorphismProperty MarkedDiagSet.{u}}
    (hJ : ∀ {A B : MarkedDiagSet.{u}} (g : A ⟶ B), J g →
      markedHorns g ∨ IsIso (MarkedPresheaf.forget.map g))
    {X : MarkedDiagSet.{u}} (hX : HasMarkedRLP J X) (hH : HasMarkedRLP markedHorns X)
    (hI : HasMarkedRLP invertorGenerators X)
    {A B : MarkedDiagSet.{u}} (g : A ⟶ B) (hg : fibrancyGenerators J g) :
    HornLike g ∨
      (IsIso (MarkedPresheaf.forget.map g) ∧ HasLiftingProperty g (terminal.from X)) := by
  induction hg with
  | generator g hg =>
    rcases hJ g hg with hh | hi
    · rcases hh with ⟨m⟩
      exact Or.inl (hornLike_markedHornInclusion m)
    · exact Or.inr ⟨hi, hX g hg⟩
  | sphere ε U => exact Or.inl (hornLike_endpointBox_sphereToMarkedBall ε U)
  | marking ε U hU =>
    have : IsIso (MarkedPresheaf.forget.map (markingToMarkedBall U hU)) :=
      inferInstanceAs (CategoryTheory.IsIso (𝟙 _))
    exact Or.inr ⟨isIso_forget_map_endpointBox ε _,
      hasLiftingProperty_endpointBox_markingToMarkedBall ε U hU hH hI⟩
  | bothBox g _ ih =>
    rcases ih with hh | ⟨hi, -⟩
    · exact Or.inl (hh.bothBox hornLike_bothBox_markedHornInclusion)
    · have := isIso_bothBox_of_isIso_forget g
      exact Or.inr ⟨inferInstance, HasLiftingProperty.of_left_iso _ _⟩

theorem anodyne_le_saturation_fibrancyGenerators (J : MorphismProperty MarkedDiagSet.{u}) :
    markedExactCylinder.anodyne J ≤ saturation.{u} (fibrancyGenerators J) := by
  have hmono : MorphismProperty.monomorphisms MarkedDiagSet.{u} =
      saturation.{u} (functorImage (MarkedPresheaf.flat atomMarking) sphereInclusions ⊔
        MarkedPresheaf.markingMaps atomMarking) :=
    (MarkedPresheaf.saturation_functorImage_flat_sup_markingMaps atomMarking
      monomorphisms_eq_saturation_sphereInclusions.symm).symm
  refine markedExactCylinder.anodyne_le J _ ⟨inferInstance, fun _ _ g hg =>
    le_saturation _ _ (.generator g hg), fun ε _ _ i hi => ?_, fun i _ hi => ?_⟩
  · have := markedExactCylinder.isSaturated_endpointBox_preimage ε
      (saturation.{u} (fibrancyGenerators J))
    refine saturation_le.{u} _ (NatTrans.leibnizPreimage (markedExactCylinder.endpoint ε)
      (saturation.{u} (fibrancyGenerators J))) ?_ i
        ((congrArg (fun P : MorphismProperty MarkedDiagSet.{u} => P i) hmono).mp hi)
    rintro _ _ g (⟨K, Y, t, ht, e⟩ | ⟨a, h⟩)
    · cases ht with
      | mk U =>
        exact ((NatTrans.leibnizPreimage (markedExactCylinder.endpoint ε)
          (saturation.{u} (fibrancyGenerators J))).arrow_mk_iso_iff
            ((eqToIso e).symm ≪≫ flatSphereInclusionArrowIso U)).2
              (le_saturation _ _ (.sphere ε U))
    · exact ((NatTrans.leibnizPreimage (markedExactCylinder.endpoint ε)
        (saturation.{u} (fibrancyGenerators J))).arrow_mk_iso_iff
          (markingMapArrowIso a h)).2 (le_saturation _ _ (.marking ε a h))
  · have := markedExactCylinder.isSaturated_bothBox_preimage
      (saturation.{u} (fibrancyGenerators J))
    exact saturation_le.{u} (fibrancyGenerators J)
      (NatTrans.leibnizPreimage markedExactCylinder.endpointsNatTrans
        (saturation.{u} (fibrancyGenerators J)))
      (fun _ _ g hg => le_saturation _ _ (.bothBox g hg)) i hi

theorem isFibrant_markedExactCylinder (J : MorphismProperty MarkedDiagSet.{u})
    (hJ : ∀ {A B : MarkedDiagSet.{u}} (g : A ⟶ B), J g →
      markedHorns g ∨ IsIso (MarkedPresheaf.forget.map g))
    {X : MarkedDiagSet.{u}} (hX : HasMarkedRLP J X) (hH : HasMarkedRLP markedHorns X)
    (hI : HasMarkedRLP invertorGenerators X) :
    markedExactCylinder.{u}.IsFibrant J X := by
  let P : MorphismProperty MarkedDiagSet.{u} :=
    (MorphismProperty.ofHoms fun _ : Unit => terminal.from X).llp
  have hgen : fibrancyGenerators J ≤ P := fun _ _ g hg _ _ f hf => by
    cases hf
    exact (hornLike_or_lifting_of_fibrancyGenerators hJ hX hH hI g hg).elim
      (fun h => h.hasLiftingProperty hH) fun h => h.2
  intro _ _ f hf
  exact saturation_le.{u} _ P hgen f (anodyne_le_saturation_fibrancyGenerators J f hf) _
    (MorphismProperty.ofHoms.mk ())

theorem markedHorns_or_isIso_of_coinductiveGenerators (n : ℕ∞) {A B : MarkedDiagSet.{u}}
    (g : A ⟶ B) (hg : coinductiveGenerators n g) :
    markedHorns g ∨ IsIso (MarkedPresheaf.forget.map g) := by
  rcases hg with (hh | h) | h
  · exact Or.inl hh
  all_goals cases h; exact Or.inr (inferInstanceAs (CategoryTheory.IsIso (𝟙 _)))

theorem markedHorns_or_isIso_of_inductiveGenerators (n : ℕ∞) {A B : MarkedDiagSet.{u}}
    (g : A ⟶ B) (hg : inductiveGenerators n g) :
    markedHorns g ∨ IsIso (MarkedPresheaf.forget.map g) := by
  rcases hg with (hh | h) | h
  · exact Or.inl hh
  all_goals cases h; exact Or.inr (inferInstanceAs (CategoryTheory.IsIso (𝟙 _)))

theorem isFibrant_coinductive_iff_isFibrant (n : ℕ∞) (X : MarkedDiagSet.Coinductive.{u} n) :
    IsFibrant X ↔
      markedExactCylinder.{u}.IsFibrant (coinductiveGenerators n) X :=
  (HomotopicalAlgebra.fibration_iff _).trans
    (markedExactCylinder.rlp_trivialCofibrations_terminal_from_iff _
      (coinductiveGenerators_le_monomorphisms n) X)

theorem isFibrant_inductive_iff_isFibrant (n : ℕ∞) (X : MarkedDiagSet.Inductive.{u} n) :
    IsFibrant X ↔
      markedExactCylinder.{u}.IsFibrant (inductiveGenerators n) X :=
  (HomotopicalAlgebra.fibration_iff _).trans
    (markedExactCylinder.rlp_trivialCofibrations_terminal_from_iff _
      (inductiveGenerators_le_monomorphisms n) X)

theorem isFibrant_coinductive_iff (n : ℕ∞) (X : MarkedDiagSet.Coinductive.{u} n) :
    IsFibrant X ↔
      HasMarkedRLP (coinductiveGenerators n) X := by
  refine (isFibrant_coinductive_iff_isFibrant n X).trans ⟨fun h _ _ f hf =>
    h f (markedExactCylinder.le_anodyne _ _ hf), fun h => ?_⟩
  obtain ⟨-, hM⟩ := (hasMarkedRLP_coinductiveGenerators_iff n X).1 h
  exact isFibrant_markedExactCylinder _ (markedHorns_or_isIso_of_coinductiveGenerators n) h
    ((hasMarkedRLP_sup _ _ _).1 ((hasMarkedRLP_sup _ _ _).1 h).1).1
    (hasMarkedRLP_of_natural hM (hasMarkedRLP_invertorGenerators_natural X.underlying))

theorem isFibrant_inductive_iff (n : ℕ∞) (X : MarkedDiagSet.Inductive.{u} n) :
    IsFibrant X ↔ HasMarkedRLP (inductiveGenerators n) X := by
  refine (isFibrant_inductive_iff_isFibrant n X).trans ⟨fun h _ _ f hf =>
    h f (markedExactCylinder.le_anodyne _ _ hf), fun h => ?_⟩
  exact isFibrant_markedExactCylinder _ (markedHorns_or_isIso_of_inductiveGenerators n) h
    ((hasMarkedRLP_sup _ _ _).1 ((hasMarkedRLP_sup _ _ _).1 h).1).1
    ((hasMarkedRLP_sup _ _ _).1 h).2

theorem isFibrant_coinductive_iff_natural (n : ℕ∞) (X : MarkedDiagSet.Coinductive.{u} n) :
    IsFibrant X ↔ IsInftyCategory n X.underlying ∧
      ∀ (U : Atom) (x : diagram X.underlying U), x ∈ X.marked U ↔ IsEquivalence X.underlying x :=
  (isFibrant_coinductive_iff n X).trans (hasMarkedRLP_coinductiveGenerators_iff n X)

theorem isFibrant_inductive_iff_natural (n : ℕ) (X : MarkedDiagSet.Inductive.{u} n) :
    IsFibrant X ↔ IsInftyCategory n X.underlying ∧
      ∀ (U : Atom) (x : diagram X.underlying U), x ∈ X.marked U ↔ IsEquivalence X.underlying x :=
  (isFibrant_inductive_iff (n : ℕ∞) X).trans (hasMarkedRLP_inductiveGenerators_iff n X)

theorem isFibrant_coinductive_natural (n : ℕ∞) {X : DiagSet.{u}} (hX : IsInftyCategory n X) :
    IsFibrant ((MarkedDiagSet.toCoinductive n).obj (MarkedDiagSet.natural.obj X)) :=
  (isFibrant_coinductive_iff n _).2 (hasMarkedRLP_coinductiveGenerators_natural n hX)

theorem isFibrant_inductive_natural (n : ℕ∞) {X : DiagSet.{u}} (hX : IsInftyCategory n X) :
    IsFibrant ((MarkedDiagSet.toInductive n).obj (MarkedDiagSet.natural.obj X)) :=
  (isFibrant_inductive_iff n _).2 (hasMarkedRLP_inductiveGenerators_natural n hX)

end Atoms.Diagrammatic
