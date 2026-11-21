import Atoms.Diagrammatic.Marked.HornMaps
import Atoms.Shape.Invertor

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

theorem exists_fills_of_hasLiftingProperty {X : MarkedDiagSet.{u}} (m : MarkedHornData)
    (hm : HasLiftingProperty (markedHornInclusion m) (terminal.from X))
    (w : realize.obj m.hornRDC ⟶ X.underlying) (hw : m.MarksHorn X w) : ∃ z, m.Fills X w z := by
  let Φ := closedSubpresheafRealizeIso m.atom m.hornSet
  let q : m.source ⟶ X := Homotopical.MarkedPresheaf.homMk (Φ.inv ≫ w) fun V y hy => by
    rcases (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy with
      hy | ⟨a, ha, him, hd⟩
    · exact X.mem_marked_of_isDegenerate (isDegenerate_app _ hy)
    · obtain ⟨e, he⟩ := exists_iso_comp_closureIncl y.1.down (Atom.map_top_eq_Iic_iff.1 him) hd
      have hy' : Φ.inv.app (op V) y = (realize.obj m.hornRDC).map e.hom.op
          ⟨principalInclusionIn m.atom m.hornSet (m.marking_mem a ha).1⟩ := by
        have h1 := NatTrans.naturality_apply Φ.hom e.hom.op
          ⟨principalInclusionIn m.atom m.hornSet (m.marking_mem a ha).1⟩
        have h2 : (closedSubpresheaf m.atom m.hornSet).toFunctor.map e.hom.op
            (Φ.hom.app _ ⟨principalInclusionIn m.atom m.hornSet (m.marking_mem a ha).1⟩) = y :=
          Subtype.ext (congrArg ULift.up he)
        rw [← h2, ← h1, Iso.hom_inv_id_app_apply]
      change w.app (op V) (Φ.inv.app (op V) y) ∈ X.marked V
      rw [hy']
      exact (congrArg (· ∈ X.marked V) (NatTrans.naturality_apply w e.hom.op _)).mpr
        ((X.transport e _).1 (hw a ha))
  have sq : CommSq q (markedHornInclusion m) (terminal.from X) (terminal.from _) :=
    ⟨terminal.hom_ext _ _⟩
  let f := sq.lift
  have hf : markedHornInclusion m ≫ f = q := sq.fac_left
  let F := Homotopical.MarkedPresheaf.forget.map f
  let z : diagram X.underlying m.atom :=
    F.app (op m.atom) ⟨⟨𝟙 m.atom⟩, fun _ => LowerSet.mem_top⟩
  have hfz : ∀ {T : Atom} (g : T ⟶ m.atom) (hg : ∀ t, g t ∈ (⊤ : LowerSet m.atom.ogp)),
      F.app (op T) ⟨⟨g⟩, hg⟩ = X.underlying.map g.op z := by
    intro T g hg
    exact (congrArg (F.app (op T))
      (Subtype.ext (congrArg ULift.up (Category.comp_id g).symm))).trans
      (NatTrans.naturality_apply F g.op
        (⟨⟨𝟙 m.atom⟩, fun _ => LowerSet.mem_top⟩ : m.target.underlying.obj (op m.atom)))
  refine ⟨z, ?_, ?_, fun hsub => ?_⟩
  · ext ⟨T⟩ ⟨c⟩
    have e := congrArg (fun φ : m.source ⟶ X =>
      (Homotopical.MarkedPresheaf.forget.map φ).app (op T) (Φ.hom.app (op T) ⟨c⟩)) hf
    exact (hfz (Atom.fullyFaithful.preimage (c ≫ m.hornIncl))
      (fun _ => LowerSet.mem_top)).symm.trans e
  · exact Homotopical.MarkedPresheaf.map_mem_marked f
      ((Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
        (Or.inr ⟨m.atom.top, m.mem_targetMarking_iff.2 (Or.inl rfl), Atom.map_top _,
          m.atom.dimension_eq⟩))
  · exact (congrArg (· ∈ X.marked _) (hfz _ (fun _ => LowerSet.mem_top))).mp
      (Homotopical.MarkedPresheaf.map_mem_marked f
        ((Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
          (Or.inr ⟨m.face, m.mem_targetMarking_iff.2 (Or.inr (Or.inl ⟨hsub, rfl⟩)),
            Atom.map_closureInclOGP_top m.atom m.face, Atom.dimension_ofClosure m.atom m.face⟩)))

section InvertorFiller

variable {V : Atom} (ε : Bool) (hV : 0 < V.dimension)

def invertorHornMap {Y : DiagSet.{u}} (e : diagram Y V) :
    realize.obj (invertorMarkedHorn V ε hV).hornRDC ⟶ Y :=
  realize.map (invertorHornProj V ε hV) ≫ (ofCell e).map

theorem marksHorn_invertorHornMap {X : MarkedDiagSet.{u}} (e : diagram X.underlying V)
    (he : e ∈ X.marked V) : (invertorMarkedHorn V ε hV).MarksHorn X (invertorHornMap ε hV e) := by
  intro a ha
  obtain rfl := Set.mem_singleton_iff.1 ha
  let c := principalInclusionIn (invertorAtom V ε hV) (invertorMarkedHorn V ε hV).hornSet
    (invertorTopElt_some_bnot_mem_hornSet V ε hV)
  let g : Atom.ofClosure (invertorAtom V ε hV) (invertorTopElt V ε hV (some (!ε))) ⟶ V :=
    Atom.fullyFaithful.preimage (c ≫ invertorHornProj V ε hV)
  have hcol : IsCollapseHom g := by
    intro v
    have hv : invertorEndpointNot V.toMoleculeShape ε hV v ∈ Set.range
        (Atom.closureIncl (invertorAtom V ε hV) (invertorTopElt V ε hV (some (!ε)))) := by
      rw [Atom.range_closureIncl]
      change invertorEndpointNot V.toMoleculeShape ε hV v ≤ invertorTopElt V ε hV (some (!ε))
      rw [← invertorEndpointNot_top ε hV]
      exact (isMorphism (invertorEndpointNot V.toMoleculeShape ε hV)).monotone (V.le_top v)
    obtain ⟨p, hp⟩ := hv
    refine ⟨p, ?_⟩
    change partialCylinderProj V.ogp (V.ogp.bdry ⊤ ε) ((invertorAtomIso V ε hV).inv
      (Atom.closureIncl (invertorAtom V ε hV) (invertorTopElt V ε hV (some (!ε))) p)) = v
    rw [hp]
    exact proj_invertorShapeIso_symm_invertorEndpointNot V.toMoleculeShape ε hV v
  have hdim :
      (Atom.ofClosure (invertorAtom V ε hV) (invertorTopElt V ε hV (some (!ε)))).dimension =
      V.dimension := by
    rw [Atom.dimension_ofClosure, dim_invertorTopElt_some]
  have := isIso_of_isCollapseHom_of_dimension_eq g hcol hdim
  have hval : (invertorHornMap ε hV e).app (op _) ⟨c⟩ = X.underlying.map g.op e :=
    (realize_map_comp_app (invertorHornProj V ε hV) (ofCell e).map c).trans
      (ofCell_map_app_map e g)
  exact (congrArg (· ∈ X.marked _) hval).mpr ((X.transport (asIso g) e).1 he)

theorem invertorFiller_restrict {Y : DiagSet.{u}} {e : diagram Y V}
    {z : diagram Y (invertorAtom V ε hV)}
    (hz : realize.map (invertorMarkedHorn V ε hV).hornIncl ≫ (ofCell z).map =
      invertorHornMap ε hV e)
    {A : MoleculeShape} (g : A.ogp ⟶ (invertorShape V.toMoleculeShape ε hV).ogp) [IsInclusion g]
    (hg : ∀ a, g a ∈ (invertorMarkedHorn V ε hV).hornSet) :
    realize.map (RDCpx.ofInclusion (P := A.rdc) (Q := (invertorShape V.toMoleculeShape ε hV).rdc)
        g) ≫ (ofCell z).map =
      realize.map (@RDCpx.ofInclusion A.rdc (invertorMarkedHorn V ε hV).hornRDC
        (codRestrict g (invertorMarkedHorn V ε hV).hornSet hg)
        ⟨fun _ _ h => IsInclusion.injective (f := g) (congrArg Subtype.val h)⟩ ≫
        invertorHornProj V ε hV) ≫ (ofCell e).map := by
  have hcomp : @RDCpx.ofInclusion A.rdc (invertorMarkedHorn V ε hV).hornRDC
      (codRestrict g (invertorMarkedHorn V ε hV).hornSet hg)
      ⟨fun _ _ h => IsInclusion.injective (f := g) (congrArg Subtype.val h)⟩ ≫
        (invertorMarkedHorn V ε hV).hornIncl =
      RDCpx.ofInclusion (P := A.rdc) (Q := (invertorShape V.toMoleculeShape ε hV).rdc) g := by
    ext x
    rfl
  exact (congrArg (fun t => realize.map t ≫ (ofCell z).map) hcomp.symm).trans
    ((realize.map_comp_assoc _ _ _).trans
      ((congrArg (realize.map _ ≫ ·) hz).trans (realize.map_comp_assoc _ _ _).symm))

end InvertorFiller

section BiInv

variable {Y : DiagSet.{u}} {V : Atom}

theorem equiv_ofCell_map_closureIncl_invertorDual (ε : Bool) (hV : 0 < V.dimension)
    (z : diagram Y (invertorAtom V ε hV)) :
    (ofCell (Y.map (Atom.closureIncl (invertorAtom V ε hV) (invertorTopElt V ε hV (some ε))).op
      z)).Equiv (invertorDual V.toMoleculeShape ε hV (ofCell z).map) := by
  have : @IsInclusion (ofCell (Y.map (Atom.closureIncl (invertorAtom V ε hV)
      (invertorTopElt V ε hV (some ε))).op z)).shape.ogp (invertorShape V.toMoleculeShape ε hV).ogp
      (Atom.closureInclOGP _ (invertorTopElt V ε hV (some ε))) :=
    inferInstanceAs (IsInclusion (Atom.closureInclOGP _ (invertorTopElt V ε hV (some ε))))
  have : @IsInclusion (invertorDual V.toMoleculeShape ε hV (ofCell z).map).shape.ogp
      (invertorShape V.toMoleculeShape ε hV).ogp (invertorEndpointDual V.toMoleculeShape ε hV) :=
    inferInstanceAs (IsInclusion (invertorEndpointDual V.toMoleculeShape ε hV))
  have hι : RDCpx.ofInclusion (P := (ofCell (Y.map (Atom.closureIncl (invertorAtom V ε hV)
      (invertorTopElt V ε hV (some ε))).op z)).shape.rdc)
      (Q := (invertorShape V.toMoleculeShape ε hV).rdc)
      (Atom.closureInclOGP _ (invertorTopElt V ε hV (some ε))) =
      atomToRDCpx.map (Atom.closureIncl _ _) := by
    ext
    rfl
  refine equiv_of_emb_of_image_eq (C := (invertorShape V.toMoleculeShape ε hV).rdc) (ofCell z).map
    (Atom.closureInclOGP _ (invertorTopElt V ε hV (some ε)))
    (invertorEndpointDual V.toMoleculeShape ε hV)
    ((congrArg (fun t => realize.map t ≫ (ofCell z).map) hι).trans (ofCell_map_op_map _ z).symm)
    rfl ?_
  exact (Atom.map_closureInclOGP_top _ _).trans ((closure_invertorTopElt V ε hV ε).trans
    (image_invertorEndpointDual V.toMoleculeShape ε hV).symm)

theorem exists_biInvData_of_invertors (hV : 0 < V.dimension) (e : diagram Y V)
    (z : ∀ α, diagram Y (invertorAtom V (!α) hV))
    (hz : ∀ α, realize.map (invertorMarkedHorn V (!α) hV).hornIncl ≫ (ofCell (z α)).map =
      invertorHornMap (!α) hV e) :
    ∃ d : BiInvData Set.univ (cellRound e), ∀ α,
      (ofCell (Y.map (Atom.closureIncl (invertorAtom V (!α) hV)
        (invertorTopElt V (!α) hV (some (!α)))).op (z α))).Equiv
          (d.inverse α).toPastingDiagram ∧
      (ofCell (z α)).Equiv (d.invertor α).toPastingDiagram := by
  have hr : V.toMoleculeShape.IsRound := V.isAtom.isRound
  have hn : V.dimension - 1 < V.dimension := by omega
  have h₁ (α : Bool) : realize.map (RDCpx.ofInclusion (P := V.toMoleculeShape.rdc)
      (Q := (invertorShape V.toMoleculeShape (!α) hV).rdc)
      (invertorEndpointNot V.toMoleculeShape (!α) hV)) ≫ (ofCell (z α)).map = (ofCell e).map :=
    (invertorFiller_restrict (!α) hV (hz α) _ (invertorEndpointNot_mem_horn (!α) hV)).trans
      ((congrArg (fun t => realize.map t ≫ (ofCell e).map)
        (invertorEndpointNot_comp_proj (!α) hV)).trans
        ((congrArg (· ≫ (ofCell e).map) (realize.map_id _)).trans (Category.id_comp _)))
  have h₂ (α : Bool) := (invertorFiller_restrict (!α) hV (hz α) _
    (invertorUnitEmb_mem_horn (!α) hV hr)).trans
      ((congrArg (fun t => realize.map t ≫ (ofCell e).map)
        (invertorUnitEmb_comp_proj (!α) hV hr)).trans (realize.map_comp_assoc _ _ _))
  let eα (α : Bool) := invertorDual V.toMoleculeShape (!α) hV (ofCell (z α)).map
  have (α : Bool) : @IsInclusion (eα α).shape.ogp (invertorShape V.toMoleculeShape (!α) hV).ogp
      (invertorEndpointDual V.toMoleculeShape (!α) hV) :=
    inferInstanceAs (IsInclusion (invertorEndpointDual V.toMoleculeShape (!α) hV))
  have hdim (α : Bool) : (eα α).dim = V.dimension := MoleculeShape.dimension_dual _ _
  have hmeet (α : Bool) : ((eα α).boundary (V.dimension - 1) α).Equiv
      ((ofCell e).boundary (V.dimension - 1) (!α)) := by
    have h := equiv_invertor_boundary_meet V.toMoleculeShape (!α) hV (ofCell (z α)).map (ofCell e)
      (eα α) (invertorEndpointNot V.toMoleculeShape (!α) hV)
      (invertorEndpointDual V.toMoleculeShape (!α) hV) (h₁ α) rfl
      (image_invertorEndpointNot V.toMoleculeShape (!α) hV)
      (image_invertorEndpointDual V.toMoleculeShape (!α) hV)
    simpa only [Bool.not_not] using h.symm
  have hpst (α : Bool) : (cond α (eα α) (ofCell e)).Pastable (cond α (ofCell e) (eα α))
      (V.dimension - 1) :=
    Pastable.of_side α (hmeet α) ((hdim α).symm ▸ hn) hn
  have hcomp (α : Bool) : ((ofCell (z α)).boundary V.dimension α).Equiv
      ((cond α (eα α) (ofCell e)).paste (cond α (ofCell e) (eα α)) (V.dimension - 1)
        (hpst α)) := by
    have h : ((ofCell (z α)).boundary V.dimension (!!α)).Equiv _ :=
      equiv_invertor_boundary_not_eps V.toMoleculeShape (!α) hV (ofCell (z α)).map
        (ofCell e) (eα α) (invertorEndpointNot V.toMoleculeShape (!α) hV)
        (invertorEndpointDual V.toMoleculeShape (!α) hV) (h₁ α) rfl
        (image_invertorEndpointNot V.toMoleculeShape (!α) hV)
        (image_invertorEndpointDual V.toMoleculeShape (!α) hV)
        (by simpa only [Bool.cond_not] using hpst α)
    simpa only [Bool.not_not, Bool.cond_not] using h
  have hunit (α : Bool) : ((ofCell (z α)).boundary V.dimension (!α)).Equiv
      ((ofCell e).boundary (V.dimension - 1) α).unit := by
    have h : ((ofCell (z α)).boundary V.dimension (!α)).Equiv
        ((ofCell e).boundary (V.dimension - 1) (!!α)).unit :=
      equiv_invertor_boundary_eps V.toMoleculeShape (!α) hV hr (ofCell (z α)).map (ofCell e).map
        (h₂ α)
    simpa only [Bool.not_not] using h
  have hother (α : Bool) : ((eα α).boundary (V.dimension - 1) (!α)).Equiv
      ((ofCell e).boundary (V.dimension - 1) α) := by
    have hc : cond (!α) (cond α (ofCell e) (eα α)) (cond α (eα α) (ofCell e)) = eα α := by
      cases α <;> rfl
    have h := equiv_boundary_paste (hpst α) (!α)
    rw [hc] at h
    exact h.symm.trans (((hcomp α).boundary _ (!α)).symm.trans
      ((equiv_boundary_boundary _ hn α (!α)).trans
        ((equiv_boundary_boundary _ hn (!α) (!α)).symm.trans
          (((hunit α).boundary _ (!α)).trans
            (boundary_unit (dim_boundary _ (Nat.sub_le _ 1) α) (!α))))))
  refine ⟨{ dim_pos := hV
            inverse := fun α => ⟨eα α, MoleculeShape.isRound_dual hr _⟩
            invertor := fun α => cellRound (z α)
            invertor_mem := fun _ => Set.mem_univ _
            dim_inverse := hdim
            dim_invertor := fun α => dimension_invertorAtom V (!α) hV
            equiv_boundary_inverse := fun α γ => ?_
            pastable := hpst
            boundary_invertor_composite := hcomp
            boundary_invertor_unit := hunit },
    fun α => ⟨equiv_ofCell_map_closureIncl_invertorDual (!α) hV (z α), .refl _⟩⟩
  obtain rfl | rfl := Bool.eq_or_eq_not γ α
  · exact hmeet γ
  · rw [Bool.not_not]
    exact hother α

end BiInv

section Lemma41

variable {X' : MarkedDiagSet.{u}}

def markedRound (X' : MarkedDiagSet.{u}) : Set (RoundPastingDiagram X'.underlying) :=
  {d | ∃ (U : Atom) (x : diagram X'.underlying U), x ∈ X'.marked U ∧ (ofCell x).Equiv d.1}

theorem cellRound_mem_markedRound {U : Atom} {x : diagram X'.underlying U}
    (hx : x ∈ X'.marked U) : cellRound x ∈ markedRound X' :=
  ⟨U, x, hx, .refl _⟩

theorem biInvWitness_of_marked
    (hX : ∀ (V : Atom) (ε : Bool) (hV : 0 < V.dimension),
      HasLiftingProperty (markedHornInclusion (invertorMarkedHorn V ε hV)) (terminal.from X'))
    {V : Atom} {e : diagram X'.underlying V} (he : e ∈ X'.marked V) :
    BiInvWitness (markedRound X') (cellRound e) := by
  have hV : 0 < V.dimension := X'.markable V e he
  choose z hz hzm using fun α => exists_fills_of_hasLiftingProperty
    (invertorMarkedHorn V (!α) hV) (hX V (!α) hV) (invertorHornMap (!α) hV e)
    (marksHorn_invertorHornMap (!α) hV e he)
  obtain ⟨d, hd⟩ := exists_biInvData_of_invertors hV e z hz
  exact BiInvData.witness { d with invertor_mem := fun α => ⟨_, z α, (hzm α).1, (hd α).2⟩ }

theorem isEquivalence_of_mem_marked (X : MarkedDiagSet.{u})
    (hX : ∀ (V : Atom) (ε : Bool) (hV : 0 < V.dimension),
      HasLiftingProperty (markedHornInclusion (invertorMarkedHorn V ε hV)) (terminal.from X))
    (U : Atom) (x : diagram X.underlying U) (hx : x ∈ X.marked U) :
    IsEquivalence X.underlying x :=
  subset_equivalences (A := markedRound X)
    (fun _ ⟨_, _, hy, hd⟩ => BiInvWitness.of_equiv hd (biInvWitness_of_marked hX hy))
    (cellRound_mem_markedRound hx)

theorem marked_subset_equivalences (X : MarkedDiagSet.{u})
    (hX : HasMarkedRLP markedHorns X) (U : Atom) (x : diagram X.underlying U)
    (hx : x ∈ X.marked U) : IsEquivalence X.underlying x :=
  isEquivalence_of_mem_marked X (fun _ _ _ => hX _ (MorphismProperty.ofHoms.mk _)) U x hx

end Lemma41

end Atoms.Diagrammatic
