import Atoms.Diagrammatic.Localization.Loc
import Atoms.Diagrammatic.Marked.Invertible

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Opposite Order
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

section AttachedInvertor

open Atoms.Molecule Atoms.Molecule.OGP Atoms.Diagrammatic.PastingDiagram

variable {X : DiagSet.{u}}

theorem apply_eq_of_isPastingIn_of_isPastingIn {L S U₁ U₂ : OGP.{0}} {k : ℕ}
    (hU₁ : IsMolecule U₁) (θ : L ⟶ S) [IsInclusion θ] {BL : LowerSet L} {BS : LowerSet S}
    (hBL : IsMoleculeIn L BL) (a₁ : U₁ ⟶ L) (a₂ : U₂ ⟶ L) (b₁ : U₁ ⟶ S) (b₂ : U₂ ⟶ S)
    [IsInclusion a₁] [IsInclusion a₂] [IsInclusion b₁] [IsInclusion b₂]
    (hpL : L.IsPastingIn k (map a₁ ⊤) (map a₂ ⊤) BL)
    (hpS : S.IsPastingIn k (map b₁ ⊤) (map b₂ ⊤) BS) (hθ : map θ BL = BS) :
    (∀ x, θ (a₁ x) = b₁ x) ∧ ∀ y, θ (a₂ y) = b₂ y := by
  have hpL' : S.IsPastingIn k (map (a₁ ≫ θ) ⊤) (map (a₂ ≫ θ) ⊤) BS := by
    rw [map_comp, map_comp, ← hθ]
    exact (isPastingIn_map_iff θ k _ _ _).2 hpL
  have hBS : IsMolecule (S.restrict BS) :=
    (isMolecule_restrict_iff BS).2 (hθ ▸ (isMoleculeIn_map_iff θ BL).2 hBL)
  let i := codRestrict (a₁ ≫ θ) BS fun x => hpL'.left_le ⟨x, LowerSet.mem_top, rfl⟩
  let j := codRestrict (a₂ ≫ θ) BS fun y => hpL'.right_le ⟨y, LowerSet.mem_top, rfl⟩
  let i' := codRestrict b₁ BS fun x => hpS.left_le ⟨x, LowerSet.mem_top, rfl⟩
  let j' := codRestrict b₂ BS fun y => hpS.right_le ⟨y, LowerSet.mem_top, rfl⟩
  have hp₀ : (S.restrict BS).IsPastingIn k (map i ⊤) (map j ⊤) ⊤ := by
    rw [← isPastingIn_map_iff (incl BS), ← map_comp, ← map_comp, codRestrict_incl,
      codRestrict_incl, map_incl_top]
    exact hpL'
  have hp' : (S.restrict BS).IsPastingIn k (map i' ⊤) (map j' ⊤) ⊤ := by
    rw [← isPastingIn_map_iff (incl BS), ← map_comp, ← map_comp, codRestrict_incl,
      codRestrict_incl, map_incl_top]
    exact hpS
  obtain ⟨Θ, hi, hj, -, -⟩ := exists_iso_of_cover_pair i j i' j' hp₀.sup_eq hp'.sup_eq
    (apply_eq_apply_iff_of_isPastingIn_of_isMolecule hU₁ hp₀ hp')
  have : Subsingleton (S.restrict BS ≅ S.restrict BS) := hBS.subsingleton_iso
  obtain rfl : Θ = Iso.refl _ := Subsingleton.elim _ _
  exact ⟨fun x => congrArg Subtype.val (ConcreteCategory.congr_hom hi x),
    fun y => congrArg Subtype.val (ConcreteCategory.congr_hom hj y)⟩

section InvertorHorn

variable {V : Atom} (ε : Bool)

private theorem std_le_copy_sup_over (hV : 0 < V.dimension) :
    InvertedCylinder.std (V.ogp.bdry ⊤ ε) ε V.dimension ≤
      PartialCylinder.copy (V.ogp.bdry ⊤ ε) (!ε) ⊤ ⊔
        PartialCylinder.over (V.ogp.bdry ⊤ ε) (V.ogp.boundary ⊤ (V.dimension - 1) (!ε)) := by
  have hS : krullDim (⊤ : LowerSet V.ogp) = (V.dimension - 1 : ℕ) + 1 := by
    rw [LowerSet.krullDim_top, V.krullDim_eq_dimension]
    exact_mod_cast (by omega : V.dimension = V.dimension - 1 + 1)
  have hbd : ∀ x : V.ogp, x ∉ V.ogp.bdry ⊤ ε → grade ℕ x < V.dimension →
      x ∈ V.ogp.boundary ⊤ (V.dimension - 1) (!ε) := by
    intro x hx hxd
    have hfull : x ∈ V.ogp.bdryFull ⊤ := (V.mem_bdryFull_top_iff x).2 fun h => by
      rw [h, ← V.dimension_eq] at hxd
      exact lt_irrefl _ hxd
    rw [← bdry_eq_boundary hS]
    rcases LowerSet.mem_sup_iff.1 hfull with h | h <;> cases ε
    · exact absurd h hx
    · exact h
    · exact h
    · exact absurd h hx
  intro a ha
  rw [SetLike.mem_coe, InvertedCylinder.mem_std] at ha
  rw [SetLike.mem_coe]
  refine LowerSet.mem_sup_iff.2 ?_
  rcases a with ⟨x, hx⟩ | ⟨⟨_ | β⟩, ⟨x, hx⟩⟩
  · exact Or.inl ((PartialCylinder.mkK_mem_copy hx).2 LowerSet.mem_top)
  · refine Or.inr (hbd x hx ?_)
    simpa [InvertedCylinder.changed] using ha
  · by_cases hβ : β = !ε
    · subst hβ
      exact Or.inl (PartialCylinder.mem_copy.2
        ⟨LowerSet.mem_top, PartialCylinder.endpoint_of_notMem _ hx⟩)
    · have hβ' : β = ε := (Bool.eq_not.2 hβ).trans (Bool.not_not ε)
      subst hβ'
      refine Or.inr (hbd x hx ?_)
      simpa [InvertedCylinder.changed] using ha

private theorem map_invertorUnitEmb_eq_over (hV : 0 < V.dimension)
    (hr : V.toMoleculeShape.IsRound) :
    map (invertorUnitEmb V.toMoleculeShape ε hV hr) ⊤ =
      map (invertorShapeIso V.toMoleculeShape ε hV).hom
        (PartialCylinder.over (V.ogp.bdry ⊤ ε) (V.ogp.boundary ⊤ (V.dimension - 1) (!ε))) := by
  rw [invertorUnitEmb, map_comp, map_top_of_isIso, map_comp, InvertedCylinder.map_embOfStd,
    PartialCylinder.map_embOfEmb_top, MoleculeShape.map_boundaryIncl_top]

theorem hornSet_invertorAtom_le (hV : 0 < V.dimension) (hr : V.toMoleculeShape.IsRound) :
    (invertorMarkedHorn V ε hV).hornSet ≤
      map (invertorEndpointNot V.toMoleculeShape ε hV) ⊤ ⊔
        map (invertorUnitEmb V.toMoleculeShape ε hV hr) ⊤ := by
  change ((invertorAtom V ε hV).isRewritableSubmolecule_Iic_of_mem_faces
      (invertorTopElt_mem_faceSet V ε hV ε)).hornSet
      (invertorAtom V ε hV).isMolecule (invertorAtom V ε hV).isAtom.isRound ≤ _
  rw [hornSet_invertorAtom, image_invertorEndpointNot, map_invertorUnitEmb_eq_over ε hV hr,
    ← map_sup]
  exact map_mono _ (std_le_copy_sup_over ε hV)

end InvertorHorn

namespace InversionData

variable (A : InversionData X)

theorem nonempty_iso_invertorAtom_next_shape (i : A.ι) (α : Bool)
    (hV : 0 < (A.shape i).dimension) :
    Nonempty (invertorAtom (A.shape i) (!α) hV ≅ A.next.shape (i, α)) := by
  obtain ⟨θ'⟩ := A.nonempty_iso_next_shape (i, α)
  exact ⟨θ'.symm⟩

private theorem exists_withins_apply_iso (i : A.ι) (ε : Bool) (hV : 0 < (A.shape i).dimension)
    (θ : invertorAtom (A.shape i) ε hV ≅ A.next.shape (i, !ε)) :
    ∃ (wu : Within (ofCell (A.stepIncl.app _ (A.cell i))) (ofCell (A.next.cell (i, !ε))))
      (wl : Within (ofCell (A.invertorExtension.incl.app _ (A.inverseExtension.cell (i, !ε))))
        (ofCell (A.next.cell (i, !ε))))
      (w₁ : Within ⟨unitShape ((A.shape i).toMoleculeShape.boundary
          ((A.shape i).dimension - 1) (!ε)),
          realize.map (cylProj ((A.shape i).toMoleculeShape.boundary
              ((A.shape i).dimension - 1) (!ε))
            (((A.shape i).toMoleculeShape.boundary ((A.shape i).dimension - 1) (!ε)).ogp.bdryFull
              ⊤)) ≫
            realize.map ((A.shape i).toMoleculeShape.boundaryInclRDC
              ((A.shape i).dimension - 1) (!ε)) ≫ (ofCell (A.stepIncl.app _ (A.cell i))).map⟩
        (ofCell (A.next.cell (i, !ε))))
      (ψ : (A.inverseExtension.shape (i, !ε)).ogp ≅
        ((A.shape i).toMoleculeShape.dual (OGP.topDim (A.shape i).dimension)).ogp),
      (∀ v, θ.hom (invertorEndpointNot (A.shape i).toMoleculeShape ε hV v) = wu.emb v) ∧
      (∀ y, θ.hom (invertorEndpointDual (A.shape i).toMoleculeShape ε hV (ψ.hom y)) = wl.emb y) ∧
      ∀ y, θ.hom (invertorUnitEmb (A.shape i).toMoleculeShape ε hV (A.shape i).isAtom.isRound y) =
        w₁.emb y := by
  obtain ⟨ψ⟩ := A.nonempty_iso_inverseExtension_shape (i, !ε)
  obtain ⟨wu, wl, w₁, himg₁, hpS⟩ := A.exists_withins_next_cell i (!ε)
  let θ' : (invertorAtom (A.shape i) ε hV).ogp ⟶ (A.next.shape (i, !ε)).ogp :=
    (Atom.isoOGP θ).hom
  have hk : (invertorAtom (A.shape i) ε hV).dimension - 2 = (A.shape i).dimension - 1 := by
    rw [dimension_invertorAtom]
    omega
  have hpL := isPastingIn_closure_invertorTopElt (A.shape i) ε hV
  rw [hk] at hpL
  let a₂ : (A.shape i).ogp ⟶ (invertorAtom (A.shape i) ε hV).ogp :=
    invertorEndpointNot (A.shape i).toMoleculeShape ε hV
  have : IsInclusion a₂ :=
    inferInstanceAs (IsInclusion (invertorEndpointNot (A.shape i).toMoleculeShape ε hV))
  let a₁ : (A.inverseExtension.shape (i, !ε)).ogp ⟶ (invertorAtom (A.shape i) ε hV).ogp :=
    ψ.hom ≫ invertorEndpointDual (A.shape i).toMoleculeShape ε hV
  have : IsInclusion a₁ :=
    inferInstanceAs (IsInclusion (ψ.hom ≫ invertorEndpointDual (A.shape i).toMoleculeShape ε hV))
  have hVc : map a₂ ⊤ = .Iic (invertorTopElt (A.shape i) ε hV (some (!ε))) :=
    (image_invertorEndpointNot _ ε hV).trans (closure_invertorTopElt _ ε hV (!ε)).symm
  have hDc : map a₁ ⊤ = .Iic (invertorTopElt (A.shape i) ε hV (some ε)) :=
    (map_comp ψ.hom _ ⊤).trans ((congrArg (map _) (map_top_of_isIso ψ.hom)).trans
      ((image_invertorEndpointDual _ ε hV).trans (closure_invertorTopElt _ ε hV ε).symm))
  have hθ : map θ' ((invertorAtom (A.shape i) ε hV).ogp.bdry ⊤ (!ε)) =
      (A.next.shape (i, !ε)).ogp.boundary ⊤ (A.shape i).dimension (!ε) := by
    rw [bdry_invertorAtom, map_boundary, map_top_of_isIso]
  have hBL := isMoleculeIn_bdry_invertorAtom (A.shape i) ε hV (!ε)
  rw [← hDc, ← hVc] at hpL
  have hP1 : (∀ v, θ' (a₂ v) = wu.emb v) ∧ ∀ y, θ' (a₁ y) = wl.emb y := by
    cases ε
    · exact (apply_eq_of_isPastingIn_of_isPastingIn (A.inverseExtension.shape (i, true)).isMolecule
        θ' hBL a₁ a₂ wl.emb wu.emb hpL hpS hθ).symm
    · exact apply_eq_of_isPastingIn_of_isPastingIn (A.shape i).isMolecule θ' hBL a₂ a₁ wu.emb wl.emb
        hpL hpS hθ
  have hr : (A.shape i).toMoleculeShape.IsRound := (A.shape i).isAtom.isRound
  rw [Bool.not_not] at himg₁
  let u₁ : (unitShape ((A.shape i).toMoleculeShape.boundary ((A.shape i).dimension - 1)
      (!ε))).ogp ⟶ (invertorAtom (A.shape i) ε hV).ogp :=
    invertorUnitEmb (A.shape i).toMoleculeShape ε hV hr
  have : IsInclusion u₁ :=
    inferInstanceAs (IsInclusion (invertorUnitEmb (A.shape i).toMoleculeShape ε hV hr))
  have hm : map (u₁ ≫ θ') ⊤ = map w₁.emb ⊤ := by
    rw [map_comp, image_invertorUnitEmb_invertorAtom, map_boundary, map_top_of_isIso]
    exact himg₁.symm
  exact ⟨wu, wl, w₁, ψ, hP1.1, hP1.2, fun y => IsMoleculeIn.eqOn_of_map_eq _ _
    (unitShape _).isMolecule hm (LowerSet.mem_top (a := y))⟩

theorem hornIncl_comp_next_cell (i : A.ι) (α : Bool) (hV : 0 < (A.shape i).dimension)
    (θ : invertorAtom (A.shape i) (!α) hV ≅ A.next.shape (i, α)) :
    realize.map (invertorMarkedHorn (A.shape i) (!α) hV).hornIncl ≫
        (ofCell (A.step.map θ.hom.op (A.next.cell (i, α)))).map =
      invertorHornMap (!α) hV (A.stepIncl.app _ (A.cell i)) := by
  generalize hε : (!α) = ε at θ ⊢
  obtain rfl : α = !ε := by rw [← hε, Bool.not_not]
  obtain ⟨wu, -, w₁, -, hP1, -, hP2⟩ := A.exists_withins_apply_iso i ε hV θ
  have hr : (A.shape i).toMoleculeShape.IsRound := (A.shape i).isAtom.isRound
  let i₀ : (A.shape i).rdc.obj.toOGP ⟶ (invertorMarkedHorn (A.shape i) ε hV).hornRDC.obj.toOGP :=
    codRestrict (invertorEndpointNot (A.shape i).toMoleculeShape ε hV) _
      (invertorEndpointNot_mem_horn ε hV)
  have : IsInclusion i₀ := ⟨fun _ _ h => IsInclusion.injective
    (f := invertorEndpointNot (A.shape i).toMoleculeShape ε hV) (congrArg Subtype.val h)⟩
  let j₀ : (unitShape ((A.shape i).toMoleculeShape.boundary
        ((A.shape i).dimension - 1) (!ε))).rdc.obj.toOGP ⟶
      (invertorMarkedHorn (A.shape i) ε hV).hornRDC.obj.toOGP :=
    codRestrict (invertorUnitEmb (A.shape i).toMoleculeShape ε hV hr) _
      (invertorUnitEmb_mem_horn ε hV hr)
  have : IsInclusion j₀ := ⟨fun _ _ h => IsInclusion.injective
    (f := invertorUnitEmb (A.shape i).toMoleculeShape ε hV hr) (congrArg Subtype.val h)⟩
  have hcov : map i₀ ⊤ ⊔ map j₀ ⊤ = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    rcases LowerSet.mem_sup_iff.1 (hornSet_invertorAtom_le ε hV hr w.2) with ⟨v, -, hv⟩ |
      ⟨y, -, hy⟩
    · exact LowerSet.mem_sup_iff.2 (Or.inl ⟨v, LowerSet.mem_top, Subtype.ext hv⟩)
    · exact LowerSet.mem_sup_iff.2 (Or.inr ⟨y, LowerSet.mem_top, Subtype.ext hy⟩)
  have hz : (ofCell (A.step.map θ.hom.op (A.next.cell (i, !ε)))).map =
      realize.map (atomToRDCpx.map θ.hom) ≫ (ofCell (A.next.cell (i, !ε))).map :=
    ofCell_map_op_map θ.hom _
  have hgu : RDCpx.ofInclusion (P := (A.shape i).toMoleculeShape.rdc)
      (Q := (invertorShape (A.shape i).toMoleculeShape ε hV).rdc)
      (invertorEndpointNot (A.shape i).toMoleculeShape ε hV) ≫ atomToRDCpx.map θ.hom =
      RDCpx.ofInclusion (P := (A.shape i).toMoleculeShape.rdc)
        (Q := (A.next.shape (i, !ε)).toMoleculeShape.rdc) wu.emb := by
    ext v
    exact hP1 v
  have hg₁ : RDCpx.ofInclusion (P := (unitShape ((A.shape i).toMoleculeShape.boundary
        ((A.shape i).dimension - 1) (!ε))).rdc)
      (Q := (invertorShape (A.shape i).toMoleculeShape ε hV).rdc)
      (invertorUnitEmb (A.shape i).toMoleculeShape ε hV hr) ≫ atomToRDCpx.map θ.hom =
      RDCpx.ofInclusion (P := (unitShape ((A.shape i).toMoleculeShape.boundary
        ((A.shape i).dimension - 1) (!ε))).rdc)
        (Q := (A.next.shape (i, !ε)).toMoleculeShape.rdc) w₁.emb := by
    ext y
    exact hP2 y
  refine hom_ext_cover i₀ j₀ hcov ?_ ?_
  · have e₁ : RDCpx.ofInclusion i₀ ≫ (invertorMarkedHorn (A.shape i) ε hV).hornIncl =
        RDCpx.ofInclusion (P := (A.shape i).toMoleculeShape.rdc)
          (Q := (invertorShape (A.shape i).toMoleculeShape ε hV).rdc)
          (invertorEndpointNot (A.shape i).toMoleculeShape ε hV) := by
      ext
      rfl
    refine (realize.map_comp_assoc _ _ _).symm.trans ?_
    refine (congrArg (fun t => realize.map t ≫
      (ofCell (A.step.map θ.hom.op (A.next.cell (i, !ε)))).map) e₁).trans ?_
    refine (congrArg (realize.map _ ≫ ·) hz).trans ?_
    refine (realize.map_comp_assoc _ _ _).symm.trans ?_
    refine (congrArg (fun t => realize.map t ≫ (ofCell (A.next.cell (i, !ε))).map) hgu).trans ?_
    refine wu.comm.trans (Eq.trans ?_ (realize.map_comp_assoc _ _ _))
    exact Eq.symm ((congrArg (fun t => realize.map t ≫
      (ofCell (A.stepIncl.app _ (A.cell i))).map)
        (invertorEndpointNot_comp_proj (V := A.shape i) ε hV)).trans
          ((congrArg (· ≫ _) (realize.map_id _)).trans (Category.id_comp _)))
  · have e₁ : RDCpx.ofInclusion j₀ ≫ (invertorMarkedHorn (A.shape i) ε hV).hornIncl =
        RDCpx.ofInclusion (P := (unitShape ((A.shape i).toMoleculeShape.boundary
          ((A.shape i).dimension - 1) (!ε))).rdc)
          (Q := (invertorShape (A.shape i).toMoleculeShape ε hV).rdc)
          (invertorUnitEmb (A.shape i).toMoleculeShape ε hV hr) := by
      ext
      rfl
    refine (realize.map_comp_assoc _ _ _).symm.trans ?_
    refine (congrArg (fun t => realize.map t ≫
      (ofCell (A.step.map θ.hom.op (A.next.cell (i, !ε)))).map) e₁).trans ?_
    refine (congrArg (realize.map _ ≫ ·) hz).trans ?_
    refine (realize.map_comp_assoc _ _ _).symm.trans ?_
    refine (congrArg (fun t => realize.map t ≫ (ofCell (A.next.cell (i, !ε))).map) hg₁).trans ?_
    refine w₁.comm.trans (Eq.trans ?_ (realize.map_comp_assoc _ _ _))
    exact Eq.symm ((congrArg (fun t => realize.map t ≫
      (ofCell (A.stepIncl.app _ (A.cell i))).map)
        (invertorUnitEmb_comp_proj (V := A.shape i) ε hV hr)).trans (realize.map_comp_assoc _ _ _))

theorem nonempty_iso_inverseExtension_shape_ofClosure (i : A.ι) (α : Bool)
    (hV : 0 < (A.shape i).dimension) :
    Nonempty (A.inverseExtension.shape (i, α) ≅ Atom.ofClosure (invertorAtom (A.shape i) (!α) hV)
      (invertorTopElt (A.shape i) (!α) hV (some (!α)))) := by
  obtain ⟨ψ⟩ := A.nonempty_iso_inverseExtension_shape (i, α)
  have h : map (invertorEndpointDual (A.shape i).toMoleculeShape (!α) hV) ⊤ =
      LowerSet.Iic (invertorTopElt (A.shape i) (!α) hV (some (!α))) :=
    (image_invertorEndpointDual _ (!α) hV).trans (closure_invertorTopElt _ (!α) hV (!α)).symm
  exact ⟨Atom.isoOfOGPIso (ψ ≪≫ isoRestrictOfFintype _ h ≪≫ Atom.closureIso _ _)⟩

theorem map_closureIncl_next_cell (i : A.ι) (α : Bool) (hV : 0 < (A.shape i).dimension)
    (θ : invertorAtom (A.shape i) (!α) hV ≅ A.next.shape (i, α))
    (e : A.inverseExtension.shape (i, α) ≅ Atom.ofClosure (invertorAtom (A.shape i) (!α) hV)
      (invertorTopElt (A.shape i) (!α) hV (some (!α)))) :
    A.step.map e.hom.op (A.step.map (Atom.closureIncl _ _).op
      (A.step.map θ.hom.op (A.next.cell (i, α)))) =
        A.invertorExtension.incl.app _ (A.inverseExtension.cell (i, α)) := by
  generalize hε : (!α) = ε at θ e ⊢
  obtain rfl : α = !ε := by rw [← hε, Bool.not_not]
  obtain ⟨-, wl, -, ψ, -, hP, -⟩ := A.exists_withins_apply_iso i ε hV θ
  let f : (A.inverseExtension.shape (i, !ε)).ogp ⟶ (A.next.shape (i, !ε)).ogp :=
    (Atom.isoOGP e).hom ≫ Atom.closureInclOGP _ _ ≫ (Atom.isoOGP θ).hom
  have hwl : wl.emb = ψ.hom ≫ invertorEndpointDual (A.shape i).toMoleculeShape ε hV ≫
      (Atom.isoOGP θ).hom :=
    ConcreteCategory.hom_ext _ _ fun y => (hP y).symm
  have h₁ : map f ⊤ = map (Atom.isoOGP θ).hom
      (.Iic (invertorTopElt (A.shape i) ε hV (some ε))) :=
    (map_comp _ _ ⊤).trans ((congrArg (map _) (map_top_of_isIso _)).trans
      ((map_comp _ _ ⊤).trans (congrArg (map _) (Atom.map_closureInclOGP_top _ _))))
  have h₂ : map wl.emb ⊤ = map (Atom.isoOGP θ).hom
      (.Iic (invertorTopElt (A.shape i) ε hV (some ε))) :=
    (congrArg (map · ⊤) hwl).trans ((map_comp _ _ ⊤).trans
      ((congrArg (map _) (map_top_of_isIso _)).trans ((map_comp _ _ ⊤).trans
        (congrArg (map _) ((image_invertorEndpointDual _ ε hV).trans
          (closure_invertorTopElt _ ε hV ε).symm)))))
  have hmap : e.hom ≫ Atom.closureIncl _ _ ≫ θ.hom = Atom.ofInclusion wl.emb :=
    Atom.hom_ext fun y => IsMoleculeIn.eqOn_of_map_eq _ _
      (A.inverseExtension.shape (i, !ε)).isMolecule (h₁.trans h₂.symm) (LowerSet.mem_top (a := y))
  have hc : A.step.map (Atom.ofInclusion wl.emb).op (A.next.cell (i, !ε)) =
      A.invertorExtension.incl.app _ (A.inverseExtension.cell (i, !ε)) :=
    ofCell_map_injective ((ofCell_map_op_map _ _).trans wl.comm)
  refine Eq.trans ?_ ((congrArg (fun t => A.step.map t.op (A.next.cell (i, !ε))) hmap).trans hc)
  exact ((Functor.map_comp_apply A.step _ _ _).symm.trans
    (Functor.map_comp_apply A.step _ _ _).symm).trans rfl

end InversionData

end AttachedInvertor

section Localization

open Atoms.Molecule Atoms.Molecule.OGP Atoms.Diagrammatic.PastingDiagram

theorem exists_fills_over_of_hasLiftingProperty (m : MarkedHornData) {E B : MarkedDiagSet.{u}}
    (p : E ⟶ B) [HasLiftingProperty (markedHornInclusion m) p]
    (w : realize.obj m.hornRDC ⟶ E.underlying) (hw : m.MarksHorn E w)
    (zB : diagram B.underlying m.atom) (hzB : m.Fills B (w ≫ MarkedPresheaf.forget.map p) zB) :
    ∃ z, m.Fills E w z ∧ (MarkedPresheaf.forget.map p).app _ z = zB := by
  obtain ⟨hz, hzm, hzf⟩ := hzB
  let Φ := closedSubpresheafRealizeIso m.atom m.hornSet
  let q : m.source ⟶ E := MarkedPresheaf.homMk (Φ.inv ≫ w) fun V y hy => by
    rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy with hy | ⟨a, ha, him, hd⟩
    · exact E.mem_marked_of_isDegenerate (isDegenerate_app _ hy)
    · obtain ⟨e, he⟩ := exists_iso_comp_closureIncl y.1.down (Atom.map_top_eq_Iic_iff.1 him) hd
      have hy' : Φ.inv.app (op V) y = (realize.obj m.hornRDC).map e.hom.op
          ⟨principalInclusionIn m.atom m.hornSet (m.marking_mem a ha).1⟩ := by
        have h1 := NatTrans.naturality_apply Φ.hom e.hom.op
          ⟨principalInclusionIn m.atom m.hornSet (m.marking_mem a ha).1⟩
        have h2 : (closedSubpresheaf m.atom m.hornSet).toFunctor.map e.hom.op
            (Φ.hom.app _ ⟨principalInclusionIn m.atom m.hornSet (m.marking_mem a ha).1⟩) = y :=
          Subtype.ext (congrArg ULift.up he)
        rw [← h2, ← h1, Iso.hom_inv_id_app_apply]
      change w.app (op V) (Φ.inv.app (op V) y) ∈ E.marked V
      rw [hy']
      exact (congrArg (· ∈ E.marked V) (NatTrans.naturality_apply w e.hom.op _)).mpr
        ((E.transport e _).1 (hw a ha))
  have hzi : ∀ {T : Atom} (c : atomToRDCpx.obj T ⟶ m.hornRDC),
      (realize.map m.hornIncl ≫ (ofCell zB).map).app (op T) ⟨c⟩ =
        (w ≫ MarkedPresheaf.forget.map p).app (op T) ⟨c⟩ := fun c =>
    congrArg (fun φ => φ.app (op _) ⟨c⟩) hz
  let r : m.target ⟶ B := MarkedPresheaf.homMk
    ((closedSubpresheafUnivIso m.atom).hom ≫ uliftYonedaEquiv.symm zB) fun V y hy => by
      rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy with hy | ⟨a, ha, him, hd⟩
      · exact B.mem_marked_of_isDegenerate
          (isDegenerate_app ((closedSubpresheafUnivIso m.atom).hom ≫ uliftYonedaEquiv.symm zB) hy)
      change B.underlying.map y.1.down.op zB ∈ B.marked V
      obtain ⟨e, he⟩ := exists_iso_comp_closureIncl y.1.down (Atom.map_top_eq_Iic_iff.1 him) hd
      have hyz : B.underlying.map y.1.down.op zB =
          B.underlying.map e.hom.op (B.underlying.map (Atom.closureIncl m.atom a).op zB) := by
        rw [← he]
        exact Functor.map_comp_apply B.underlying (Atom.closureIncl m.atom a).op e.hom.op zB
      refine (congrArg (· ∈ B.marked V) hyz).mpr ((B.transport e _).1 ?_)
      rcases m.mem_targetMarking_iff.1 ha with rfl | ⟨hsub, rfl⟩ | ha
      · obtain ⟨e', he'⟩ := exists_iso_comp_closureIncl (a := m.atom.top) (𝟙 m.atom)
          (Atom.map_top_eq_Iic_iff.1 (Atom.map_top _)) m.atom.dimension_eq
        have hι : Atom.closureIncl m.atom m.atom.top = e'.inv := by
          rw [← Category.id_comp (Atom.closureIncl m.atom m.atom.top), ← e'.inv_hom_id,
            Category.assoc, he', Category.comp_id]
        have hz' : B.underlying.map (Atom.closureIncl m.atom m.atom.top).op zB =
            B.underlying.map e'.symm.hom.op zB := by
          rw [hι]
          rfl
        exact (congrArg (· ∈ B.marked _) hz').mpr ((B.transport e'.symm zB).1 hzm)
      · exact hzf hsub
      · exact (congrArg (· ∈ B.marked _)
          (hzi (principalInclusionIn m.atom m.hornSet (m.marking_mem a ha).1))).mpr
          (MarkedPresheaf.map_mem_marked p (hw a ha))
  have sq : CommSq q (markedHornInclusion m) p r := ⟨MarkedPresheaf.hom_ext (by
    ext ⟨T⟩ y
    exact (hzi (Φ.inv.app (op T) y).down).symm)⟩
  let F := MarkedPresheaf.forget.map sq.lift
  let z : diagram E.underlying m.atom :=
    F.app (op m.atom) ⟨⟨𝟙 m.atom⟩, fun _ => LowerSet.mem_top⟩
  have hfz : ∀ {T : Atom} (g : T ⟶ m.atom) (hg : ∀ t, g t ∈ (⊤ : LowerSet m.atom.ogp)),
      F.app (op T) ⟨⟨g⟩, hg⟩ = E.underlying.map g.op z := by
    intro T g hg
    exact (congrArg (F.app (op T))
      (Subtype.ext (congrArg ULift.up (Category.comp_id g).symm))).trans
      (NatTrans.naturality_apply F g.op
        (⟨⟨𝟙 m.atom⟩, fun _ => LowerSet.mem_top⟩ : m.target.underlying.obj (op m.atom)))
  refine ⟨z, ⟨?_, ?_, fun hsub => ?_⟩, ?_⟩
  · ext ⟨T⟩ ⟨c⟩
    have e := congrArg (fun φ : m.source ⟶ E =>
      (MarkedPresheaf.forget.map φ).app (op T) (Φ.hom.app (op T) ⟨c⟩)) sq.fac_left
    exact (hfz (Atom.fullyFaithful.preimage (c ≫ m.hornIncl))
      (fun _ => LowerSet.mem_top)).symm.trans e
  · exact MarkedPresheaf.map_mem_marked sq.lift ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
      (Or.inr ⟨m.atom.top, m.mem_targetMarking_iff.2 (Or.inl rfl), Atom.map_top _,
        m.atom.dimension_eq⟩))
  · exact (congrArg (· ∈ E.marked _) (hfz _ (fun _ => LowerSet.mem_top))).mp
      (MarkedPresheaf.map_mem_marked sq.lift ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
        (Or.inr ⟨m.face, m.mem_targetMarking_iff.2 (Or.inr (Or.inl ⟨hsub, rfl⟩)),
          Atom.map_closureInclOGP_top m.atom m.face, Atom.dimension_ofClosure m.atom m.face⟩)))
  · let pt : m.target.underlying.obj (op m.atom) := ⟨⟨𝟙 m.atom⟩, fun _ => LowerSet.mem_top⟩
    have e := congrArg (fun φ : m.target ⟶ B => (MarkedPresheaf.forget.map φ).app (op m.atom) pt)
      sq.fac_right
    have e' := congrArg (fun φ => φ.app (op m.atom) pt) (MarkedPresheaf.forget.map_comp sq.lift p)
    exact (NatTrans.comp_app_apply F _ _ _).symm.trans (e'.symm.trans (e.trans
      ((uliftYonedaEquiv_apply _).symm.trans (uliftYonedaEquiv.apply_symm_apply zB))))

section InvertorHornFace

variable {V : Atom} (ε : Bool) (hV : 0 < V.dimension)

private theorem mem_hornSet_of_mem_faceSet_invertorAtom {a : (invertorAtom V ε hV).ogp}
    (ha : a ∈ (invertorAtom V ε hV).ogp.faces (!(!ε)) (invertorAtom V ε hV).top) :
    a ∈ (invertorMarkedHorn V ε hV).hornSet ∧ 0 < grade ℕ a := by
  have hb : a ∈ (invertorAtom V ε hV).ogp.bdry ⊤ (!(!ε)) := by
    rw [← (invertorAtom V ε hV).Iic_top, bdry_Iic]
    exact subset_lowerClosure ha
  refine ⟨(invertorMarkedHorn V ε hV).bdry_not_subset_hornSet hb, ?_⟩
  have h₁ := Nat.covBy_iff_add_one_eq.1 ((mem_faces.1 ha).1.grade ℕ)
  have h₂ := (invertorAtom V ε hV).dimension_eq
  have h₃ := dimension_invertorAtom V ε hV
  omega

def invertorMarkedHornFace : MarkedHornData :=
  { invertorMarkedHorn V ε hV with
    marking := insert (invertorTopElt V ε hV (some (!ε)))
      ((invertorAtom V ε hV).ogp.faces (!(!ε)) (invertorAtom V ε hV).top)
    marking_mem := fun a ha => by
      rcases Set.mem_insert_iff.1 ha with rfl | ha
      · exact ⟨invertorTopElt_some_bnot_mem_hornSet V ε hV,
          lt_of_lt_of_eq hV (dim_invertorTopElt_some V ε hV (!ε)).symm⟩
      · exact mem_hornSet_of_mem_faceSet_invertorAtom ε hV ha
    marked_tops := fun i hi y hy hyd => Set.mem_insert_iff.2 (Or.inl (Set.mem_singleton_iff.1
      ((invertorMarkedHorn V ε hV).marked_tops i hi y hy hyd))) }

theorem mem_marking_invertorMarkedHornFace {a : (invertorAtom V ε hV).ogp} :
    a ∈ (invertorMarkedHornFace ε hV).marking ↔ a = invertorTopElt V ε hV (some (!ε)) ∨
      a ∈ (invertorAtom V ε hV).ogp.faces (!(!ε)) (invertorAtom V ε hV).top :=
  Set.mem_insert_iff

private theorem invertorTopElt_some_bnot_notMem_faceSet :
    invertorTopElt V ε hV (some (!ε)) ∉
      (invertorAtom V ε hV).ogp.faces (!(!ε)) (invertorAtom V ε hV).top := fun h => by
  obtain ⟨_, h₁⟩ := mem_faces.1 h
  obtain ⟨_, h₂⟩ := mem_faces.1 (invertorTopElt_mem_faceSet V ε hV (!ε))
  exact absurd (h₁.symm.trans h₂) (by simp)

theorem not_faceSet_subset_marking_invertorMarkedHorn :
    ¬ (invertorAtom V ε hV).ogp.faces (!(invertorMarkedHorn V ε hV).side)
        (invertorAtom V ε hV).top ⊆ (invertorMarkedHorn V ε hV).marking := by
  intro h
  have hpos : 0 < grade ℕ (invertorAtom V ε hV).top := by
    rw [← (invertorAtom V ε hV).dimension_eq, dimension_invertorAtom]
    omega
  obtain ⟨y, hy⟩ := (invertorAtom V ε hV).isMolecule.nonempty_faces LowerSet.mem_top hpos (!(!ε))
  have hy' := Set.mem_singleton_iff.1 (h hy)
  rw [hy'] at hy
  exact invertorTopElt_some_bnot_notMem_faceSet ε hV hy

private theorem dim_invertorHornProj_lt {a : (invertorAtom V ε hV).ogp}
    (ha : a ∈ (invertorAtom V ε hV).ogp.faces (!(!ε)) (invertorAtom V ε hV).top)
    (h : a ∈ (invertorMarkedHorn V ε hV).hornSet) :
    grade ℕ (ConcreteCategory.hom (invertorHornProj V ε hV).hom ⟨a, h⟩) < grade ℕ a := by
  have hda : grade ℕ a = V.dimension := by
    have h₁ := Nat.covBy_iff_add_one_eq.1 ((mem_faces.1 ha).1.grade ℕ)
    have h₂ := (invertorAtom V ε hV).dimension_eq
    have h₃ := dimension_invertorAtom V ε hV
    omega
  rw [hda]
  have hr : V.toMoleculeShape.IsRound := V.isAtom.isRound
  rcases LowerSet.mem_sup_iff.1 (hornSet_invertorAtom_le ε hV hr h) with h' | ⟨u, -, rfl⟩
  · have hVc : map (invertorEndpointNot V.toMoleculeShape ε hV) ⊤ =
        .Iic (invertorTopElt V ε hV (some (!ε))) :=
      (image_invertorEndpointNot _ ε hV).trans (closure_invertorTopElt _ ε hV (!ε)).symm
    rw [hVc] at h'
    have hd : grade ℕ a = (invertorAtom V ε hV).dimension - 1 := by
      rw [hda, dimension_invertorAtom]
      omega
    obtain rfl := eq_of_mem_closure_invertorTopElt V ε hV h' hd
    exact absurd ha (invertorTopElt_some_bnot_notMem_faceSet ε hV)
  · have hb : V.toMoleculeShape.boundaryIncl (V.dimension - 1) (!ε)
        (ConcreteCategory.hom (cylProj _ _).hom u) ∈
          V.toMoleculeShape.ogp.boundary ⊤ (V.dimension - 1) (!ε) :=
      (V.toMoleculeShape.map_boundaryIncl_top _ _).le ⟨_, LowerSet.mem_top, rfl⟩
    refine lt_of_eq_of_lt (congrArg (grade ℕ) ((invertorHornProj_apply V ε hV _).trans
      (proj_invertorShapeIso_symm_invertorUnitEmb V.toMoleculeShape ε hV hr u))) ?_
    exact lt_of_le_of_lt (grade_le_of_mem_boundary hb) (by omega)

private theorem isDegenerate_map_of_dim_lt {Y : DiagSet.{u}} {S W : Atom} (g : S ⟶ W)
    (h : grade ℕ (g S.top) < S.dimension) (e : diagram Y W) :
    IsDegenerate Y (Y.map g.op e) := by
  refine ⟨Atom.ofClosure W (g S.top), principalLift W (g S.top) g
    (apply_mem_closure_apply_top g), Y.map (Atom.closureIncl W (g S.top)).op e,
    isCollapseHom_of_apply_eq_top _ (principalLift_apply_top g), fun hiso => ?_, ?_⟩
  · have h₁ := Atom.dimension_eq_of_iso (asIso (principalLift W (g S.top) g
      (apply_mem_closure_apply_top g)))
    rw [Atom.dimension_ofClosure] at h₁
    omega
  · exact (Functor.map_comp_apply Y _ _ e).symm.trans
      (congrArg (fun t : S ⟶ W => Y.map t.op e) (principalLift_comp_closureIncl _ _ _ _))

private theorem mem_marked_invertorHornMap_of_mem_faceSet {X : MarkedDiagSet.{u}}
    (e : diagram X.underlying V) {a : (invertorAtom V ε hV).ogp}
    (ha' : a ∈ (invertorAtom V ε hV).ogp.faces (!(!ε)) (invertorAtom V ε hV).top)
    (hh : a ∈ (invertorMarkedHorn V ε hV).hornSet) :
    (invertorHornMap ε hV e).app (op _)
      ⟨principalInclusionIn (invertorAtom V ε hV) (invertorMarkedHorn V ε hV).hornSet hh⟩ ∈
        X.marked _ := by
  refine X.mem_marked_of_isDegenerate ?_
  let c := principalInclusionIn (invertorAtom V ε hV) (invertorMarkedHorn V ε hV).hornSet hh
  let g : Atom.ofClosure (invertorAtom V ε hV) a ⟶ V :=
    Atom.fullyFaithful.preimage (c ≫ invertorHornProj V ε hV)
  have hval : (invertorHornMap ε hV e).app (op _) ⟨c⟩ = X.underlying.map g.op e :=
    (realize_map_comp_app (invertorHornProj V ε hV) (ofCell e).map c).trans
      (ofCell_map_app_map e g)
  refine (congrArg (IsDegenerate X.underlying) hval).mpr (isDegenerate_map_of_dim_lt g ?_ e)
  have hg : g (Atom.ofClosure (invertorAtom V ε hV) a).top =
      ConcreteCategory.hom (invertorHornProj V ε hV).hom ⟨a, hh⟩ :=
    congrArg (ConcreteCategory.hom (invertorHornProj V ε hV).hom)
      (Subtype.ext (Atom.closureIncl_top _ _))
  exact lt_of_eq_of_lt (congrArg (grade ℕ) hg) (lt_of_lt_of_eq
    (dim_invertorHornProj_lt ε hV ha' hh) (Atom.dimension_ofClosure _ _).symm)

theorem marksHorn_invertorMarkedHornFace {X : MarkedDiagSet.{u}} (e : diagram X.underlying V)
    (he : e ∈ X.marked V) :
    (invertorMarkedHornFace ε hV).MarksHorn X (invertorHornMap ε hV e) := fun a ha =>
  ((mem_marking_invertorMarkedHornFace ε hV).1 ha).elim
    (fun h => marksHorn_invertorHornMap ε hV e he a (Set.mem_singleton_iff.2 h))
    (fun ha' => mem_marked_invertorHornMap_of_mem_faceSet ε hV e ha' _)

end InvertorHornFace

private theorem invertorHornMap_comp {V : Atom} (ε : Bool) (hV : 0 < V.dimension)
    {Y Z : DiagSet.{u}} (x : diagram Y V) (f : Y ⟶ Z) :
    invertorHornMap ε hV x ≫ f = invertorHornMap ε hV (f.app _ x) :=
  (Category.assoc _ _ _).trans (congrArg (realize.map (invertorHornProj V ε hV) ≫ ·)
    (ofCell_app_map f x).symm)

namespace InversionData

section StepLift

variable {X : DiagSet.{u}} (A : InversionData X) {E B : MarkedDiagSet.{u}} (p : E ⟶ B)

private theorem exists_invertor_lift
    (hp : ∀ m : MarkedHornData, HasLiftingProperty (markedHornInclusion m) p)
    (g : X ⟶ E.underlying) (β : A.step ⟶ B.underlying)
    (hβ : A.stepIncl ≫ β = g ≫ MarkedPresheaf.forget.map p)
    (i : A.ι) (α : Bool) (hV : 0 < (A.shape i).dimension)
    (hg : g.app _ (A.cell i) ∈ E.marked _)
    (θ : invertorAtom (A.shape i) (!α) hV ≅ A.next.shape (i, α))
    (hβZ : β.app _ (A.next.cell (i, α)) ∈ B.marked _) :
    ∃ z : diagram E.underlying (invertorAtom (A.shape i) (!α) hV),
      realize.map (invertorMarkedHorn (A.shape i) (!α) hV).hornIncl ≫ (ofCell z).map =
        invertorHornMap (!α) hV (g.app _ (A.cell i)) ∧ z ∈ E.marked _ ∧
      (MarkedPresheaf.forget.map p).app _ z =
        B.underlying.map θ.hom.op (β.app _ (A.next.cell (i, α))) ∧
      (B.underlying.map (Atom.closureIncl _ (invertorTopElt (A.shape i) (!α) hV (some (!α)))).op
          (B.underlying.map θ.hom.op (β.app _ (A.next.cell (i, α)))) ∈ B.marked _ →
        E.underlying.map (Atom.closureIncl _ (invertorTopElt (A.shape i) (!α) hV
          (some (!α)))).op z ∈ E.marked _) := by
  have hzBm : B.underlying.map θ.hom.op (β.app _ (A.next.cell (i, α))) ∈ B.marked _ :=
    (B.transport θ _).1 hβZ
  have hhorn : realize.map (invertorMarkedHorn (A.shape i) (!α) hV).hornIncl ≫
      (ofCell (B.underlying.map θ.hom.op (β.app _ (A.next.cell (i, α))))).map =
      invertorHornMap (!α) hV (g.app _ (A.cell i)) ≫ MarkedPresheaf.forget.map p := by
    have hn : β.app _ (A.step.map θ.hom.op (A.next.cell (i, α))) =
        B.underlying.map θ.hom.op (β.app _ (A.next.cell (i, α))) :=
      NatTrans.naturality_apply β θ.hom.op _
    have h₁ : (ofCell (B.underlying.map θ.hom.op (β.app _ (A.next.cell (i, α))))).map =
        (ofCell (A.step.map θ.hom.op (A.next.cell (i, α)))).map ≫ β := by
      rw [← hn]
      exact ofCell_app_map β _
    refine (congrArg (_ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans ?_)
    refine (congrArg (· ≫ β) (A.hornIncl_comp_next_cell i α hV θ)).trans ?_
    refine (invertorHornMap_comp _ hV _ β).trans ?_
    refine Eq.trans ?_ (invertorHornMap_comp _ hV _ _).symm
    exact congrArg (invertorHornMap (!α) hV)
      ((NatTrans.comp_app_apply _ _ _ _).symm.trans
        ((congrArg (fun φ => φ.app _ (A.cell i)) hβ).trans (NatTrans.comp_app_apply _ _ _ _)))
  by_cases hf : B.underlying.map (Atom.closureIncl _
      (invertorTopElt (A.shape i) (!α) hV (some (!α)))).op
        (B.underlying.map θ.hom.op (β.app _ (A.next.cell (i, α)))) ∈ B.marked _
  · have := hp (invertorMarkedHornFace (!α) hV)
    have hF : (invertorMarkedHornFace (!α) hV).Fills B
        (invertorHornMap (!α) hV (g.app _ (A.cell i)) ≫ MarkedPresheaf.forget.map p)
        (B.underlying.map θ.hom.op (β.app _ (A.next.cell (i, α)))) := by
      refine ⟨?_, ?_, ?_⟩
      · exact hhorn
      · exact hzBm
      · exact fun _ => hf
    have hfill := exists_fills_over_of_hasLiftingProperty
      (invertorMarkedHornFace (!α) hV) p (invertorHornMap (!α) hV (g.app _ (A.cell i)))
      (marksHorn_invertorMarkedHornFace (!α) hV _ hg) _ hF
    obtain ⟨z, hF', hpz⟩ := hfill
    have hz : realize.map (invertorMarkedHorn (A.shape i) (!α) hV).hornIncl ≫ (ofCell z).map =
        invertorHornMap (!α) hV (g.app _ (A.cell i)) := hF'.1
    have hsub : (invertorAtom (A.shape i) (!α) hV).ogp.faces
        (!(invertorMarkedHornFace (!α) hV).side) (invertorAtom (A.shape i) (!α) hV).top ⊆
          (invertorMarkedHornFace (!α) hV).marking := fun y hy =>
      (mem_marking_invertorMarkedHornFace (!α) hV).2 (Or.inr hy)
    exact ⟨z, hz, hF'.2.1, hpz, fun _ => hF'.2.2 hsub⟩
  · have := hp (invertorMarkedHorn (A.shape i) (!α) hV)
    obtain ⟨z, ⟨hz, hzm, -⟩, hpz⟩ := exists_fills_over_of_hasLiftingProperty
      (invertorMarkedHorn (A.shape i) (!α) hV) p (invertorHornMap (!α) hV (g.app _ (A.cell i)))
      (marksHorn_invertorHornMap (!α) hV _ hg) _
      ⟨hhorn, hzBm, fun hs => absurd hs (not_faceSet_subset_marking_invertorMarkedHorn (!α) hV)⟩
    exact ⟨z, hz, hzm, hpz, fun h => absurd h hf⟩

theorem exists_step_lift
    (hp : ∀ m : MarkedHornData, HasLiftingProperty (markedHornInclusion m) p)
    (g : X ⟶ E.underlying) (β : A.step ⟶ B.underlying)
    (hβ : A.stepIncl ≫ β = g ≫ MarkedPresheaf.forget.map p)
    (hg : ∀ i, g.app _ (A.cell i) ∈ E.marked _)
    (hβZ : ∀ j, β.app _ (A.next.cell j) ∈ B.marked _) :
    ∃ g' : A.step ⟶ E.underlying, A.stepIncl ≫ g' = g ∧
      g' ≫ MarkedPresheaf.forget.map p = β ∧
      (∀ j, g'.app _ (A.next.cell j) ∈ E.marked _) ∧
      ∀ j, β.app _ (A.invertorExtension.incl.app _ (A.inverseExtension.cell j)) ∈ B.marked _ →
        g'.app _ (A.invertorExtension.incl.app _ (A.inverseExtension.cell j)) ∈ E.marked _ := by
  have hV : ∀ i, 0 < (A.shape i).dimension := A.dim_pos
  let θ : ∀ j : A.ι × Bool, invertorAtom (A.shape j.1) (!j.2) (hV j.1) ≅ A.next.shape j :=
    fun j => Classical.choice (A.nonempty_iso_invertorAtom_next_shape j.1 j.2 (hV j.1))
  choose z hzh hzm hzp hzf using fun j : A.ι × Bool =>
    A.exists_invertor_lift p hp g β hβ j.1 j.2 (hV j.1) (hg j.1) (θ j) (hβZ j)
  let L : A.ι × Bool → Σ H : Atom, diagram E.underlying H := fun j =>
    ⟨Atom.ofClosure (invertorAtom (A.shape j.1) (!j.2) (hV j.1))
      (invertorTopElt (A.shape j.1) (!j.2) (hV j.1) (some (!j.2))),
      E.underlying.map (Atom.closureIncl _ _).op (z j)⟩
  let Z : A.ι × Bool → Σ H : Atom, diagram E.underlying H := fun j =>
    ⟨invertorAtom (A.shape j.1) (!j.2) (hV j.1), z j⟩
  have hLZ : A.Inverts g L Z := fun i => by
    obtain ⟨d, hd⟩ := exists_biInvData_of_invertors (hV i) (g.app _ (A.cell i))
      (fun α => z (i, α)) (fun α => hzh (i, α))
    exact ⟨cellRound (g.app _ (A.cell i)), d, .refl _, hd⟩
  have hnext : ∀ j, (A.stepDesc g L Z hLZ).app _ (A.next.cell j) =
      E.underlying.map (θ j).inv.op (z j) := fun j =>
    A.stepDesc_app_next g L Z hLZ j (θ j).symm
  let κ : ∀ j : A.ι × Bool, A.inverseExtension.shape j ≅ (L j).1 := fun j =>
    Classical.choice (A.nonempty_iso_inverseExtension_shape_ofClosure j.1 j.2 (hV j.1))
  have hinv : ∀ j, (A.stepDesc g L Z hLZ).app _
      (A.invertorExtension.incl.app _ (A.inverseExtension.cell j)) =
      E.underlying.map (κ j).hom.op (L j).2 := fun j =>
    A.stepDesc_app_inverse g L Z hLZ j (κ j)
  have hβinv : ∀ j, β.app _ (A.invertorExtension.incl.app _ (A.inverseExtension.cell j)) =
      B.underlying.map (κ j).hom.op (B.underlying.map (Atom.closureIncl _ _).op
        (B.underlying.map (θ j).hom.op (β.app _ (A.next.cell j)))) := by
    rintro ⟨i, α⟩
    have h := A.map_closureIncl_next_cell i α (hV i) (θ (i, α)) (κ (i, α))
    refine (congrArg (β.app _) h).symm.trans ?_
    refine (NatTrans.naturality_apply β _ _).trans ?_
    refine congrArg (B.underlying.map _) ((NatTrans.naturality_apply β _ _).trans ?_)
    exact congrArg (B.underlying.map _) (NatTrans.naturality_apply β _ _)
  have hpinv : ∀ j, (MarkedPresheaf.forget.map p).app _ (E.underlying.map (κ j).hom.op (L j).2) =
      β.app _ (A.invertorExtension.incl.app _ (A.inverseExtension.cell j)) := by
    rintro ⟨i, α⟩
    refine (NatTrans.naturality_apply (MarkedPresheaf.forget.map p) _ _).trans ?_
    refine Eq.trans ?_ (hβinv (i, α)).symm
    refine congrArg (B.underlying.map _)
      ((NatTrans.naturality_apply (MarkedPresheaf.forget.map p) _ _).trans ?_)
    exact congrArg (B.underlying.map _) (hzp (i, α))
  refine ⟨A.stepDesc g L Z hLZ, A.stepIncl_stepDesc g L Z hLZ, ?_, fun j => ?_, fun j hj => ?_⟩
  · refine A.step_hom_ext ?_ (fun j => ?_) ?_
    · exact (A.stepIncl_stepDesc_assoc g L Z hLZ _).trans hβ.symm
    · exact (NatTrans.comp_app_apply _ _ _ _).trans
        ((congrArg _ (hinv j)).trans (hpinv j))
    · rintro ⟨i, α⟩
      refine (NatTrans.comp_app_apply _ _ _ _).trans ((congrArg _ (hnext (i, α))).trans ?_)
      refine (NatTrans.naturality_apply (MarkedPresheaf.forget.map p) _ _).trans ?_
      refine (congrArg (B.underlying.map _) (hzp (i, α))).trans ?_
      refine (Functor.map_comp_apply B.underlying _ _ _).symm.trans ?_
      rw [← op_comp, Iso.inv_hom_id, op_id, Functor.map_id_apply]
      rfl
  · rw [hnext j]
    exact (E.transport (θ j).symm _).1 (hzm j)
  · rw [hinv j]
    obtain ⟨i, α⟩ := j
    refine (E.transport (κ (i, α)) _).1 (hzf (i, α) ?_)
    rw [hβinv (i, α)] at hj
    exact (B.transport (κ (i, α)) _).2 hj

theorem exists_localization_lift
    (hp : ∀ m : MarkedHornData, HasLiftingProperty (markedHornInclusion m) p)
    (g : X ⟶ E.underlying) (b : A.localization ⟶ B.underlying)
    (hb : A.toLocalization ≫ b = g ≫ MarkedPresheaf.forget.map p)
    (hg : ∀ i, g.app _ (A.cell i) ∈ E.marked _)
    (hbZ : ∀ n j, (A.stageι n ≫ b).app _ ((A.stage n).2.cell j) ∈ B.marked _) :
    ∃ g' : A.localization ⟶ E.underlying, A.toLocalization ≫ g' = g ∧
      g' ≫ MarkedPresheaf.forget.map p = b ∧
      ∀ n j, (A.stageι n ≫ g').app _ ((A.stage n).2.cell j) ∈ E.marked _ := by
  let P : ∀ n, ((A.stage n).1 ⟶ E.underlying) → Prop := fun n g' =>
    g' ≫ MarkedPresheaf.forget.map p = A.stageι n ≫ b ∧
      ∀ j, g'.app _ ((A.stage n).2.cell j) ∈ E.marked _
  have hstep : ∀ n (r : {g' // P n g'}), ∃ r' : {g' // P (n + 1) g'},
      (A.stage n).2.stepIncl ≫ r'.1 = r.1 := by
    intro n r
    obtain ⟨g'', h₁, h₂, h₃, -⟩ := (A.stage n).2.exists_step_lift p hp r.1 (A.stageι (n + 1) ≫ b)
      ((A.stepIncl_stageι_assoc n b).trans r.2.1.symm) r.2.2 (hbZ (n + 1))
    exact ⟨⟨g'', h₂, h₃⟩, h₁⟩
  choose F hF using hstep
  let seq : ∀ n, {g' // P n g'} := fun n =>
    Nat.rec (motive := fun n => {g' // P n g'}) ⟨g, hb.symm, hg⟩ (fun n r => F n r) n
  refine ⟨A.desc (fun n => (seq n).1) (fun n => hF n (seq n)), A.stageι_desc _ _ 0,
    A.hom_ext fun n => ?_, fun n j => ?_⟩
  · exact (A.stageι_desc_assoc _ _ n _).trans (seq n).2.1
  · exact (congrArg (fun φ : (A.stage n).1 ⟶ E.underlying =>
      φ.app _ ((A.stage n).2.cell j) ∈ E.marked _) (A.stageι_desc _ _ n)).mpr ((seq n).2.2 j)

end StepLift

end InversionData

namespace InversionData

variable {X : DiagSet.{u}} (A : InversionData X)

def familyMarking : MarkedPresheaf.Marking atomMarking A.localization where
  marked V := {x | IsDegenerate _ x ∨ ∃ (n : ℕ) (j : (A.stage n).2.ι)
    (e : V ≅ (A.stage n).2.shape j),
      x = A.localization.map e.hom.op ((A.stageι n).app _ ((A.stage n).2.cell j))}
  markable _ _ hx := by
    rcases hx with hx | ⟨n, j, e, -⟩
    · exact dimension_pos_of_isDegenerate hx
    · exact (congrArg (0 < ·) (Atom.dimension_eq_of_iso e)).mpr ((A.stage n).2.dim_pos j)
  degenerate _ b p hp y := Or.inl ⟨b, p, y, hp.1, hp.2, rfl⟩
  transport V W e x := by
    refine or_congr (isDegenerate_map_iso_iff e x).symm ⟨?_, ?_⟩
    · rintro ⟨n, j, e', rfl⟩
      exact ⟨n, j, e ≪≫ e', (Functor.map_comp_apply _ _ _ _).symm⟩
    · rintro ⟨n, j, e', hx⟩
      refine ⟨n, j, e.symm ≪≫ e', ?_⟩
      calc x = A.localization.map e.inv.op (A.localization.map e.hom.op x) := by
            rw [← Functor.map_comp_apply, ← op_comp, e.inv_hom_id, op_id, Functor.map_id_apply]
        _ = A.localization.map e.inv.op (A.localization.map e'.hom.op
            ((A.stageι n).app _ ((A.stage n).2.cell j))) := by rw [hx]
        _ = _ := (Functor.map_comp_apply _ _ _ _).symm

noncomputable def markedLocalization : MarkedDiagSet.{u} :=
  MarkedPresheaf.ofMarking A.localization A.familyMarking

theorem stageι_app_cell_mem_marked (n : ℕ) (j : (A.stage n).2.ι) :
    (A.stageι n).app _ ((A.stage n).2.cell j) ∈ A.markedLocalization.marked _ :=
  (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
    (Or.inr ⟨n, j, Iso.refl _, by rw [Iso.refl_hom, op_id, Functor.map_id_apply]⟩)

noncomputable def markedLocalizationHom {Z : MarkedDiagSet.{u}} (g : A.localization ⟶ Z.underlying)
    (hg : ∀ n j, (A.stageι n ≫ g).app _ ((A.stage n).2.cell j) ∈ Z.marked _) :
    A.markedLocalization ⟶ Z :=
  MarkedPresheaf.homMk g fun V x hx => by
    rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hx with hx | ⟨n, j, e, rfl⟩
    · exact Z.mem_marked_of_isDegenerate (isDegenerate_app g hx)
    · exact (congrArg (· ∈ Z.marked V) (NatTrans.naturality_apply g e.hom.op _)).mpr
        ((Z.transport e _).1 (hg n j))

@[simp]
theorem forget_map_markedLocalizationHom {Z : MarkedDiagSet.{u}} (g : A.localization ⟶ Z.underlying)
    (hg : ∀ n j, (A.stageι n ≫ g).app _ ((A.stage n).2.cell j) ∈ Z.marked _) :
    MarkedPresheaf.forget.map (A.markedLocalizationHom g hg) = g :=
  rfl

end InversionData

end Localization

end Atoms.Diagrammatic
