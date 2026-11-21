import Atoms.Diagrammatic.Localization.WalkingEquivalence
import Atoms.Shape.Dual
import Atoms.Shape.Invertor

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Homotopical Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

namespace InversionData

variable (A : InversionData X)

private theorem ofCell_yonedaEquiv {H : Atom} (m : realize.obj H.toMoleculeShape.rdc ⟶ Y) :
    ofCell (uliftYonedaEquiv ((realizeAtomIso H).inv ≫ m)) = ⟨H.toMoleculeShape, m⟩ :=
  congrArg (PastingDiagram.mk H.toMoleculeShape)
    ((congrArg ((realizeAtomIso H).hom ≫ ·) (uliftYonedaEquiv.symm_apply_apply _)).trans
      ((realizeAtomIso H).hom_inv_id_assoc m))

private noncomputable def reverseCell (f : X ⟶ Y)
    (hf : ∀ i, IsDegenerate Y (f.app (op (A.shape i)) (A.cell i))) (j : A.ι × Bool) :
    Σ H : Atom, diagram Y H :=
  ⟨(A.shape j.1).dual (OGP.topDim (A.shape j.1).dimension),
    uliftYonedaEquiv ((realizeAtomIso _).inv ≫
      ((ofCell (f.app _ (A.cell j.1))).reverse ((isDegenerate_ofCell_iff _).2 (hf j.1))).map)⟩

private noncomputable def invertorCell (f : X ⟶ Y)
    (hf : ∀ i, IsDegenerate Y (f.app (op (A.shape i)) (A.cell i))) (j : A.ι × Bool) :
    Σ H : Atom, diagram Y H :=
  ⟨invertorAtom (A.shape j.1) (!j.2) (A.dim_pos j.1), uliftYonedaEquiv ((realizeAtomIso _).inv ≫
    ((ofCell (f.app _ (A.cell j.1))).invertor ((isDegenerate_ofCell_iff _).2 (hf j.1)) j.2).map)⟩

private theorem inverts_of_isDegenerate (f : X ⟶ Y)
    (hf : ∀ i, IsDegenerate Y (f.app (op (A.shape i)) (A.cell i))) :
    A.Inverts f (A.reverseCell f hf) (A.invertorCell f hf) := fun i =>
  ⟨_, (BiInvData.ofIsDegenerate (cellRound (f.app _ (A.cell i)))
      ((isDegenerate_ofCell_iff _).2 (hf i))).mono (Set.subset_univ _), .refl _, fun _ =>
    ⟨equiv_of_eq (ofCell_yonedaEquiv _), equiv_of_eq (ofCell_yonedaEquiv _)⟩⟩

private theorem isDegenerate_invertorCell (f : X ⟶ Y)
    (hf : ∀ i, IsDegenerate Y (f.app (op (A.shape i)) (A.cell i))) (j : A.ι × Bool) :
    IsDegenerate Y (A.invertorCell f hf j).2 :=
  (isDegenerate_ofCell_iff _).1 (Eq.mpr (congrArg PastingDiagram.IsDegenerate
    (ofCell_yonedaEquiv _)) (isDegenerate_invertor (ofCell (f.app _ (A.cell j.1)))
      ((isDegenerate_ofCell_iff _).2 (hf j.1)) j.2))

private noncomputable def extendDegenerateStage (f : X ⟶ Y)
    (hf : ∀ i, IsDegenerate Y (f.app (op (A.shape i)) (A.cell i))) :
    ∀ n, {g : (A.stage n).1 ⟶ Y //
      ∀ i, IsDegenerate Y (g.app (op ((A.stage n).2.shape i)) ((A.stage n).2.cell i))}
  | 0 => ⟨f, hf⟩
  | n + 1 =>
    let g := extendDegenerateStage f hf n
    ⟨(A.stage n).2.stepDesc g.1 _ _ ((A.stage n).2.inverts_of_isDegenerate g.1 g.2), fun j =>
      ((A.stage n).2.stepDesc_app_next _ _ _ _ j (Classical.choice
        ((A.stage n).2.nonempty_iso_next_stepDesc _ _ _
          ((A.stage n).2.inverts_of_isDegenerate g.1 g.2) j))).symm ▸
        (isDegenerate_map_iso_iff _ _).2 ((A.stage n).2.isDegenerate_invertorCell g.1 g.2 j)⟩

noncomputable def extendDegenerate (f : X ⟶ Y)
    (hf : ∀ i, IsDegenerate Y (f.app (op (A.shape i)) (A.cell i))) : A.localization ⟶ Y :=
  A.desc (fun n => (A.extendDegenerateStage f hf n).1) fun n =>
    (A.stage n).2.stepIncl_stepDesc _ _ _ _

@[reassoc (attr := simp)]
theorem toLocalization_extendDegenerate (f : X ⟶ Y)
    (hf : ∀ i, IsDegenerate Y (f.app (op (A.shape i)) (A.cell i))) :
    A.toLocalization ≫ A.extendDegenerate f hf = f :=
  A.stageι_desc _ _ 0

private def toBallAtomPoint (X : DiagSet.{u}) : X ⟶ ball atomPoint where
  app V := ↾fun _ => ⟨toAtomPoint V.unop⟩
  naturality _ _ _ := by
    ext
    exact ULift.ext _ _ (Subsingleton.elim (α := _ ⟶ atomPoint) _ _)

private theorem isDegenerate_ball_atomPoint {V : Atom} (hV : 0 < V.dimension)
    (x : diagram (ball.{u} atomPoint) V) : IsDegenerate (ball atomPoint) x :=
  ⟨atomPoint, toAtomPoint V, ⟨𝟙 atomPoint⟩, isCollapseHom_toAtomPoint V, fun h => by
    have := Atom.dimension_eq_of_iso (asIso (toAtomPoint V))
    rw [dimension_atomPoint] at this
    omega, ULift.ext _ _ (Subsingleton.elim (α := V ⟶ atomPoint) _ _)⟩

theorem nonempty_iso_next_shape (j : A.ι × Bool) :
    Nonempty (A.next.shape j ≅ invertorAtom (A.shape j.1) (!j.2) (A.dim_pos j.1)) :=
  A.nonempty_iso_next_stepDesc (toBallAtomPoint X) _ _
    (A.inverts_of_isDegenerate (toBallAtomPoint X)
      fun i => isDegenerate_ball_atomPoint (A.dim_pos i) _) j

theorem nonempty_iso_inverseExtension_shape (j : A.ι × Bool) :
    Nonempty ((A.inverseExtension.shape j).ogp ≅
      ((A.shape j.1).toMoleculeShape.dual (OGP.topDim (A.shape j.1).dimension)).ogp) :=
  (A.nonempty_iso_inverse_stepDesc (toBallAtomPoint X) _ _
    (A.inverts_of_isDegenerate (toBallAtomPoint X)
      fun i => isDegenerate_ball_atomPoint (A.dim_pos i) _) j).map Atom.isoOGP

end InversionData

section WalkingEquivalence

variable {U : Atom} (hU : 0 < U.dimension)

noncomputable def walkingEquivalenceLift {W : Atom} (p : U ⟶ W)
    (hW : W.dimension < U.dimension) : walkingEquivalence U hU ⟶ ball W :=
  (topInversionData U hU).extendDegenerate (uliftYoneda.{u}.map p) fun _ =>
    isDegenerate_ball_of_dimension_lt hW _

@[reassoc (attr := simp)]
theorem toWalkingEquivalence_walkingEquivalenceLift {W : Atom} (p : U ⟶ W)
    (hW : W.dimension < U.dimension) :
    toWalkingEquivalence U hU ≫ walkingEquivalenceLift hU p hW = uliftYoneda.{u}.map p :=
  (topInversionData U hU).toLocalization_extendDegenerate _ _

theorem walkingEquivalenceLift_unique {W : Atom} {p : U ⟶ W}
    (hW : W.dimension < U.dimension) (φ : walkingEquivalence U hU ⟶ ball W)
    (h : toWalkingEquivalence U hU ≫ φ = uliftYoneda.{u}.map p) :
    walkingEquivalenceLift hU p hW = φ :=
  (topInversionData U hU).hom_ext_ball (fun _ => hW)
    ((toWalkingEquivalence_walkingEquivalenceLift hU p hW).trans h.symm)

theorem walkingEquivalenceLift_comp {W W' : Atom} (p : U ⟶ W) (r : W ⟶ W')
    (hW : W.dimension < U.dimension) (hW' : W'.dimension < U.dimension) :
    walkingEquivalenceLift hU p hW ≫ uliftYoneda.{u}.map r =
      walkingEquivalenceLift hU (p ≫ r) hW' :=
  (walkingEquivalenceLift_unique hU hW' _
    ((toWalkingEquivalence_walkingEquivalenceLift_assoc hU p hW (uliftYoneda.{u}.map r)).trans
      (uliftYoneda.{u}.map_comp p r).symm)).symm

theorem grade_apply_top_lt_of_degenerate {V : Atom} {g : U ⟶ V}
    (hg : atomMarking.Degenerate g) : grade ℕ (g U.top) < U.dimension := by
  obtain ⟨c, p, q, ⟨hp, hni⟩, rfl⟩ := hg
  have h₁ : grade ℕ (q (p U.top)) ≤ grade ℕ (p U.top) := (Atom.isMap q).grade_le _
  have h₂ : grade ℕ (p U.top) ≤ c.dimension := c.dimension_eq ▸ grade_mono (c.le_top _)
  have h₃ := dimension_le_of_isCollapseHom p hp
  have h₄ : c.dimension ≠ U.dimension := fun h =>
    hni (isIso_of_isCollapseHom_of_dimension_eq p hp h.symm)
  exact lt_of_le_of_lt (h₁.trans h₂) (lt_of_le_of_ne h₃ h₄)

theorem not_isIso_of_degenerate {V : Atom} {g : U ⟶ V} (hg : atomMarking.Degenerate g) :
    ¬ IsIso g := fun h => by
  have h₁ := grade_apply_top_lt_of_degenerate hg
  have h₂ : grade ℕ ((inv g) (g U.top)) ≤ grade ℕ (g U.top) := (Atom.isMap (inv g)).grade_le _
  have h₃ : (inv g) (g U.top) = U.top :=
    congrArg (fun f : U ⟶ U => f U.top) (IsIso.hom_inv_id g)
  rw [h₃, ← U.dimension_eq] at h₂
  omega

noncomputable def degenerateLift {V : Atom} (g : U ⟶ V) (hg : atomMarking.Degenerate g) :
    walkingEquivalence U hU ⟶ ball V :=
  walkingEquivalenceLift hU (principalLift V (g U.top) g (apply_mem_closure_apply_top g))
    (by rw [Atom.dimension_ofClosure]; exact grade_apply_top_lt_of_degenerate hg) ≫
    uliftYoneda.{u}.map (Atom.closureIncl V (g U.top))

@[reassoc (attr := simp)]
theorem toWalkingEquivalence_degenerateLift {V : Atom} (g : U ⟶ V)
    (hg : atomMarking.Degenerate g) :
    toWalkingEquivalence U hU ≫ degenerateLift hU g hg = uliftYoneda.{u}.map g :=
  (toWalkingEquivalence_walkingEquivalenceLift_assoc hU _ _ _).trans
    ((uliftYoneda.{u}.map_comp _ _).symm.trans
      (congrArg uliftYoneda.{u}.map (principalLift_comp_closureIncl _ _ _ _)))

theorem degenerateLift_eq {V W : Atom} (g : U ⟶ V) (hg : atomMarking.Degenerate g) (p : U ⟶ W)
    (i : W ⟶ V) (hW : W.dimension < U.dimension) (h : p ≫ i = g) :
    degenerateLift hU g hg = walkingEquivalenceLift hU p hW ≫ uliftYoneda.{u}.map i := by
  let x := p U.top
  have hx : (Atom.ofClosure W x).dimension < U.dimension := by
    rw [Atom.dimension_ofClosure]
    exact ((grade_mono (W.le_top x)).trans_eq W.dimension_eq.symm).trans_lt hW
  have hg' : (Atom.ofClosure V (g U.top)).dimension < U.dimension := by
    rw [Atom.dimension_ofClosure]
    exact grade_apply_top_lt_of_degenerate hg
  have hmem : ∀ w, (Atom.closureIncl W x ≫ i) w ∈ LowerSet.Iic (g U.top) := fun w => by
    rw [← h]
    exact (Atom.isMap i).monotone (closureIncl_mem_closure W x w)
  let p' := principalLift W x p (apply_mem_closure_apply_top p)
  let r := principalLift V (g U.top) (Atom.closureIncl W x ≫ i) hmem
  have hp : p' ≫ Atom.closureIncl W x = p := principalLift_comp_closureIncl _ _ _ _
  have hr : r ≫ Atom.closureIncl V (g U.top) = Atom.closureIncl W x ≫ i :=
    principalLift_comp_closureIncl _ _ _ _
  have hpr : p' ≫ r = principalLift V (g U.top) g (apply_mem_closure_apply_top g) :=
    hom_ext_closureIncl V _ (by rw [Category.assoc, hr, ← Category.assoc, hp, h,
      principalLift_comp_closureIncl])
  exact (congrArg (fun q => walkingEquivalenceLift hU q hg' ≫
      uliftYoneda.{u}.map (Atom.closureIncl V (g U.top))) hpr.symm).trans
    ((congrArg (· ≫ uliftYoneda.{u}.map (Atom.closureIncl V (g U.top)))
      (walkingEquivalenceLift_comp hU p' r hx hg').symm).trans
    (((Category.assoc _ _ _).trans (congrArg (walkingEquivalenceLift hU p' hx ≫ ·)
      ((uliftYoneda.{u}.map_comp _ _).symm.trans (congrArg uliftYoneda.{u}.map hr)))).trans
    (((congrArg (walkingEquivalenceLift hU p' hx ≫ ·) (uliftYoneda.{u}.map_comp _ _)).trans
      (Category.assoc _ _ _).symm).trans
    (congrArg (· ≫ uliftYoneda.{u}.map i) ((walkingEquivalenceLift_comp hU p' _ hx hW).trans
      (congrArg (fun q => walkingEquivalenceLift hU q hW) hp))))))

theorem degenerateLift_comp {V W : Atom} (g : U ⟶ V) (hg : atomMarking.Degenerate g)
    (h : V ⟶ W) :
    degenerateLift hU (g ≫ h) (hg.comp h) = degenerateLift hU g hg ≫ uliftYoneda.{u}.map h := by
  have hW : (Atom.ofClosure V (g U.top)).dimension < U.dimension := by
    rw [Atom.dimension_ofClosure]
    exact grade_apply_top_lt_of_degenerate hg
  exact (degenerateLift_eq hU (g ≫ h) _
    (principalLift V (g U.top) g (apply_mem_closure_apply_top g))
    (Atom.closureIncl V (g U.top) ≫ h) hW
    (by rw [← Category.assoc, principalLift_comp_closureIncl])).trans
    ((congrArg (_ ≫ ·) (uliftYoneda.{u}.map_comp _ _)).trans (Category.assoc _ _ _).symm)

end WalkingEquivalence

section Iso

variable {U U' U'' : Atom} (hU : 0 < U.dimension) (hU' : 0 < U'.dimension)
  (hU'' : 0 < U''.dimension)

def topInversionDataHom (e : U' ≅ U) :
    (topInversionData.{u} U' hU').Hom (topInversionData U hU) where
  map := uliftYoneda.{u}.map e.hom
  index i := i
  iso _ := e
  map_app_cell _ := rfl

noncomputable def walkingEquivalenceMap (e : U' ≅ U) :
    walkingEquivalence.{u} U' hU' ⟶ walkingEquivalence U hU :=
  (topInversionDataHom hU hU' e).localizationMap

@[reassoc (attr := simp)]
theorem toWalkingEquivalence_walkingEquivalenceMap (e : U' ≅ U) :
    toWalkingEquivalence U' hU' ≫ walkingEquivalenceMap hU hU' e =
      uliftYoneda.{u}.map e.hom ≫ toWalkingEquivalence U hU :=
  (topInversionDataHom hU hU' e).toLocalization_localizationMap

theorem walkingEquivalenceMap_refl (e : U ≅ U) : walkingEquivalenceMap.{u} hU hU e = 𝟙 _ :=
  (congrArg InversionData.Hom.localizationMap
    (InversionData.Hom.ext ((congrArg (fun e' : U ≅ U => uliftYoneda.{u}.map e'.hom)
      (Atom.iso_eq e (Iso.refl U))).trans
      (uliftYoneda.{u}.map_id U)) rfl : topInversionDataHom hU hU e = InversionData.Hom.id _)).trans
    (InversionData.Hom.localizationMap_id _)

theorem walkingEquivalenceMap_comp (e : U'' ≅ U') (e' : U' ≅ U) (e'' : U'' ≅ U) :
    walkingEquivalenceMap.{u} hU hU'' e'' =
      walkingEquivalenceMap hU' hU'' e ≫ walkingEquivalenceMap hU hU' e' :=
  (congrArg InversionData.Hom.localizationMap
    (InversionData.Hom.ext ((congrArg (fun e''' : U'' ≅ U => uliftYoneda.{u}.map e'''.hom)
      (Atom.iso_eq e'' (e ≪≫ e'))).trans
      (uliftYoneda.{u}.map_comp _ _)) rfl :
      topInversionDataHom hU hU'' e'' =
        (topInversionDataHom hU' hU'' e).comp (topInversionDataHom hU hU' e'))).trans
    (InversionData.Hom.localizationMap_comp _ _)

noncomputable def walkingEquivalenceIso (e : U' ≅ U) :
    walkingEquivalence.{u} U' hU' ≅ walkingEquivalence U hU where
  hom := walkingEquivalenceMap hU hU' e
  inv := walkingEquivalenceMap hU' hU e.symm
  hom_inv_id := (walkingEquivalenceMap_comp hU' hU hU' e e.symm (Iso.refl U')).symm.trans
    (walkingEquivalenceMap_refl hU' _)
  inv_hom_id := (walkingEquivalenceMap_comp hU hU' hU e.symm e (Iso.refl U)).symm.trans
    (walkingEquivalenceMap_refl hU _)

theorem walkingEquivalenceMap_degenerateLift {V : Atom} (e : U' ≅ U) (g : U ⟶ V)
    (hg : atomMarking.Degenerate g) :
    walkingEquivalenceMap.{u} hU hU' e ≫ degenerateLift hU g hg =
      degenerateLift hU' (e.hom ≫ g) (hg.iso_comp e.hom) := by
  have hW : (Atom.ofClosure V (g U.top)).dimension < U'.dimension := by
    rw [Atom.dimension_ofClosure, Atom.dimension_eq_of_iso e]
    exact grade_apply_top_lt_of_degenerate hg
  refine Eq.trans ?_ (degenerateLift_eq hU' (e.hom ≫ g) _
    (e.hom ≫ principalLift V (g U.top) g (apply_mem_closure_apply_top g))
    (Atom.closureIncl V (g U.top)) hW
    (by rw [Category.assoc, principalLift_comp_closureIncl])).symm
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (walkingEquivalenceLift_unique hU' hW _
      ((toWalkingEquivalence_walkingEquivalenceMap_assoc hU hU' e _).trans
        ((congrArg (_ ≫ ·) (toWalkingEquivalence_walkingEquivalenceLift hU _ _)).trans
          (uliftYoneda.{u}.map_comp _ _).symm))).symm)

end Iso

section DegenerateCell

variable {P : DiagSet.{u}} {V : Atom} (hV : 0 < V.dimension)

private theorem dimension_lt_of_isDegenerate {t : diagram P V} (ht : IsDegenerate P t) :
    ht.choose.dimension < V.dimension :=
  lt_of_le_of_ne (dimension_le_of_isCollapseHom _ ht.choose_spec.choose_spec.choose_spec.1)
    fun h => ht.choose_spec.choose_spec.choose_spec.2.1
      (isIso_of_isCollapseHom_of_dimension_eq _ ht.choose_spec.choose_spec.choose_spec.1 h.symm)

noncomputable def degenerateCellLift (t : diagram P V) (ht : IsDegenerate P t) :
    walkingEquivalence V hV ⟶ P :=
  walkingEquivalenceLift hV ht.choose_spec.choose (dimension_lt_of_isDegenerate ht) ≫
    uliftYonedaEquiv.symm ht.choose_spec.choose_spec.choose

private theorem walkingEquivalenceLift_comp_eq_of_isNondegenerate {t : diagram P V} {B : Atom}
    (π : V ⟶ B) (σ : diagram P B) (hπ : IsSplitEpi π) (hσ : EZCategory.IsNondegenerate P σ)
    (hπσ : P.map π.op σ = t) (hB : B.dimension < V.dimension) {W : Atom} (p : V ⟶ W)
    (hW : W.dimension < V.dimension) (y : diagram P W) (hy : P.map p.op y = t) :
    walkingEquivalenceLift hV p hW ≫ uliftYonedaEquiv.symm y =
      walkingEquivalenceLift hV π hB ≫ uliftYonedaEquiv.symm σ := by
  let x := p V.top
  let c := principalLift W x p (apply_mem_closure_apply_top p)
  let i := Atom.closureIncl W x
  have hci : c ≫ i = p := principalLift_comp_closureIncl _ _ _ _
  have hc : IsCollapseHom c := isCollapseHom_of_apply_eq_top _ (principalLift_apply_top p)
  have h₀ : (Atom.ofClosure W x).dimension < V.dimension := by
    rw [Atom.dimension_ofClosure]
    exact ((grade_mono (W.le_top x)).trans_eq W.dimension_eq.symm).trans_lt hW
  obtain ⟨Z, q, z, hq, hz, hqz⟩ := EZCategory.exists_isNondegenerate P _ (P.map i.op y)
  have hZ : Z.dimension < V.dimension :=
    (dimension_le_of_isCollapseHom q (@isCollapseHom_of_isSplitEpi _ _ q hq)).trans_lt h₀
  have hcq : IsSplitEpi (c ≫ q) := IsSplitEpi.mk'
    ((isSplitEpi_of_isCollapseHom c hc).exists_splitEpi.some.comp hq.exists_splitEpi.some)
  have ht : P.map (c ≫ q).op z = P.map π.op σ :=
    (Functor.map_comp_apply P q.op c.op z).trans ((congrArg (P.map c.op) hqz).trans
      ((Functor.map_comp_apply P i.op c.op y).symm.trans
        ((congrArg (fun r => P.map r.op y) hci).trans (hy.trans hπσ.symm))))
  obtain ⟨e, ⟨he₁, he₂⟩, -⟩ :=
    EZCategory.existsUnique_iso_of_isNondegenerate P (c ≫ q) π z σ hcq hz hπ hσ ht
  exact (congrArg (fun r => walkingEquivalenceLift hV r hW ≫ uliftYonedaEquiv.symm y)
    hci.symm).trans
    ((congrArg (· ≫ uliftYonedaEquiv.symm y) (walkingEquivalenceLift_comp hV c i h₀ hW).symm).trans
    ((Category.assoc _ _ _).trans
    ((congrArg (walkingEquivalenceLift hV c h₀ ≫ ·) (uliftYonedaEquiv_symm_map i.op y).symm).trans
    ((congrArg (fun w => walkingEquivalenceLift hV c h₀ ≫ uliftYonedaEquiv.symm w) hqz.symm).trans
    ((congrArg (walkingEquivalenceLift hV c h₀ ≫ ·)
      (uliftYonedaEquiv_symm_map q.op z)).trans
    ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ uliftYonedaEquiv.symm z) (walkingEquivalenceLift_comp hV c q h₀ hZ)).trans
    ((congrArg (walkingEquivalenceLift hV (c ≫ q) hZ ≫ ·)
      ((congrArg uliftYonedaEquiv.symm he₂.symm).trans
        (uliftYonedaEquiv_symm_map e.hom.op σ))).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ uliftYonedaEquiv.symm σ)
      ((walkingEquivalenceLift_comp hV (c ≫ q) e.hom hZ hB).trans
        (congrArg (fun r => walkingEquivalenceLift hV r hB) he₁))))))))))))

theorem degenerateCellLift_eq (t : diagram P V) (ht : IsDegenerate P t) {W : Atom} (p : V ⟶ W)
    (hW : W.dimension < V.dimension) (y : diagram P W) (hy : P.map p.op y = t) :
    degenerateCellLift hV t ht = walkingEquivalenceLift hV p hW ≫ uliftYonedaEquiv.symm y := by
  obtain ⟨B, π, σ, hπ, hσ, hπσ⟩ := EZCategory.exists_isNondegenerate P V t
  have hB : B.dimension < V.dimension := by
    refine lt_of_le_of_ne (dimension_le_of_isCollapseHom π (@isCollapseHom_of_isSplitEpi _ _ π hπ))
      fun h => ?_
    have := isIso_of_isCollapseHom_of_dimension_eq π (@isCollapseHom_of_isSplitEpi _ _ π hπ)
      h.symm
    exact (isDegenerate_iff_not_isNondegenerate P t).1 ht
      (hπσ ▸ (isDegenerate_iff_not_isNondegenerate P _).not_left.1
        ((isDegenerate_map_iso_iff (asIso π) σ).not.2
          ((isDegenerate_iff_not_isNondegenerate P σ).not_left.2 hσ)))
  exact (walkingEquivalenceLift_comp_eq_of_isNondegenerate hV π σ hπ hσ hπσ hB _ _ _
    ht.choose_spec.choose_spec.choose_spec.2.2).trans
    (walkingEquivalenceLift_comp_eq_of_isNondegenerate hV π σ hπ hσ hπσ hB p hW y hy).symm

@[reassoc (attr := simp)]
theorem toWalkingEquivalence_degenerateCellLift (t : diagram P V) (ht : IsDegenerate P t) :
    toWalkingEquivalence V hV ≫ degenerateCellLift hV t ht = uliftYonedaEquiv.symm t :=
  (toWalkingEquivalence_walkingEquivalenceLift_assoc hV _ _ _).trans
    ((uliftYonedaEquiv_symm_map ht.choose_spec.choose.op _).symm.trans
      (congrArg uliftYonedaEquiv.symm ht.choose_spec.choose_spec.choose_spec.2.2))

theorem degenerateLift_comp_yonedaEquiv_symm {W : Atom} (g : V ⟶ W)
    (hg : atomMarking.Degenerate g) (t : diagram P W) (ht : IsDegenerate P (P.map g.op t)) :
    degenerateLift hV g hg ≫ uliftYonedaEquiv.symm t = degenerateCellLift hV _ ht := by
  have hW : (Atom.ofClosure W (g V.top)).dimension < V.dimension := by
    rw [Atom.dimension_ofClosure]
    exact grade_apply_top_lt_of_degenerate hg
  have hy : P.map (principalLift W (g V.top) g (apply_mem_closure_apply_top g)).op
      (P.map (Atom.closureIncl W (g V.top)).op t) = P.map g.op t :=
    (Functor.map_comp_apply P _ _ t).symm.trans
      (congrArg (fun r : V ⟶ W => P.map r.op t) (principalLift_comp_closureIncl _ _ _ _))
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (uliftYonedaEquiv_symm_map (Atom.closureIncl W (g V.top)).op t).symm).trans
    (degenerateCellLift_eq hV _ ht _ hW _ hy).symm)

theorem walkingEquivalenceMap_degenerateCellLift {V' : Atom} (hV' : 0 < V'.dimension)
    (e : V' ≅ V) (t : diagram P V) (ht : IsDegenerate P t)
    (ht' : IsDegenerate P (P.map e.hom.op t)) :
    walkingEquivalenceMap hV hV' e ≫ degenerateCellLift hV t ht =
      degenerateCellLift hV' _ ht' := by
  have hW := dimension_lt_of_isDegenerate ht
  have hW' : ht.choose.dimension < V'.dimension := by
    rw [Atom.dimension_eq_of_iso e]
    exact hW
  have hy : P.map (e.hom ≫ ht.choose_spec.choose).op ht.choose_spec.choose_spec.choose =
      P.map e.hom.op t :=
    (Functor.map_comp_apply P _ _ _).trans
      (congrArg (P.map e.hom.op) ht.choose_spec.choose_spec.choose_spec.2.2)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (walkingEquivalenceLift_unique hV' hW' _
      ((toWalkingEquivalence_walkingEquivalenceMap_assoc hV hV' e _).trans
        ((congrArg (_ ≫ ·) (toWalkingEquivalence_walkingEquivalenceLift hV _ _)).trans
          (uliftYoneda.{u}.map_comp _ _).symm))).symm).trans
    (degenerateCellLift_eq hV' _ ht' _ hW' _ hy).symm)

end DegenerateCell

end Atoms.Diagrammatic
