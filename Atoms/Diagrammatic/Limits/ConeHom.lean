import Atoms.Diagrammatic.Limits.GrayHomBoundary
import Atoms.Diagrammatic.Suspension.Quillen

open CategoryTheory Limits Opposite Simplicial Atoms.Shape HomotopicalAlgebra

universe u

namespace Atoms.Diagrammatic

variable {K X Y : DiagSet.{u}}

noncomputable def coneVertex (α : Bool) (d : K ⟶ X) (l : X.Vertex)
    (e : ((grayHomRight K).obj X).Edge
      (cond α (l.map (constDiagram K X)) (diagramVertex d))
      (cond α (diagramVertex d) (l.map (constDiagram K X)))) :
    (coneObject α d).Vertex :=
  (coneObjectVerticesEquiv α d).symm ⟨l, e⟩

@[simp]
theorem coneObjectπ_coneVertex (α : Bool) (d : K ⟶ X) (l : X.Vertex)
    (e : ((grayHomRight K).obj X).Edge
      (cond α (l.map (constDiagram K X)) (diagramVertex d))
      (cond α (diagramVertex d) (l.map (constDiagram K X)))) :
    (coneVertex α d l e).map (coneObjectπ α d) = l :=
  (coneObjectVerticesEquiv_fst α d _).symm.trans
    (congrArg Sigma.fst (Equiv.apply_symm_apply (coneObjectVerticesEquiv α d) ⟨l, e⟩))

theorem isLimitCone_coneVertex_iff (α : Bool) (d : K ⟶ X) (l : X.Vertex)
    (e : ((grayHomRight K).obj X).Edge
      (cond α (l.map (constDiagram K X)) (diagramVertex d))
      (cond α (diagramVertex d) (l.map (constDiagram K X)))) :
    IsLimitCone α d (coneVertex α d l e) ↔ ∀ t μ,
      (bipointedHom.obj ((coneObject α d).bipoint
        (cond α (coneVertex α d t μ) (coneVertex α d l e))
        (cond α (coneVertex α d l e) (coneVertex α d t μ)))).IsContractible := by
  refine ⟨fun h t μ => h _, fun h v => ?_⟩
  obtain ⟨⟨t, μ⟩, rfl⟩ := (coneObjectVerticesEquiv α d).symm.surjective v
  exact h t μ

theorem isPullback_bipointedHom_map {P X' Y' Z : Under pointPair.{u}} {fst : P ⟶ X'}
    {snd : P ⟶ Y'} {f : X' ⟶ Z} {g : Y' ⟶ Z} (w : fst ≫ f = snd ≫ g)
    (h : IsPullback fst.right snd.right f.right g.right) :
    IsPullback (bipointedHom.map fst) (bipointedHom.map snd) (bipointedHom.map f)
      (bipointedHom.map g) := by
  have : ReflectsLimit (cospan f g) (Under.forget pointPair.{u}) := inferInstance
  have hU : IsPullback fst snd f g := IsPullback.of_map (Under.forget _) w h
  have := bipointedSuspensionAdjunction.{u}.rightAdjoint_preservesLimits
  exact hU.map bipointedHom

noncomputable def coneObjectBaseBipointMap (α : Bool) (d : K ⟶ X)
    (v w : (coneObject α d).Vertex) :
    X.bipoint (v.map (coneObjectπ α d))
        (w.map (coneObjectπ α d)) ⟶
      ((grayHomRight intervalBoundary.{u}).obj ((grayHomRight K).obj X)).bipoint
        (v.map (coneObjectι α d ≫
          (grayHomRestrict intervalBoundaryι).app ((grayHomRight K).obj X)))
        (w.map (coneObjectι α d ≫
          (grayHomRestrict intervalBoundaryι).app ((grayHomRight K).obj X))) :=
  have h (x : (coneObject α d).Vertex) :
      vertexHom (x.map (coneObjectπ α d)) ≫ coneObjectBase α d =
        vertexHom (x.map (coneObjectι α d ≫
          (grayHomRestrict intervalBoundaryι).app ((grayHomRight K).obj X))) := by
    rw [← vertexHom_comp, ← vertexHom_comp, Category.assoc, (isPullback_coneObject α d).w]
  Under.homMk (coneObjectBase α d) (coprod.hom_ext
    (by simp only [DiagSet.bipoint, Under.mk_hom, coprod.inl_desc_assoc, coprod.inl_desc, h])
    (by simp only [DiagSet.bipoint, Under.mk_hom, coprod.inr_desc_assoc, coprod.inr_desc, h]))

@[simp]
theorem coneObjectBaseBipointMap_right (α : Bool) (d : K ⟶ X)
    (v w : (coneObject α d).Vertex) :
    (coneObjectBaseBipointMap α d v w).right = coneObjectBase α d :=
  rfl

theorem isPullback_bipointedHom_coneObject (α : Bool) (d : K ⟶ X)
    (v w : (coneObject α d).Vertex) :
    IsPullback (bipointedHom.map (DiagSet.bipointMap (coneObjectι α d) v w))
      (bipointedHom.map (DiagSet.bipointMap (coneObjectπ α d) v w))
      (bipointedHom.map (DiagSet.bipointMap
        ((grayHomRestrict intervalBoundaryι).app ((grayHomRight K).obj X)) _ _))
      (bipointedHom.map (coneObjectBaseBipointMap α d v w)) :=
  isPullback_bipointedHom_map (Under.UnderMorphism.ext (isPullback_coneObject α d).w)
    (isPullback_coneObject α d)

theorem fibration_bipointedHom_coneObjectπ (α : Bool) (d : K ⟶ X) (hX : IsInftyCategory 1 X)
    (v w : (coneObject α d).Vertex) :
    Fibration ((DiagSet.toInfty 0).map
      (bipointedHom.map (DiagSet.bipointMap (coneObjectπ α d) v w))) :=
  have := fibration_coneObjectπ α d hX
  DiagSet.fibration_bipointedHom_map _ v w

noncomputable abbrev coneHomFibre (α : Bool) (d : K ⟶ X)
    (v w : (coneObject α d).Vertex)
    (f : (bipointedHom.obj (X.bipoint
      (v.map (coneObjectπ α d))
      (w.map (coneObjectπ α d)))).Vertex) : DiagSet.{u} :=
  pullback (bipointedHom.map (DiagSet.bipointMap (coneObjectπ α d) v w)) (vertexHom f)

theorem isInftyCategory_zero_coneHomFibre (α : Bool) (d : K ⟶ X) (hX : IsInftyCategory 1 X)
    (v w : (coneObject α d).Vertex)
    (f : (bipointedHom.obj (X.bipoint
      (v.map (coneObjectπ α d))
      (w.map (coneObjectπ α d)))).Vertex) :
    IsInftyCategory 0 (coneHomFibre α d v w f) := by
  have := fibration_bipointedHom_coneObjectπ α d hX v w
  have h : IsPullback (C := DiagSet.Infty.{u} 0) ((DiagSet.toInfty 0).map (pullback.fst _ _))
      ((DiagSet.toInfty 0).map (pullback.snd
        (bipointedHom.map (DiagSet.bipointMap (coneObjectπ α d) v w)) (vertexHom f)))
      ((DiagSet.toInfty 0).map (bipointedHom.map (DiagSet.bipointMap (coneObjectπ α d) v w)))
      ((DiagSet.toInfty 0).map (vertexHom f)) :=
    IsPullback.of_hasPullback _ _
  have hsnd : Fibration ((DiagSet.toInfty 0).map (pullback.snd
      (bipointedHom.map (DiagSet.bipointMap (coneObjectπ α d) v w)) (vertexHom f))) :=
    (fibration_iff _).2 (MorphismProperty.of_isPullback h ((fibration_iff _).1 inferInstance))
  exact (isFibrant_infty_iff 0 _).1 ((isFibrant_iff_of_isTerminal ((DiagSet.toInfty 0).map
    (pullback.snd (bipointedHom.map (DiagSet.bipointMap (coneObjectπ α d) v w)) (vertexHom f)))
    isTerminalBallAtomPoint).2 hsnd)

theorem isPullback_coneHomFibre (α : Bool) (d : K ⟶ X)
    (v w : (coneObject α d).Vertex)
    (f : (bipointedHom.obj (X.bipoint
      (v.map (coneObjectπ α d))
      (w.map (coneObjectπ α d)))).Vertex) :
    IsPullback (pullback.fst _ _ ≫ bipointedHom.map (DiagSet.bipointMap (coneObjectι α d) v w))
      (pullback.snd (bipointedHom.map (DiagSet.bipointMap (coneObjectπ α d) v w)) (vertexHom f))
      (bipointedHom.map (DiagSet.bipointMap
        ((grayHomRestrict intervalBoundaryι).app ((grayHomRight K).obj X)) _ _))
      (vertexHom f ≫ bipointedHom.map (coneObjectBaseBipointMap α d v w)) :=
  (IsPullback.of_hasPullback _ _).paste_horiz (isPullback_bipointedHom_coneObject α d v w)

private theorem rlp_monomorphisms_grayHomRight_map {F : X ⟶ Y}
    (hF : (MorphismProperty.monomorphisms DiagSet.{u}).rlp F) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp ((grayHomRight K).map F) := by
  intro A B j hj
  have : Mono j := hj
  have : Mono ((grayTensorRight K).map j) := by
    rw [grayTensorRight_map_eq]
    infer_instance
  exact ((grayTensorRightAdjunction K).hasLiftingProperty_iff j F).1
    (hF _ (MorphismProperty.monomorphisms.infer_property _))

theorem rlp_monomorphisms_coneObjectMap (α : Bool) (d : K ⟶ X) {F : X ⟶ Y}
    (hF : (MorphismProperty.monomorphisms DiagSet.{u}).rlp F) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp (coneObjectMap α d F) := by
  intro T' T j hj
  let sq := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u} intervalBoundaryι
    ((grayHomRight K).map F)
  have := hF j hj
  have hL : HasLiftingProperty j sq.π := rlp_monomorphisms_grayHomRight_pullbackObjObj
    intervalBoundaryι (rlp_monomorphisms_grayHomRight_map (K := K) hF) j hj
  refine ⟨fun {a b} s => ?_⟩
  have s₁ : CommSq (a ≫ coneObjectπ α d) j F (b ≫ coneObjectπ α (d ≫ F)) :=
    ⟨by rw [Category.assoc, ← coneObjectMap_π, reassoc_of% s.w]⟩
  have hb : (s₁.lift ≫ coneObjectBase α d) ≫
      (grayHomRight intervalBoundary.{u}).map ((grayHomRight K).map F) =
      (b ≫ coneObjectι α (d ≫ F)) ≫ (grayHomRestrict intervalBoundaryι).app _ := by
    rw [Category.assoc, coneObjectBase_comp, reassoc_of% s₁.fac_right, Category.assoc]
    exact congrArg (b ≫ ·) (isPullback_coneObject α (d ≫ F)).w.symm
  have s₂ : CommSq (a ≫ coneObjectι α d) j sq.π (sq.isPullback.lift _ _ hb) := by
    refine ⟨sq.isPullback.hom_ext ?_ ?_⟩
    · refine (Category.assoc _ _ _).trans ((congrArg _ sq.π_fst).trans ?_)
      refine Eq.trans ?_ (congrArg (j ≫ ·) (sq.isPullback.lift_fst _ _ hb)).symm
      refine (Category.assoc _ _ _).trans
        ((congrArg (a ≫ ·) (isPullback_coneObject α d).w).trans ?_)
      rw [← reassoc_of% s₁.fac_left]
      rfl
    · refine (Category.assoc _ _ _).trans ((congrArg _ sq.π_snd).trans ?_)
      refine Eq.trans ?_ (congrArg (j ≫ ·) (sq.isPullback.lift_snd _ _ hb)).symm
      exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (coneObjectMap_ι α d F)).symm.trans
        ((reassoc_of% s.w) (coneObjectι α (d ≫ F))))
  have : s₂.HasLift := hL.sq_hasLift s₂
  have hl : s₂.lift ≫ (grayHomRestrict intervalBoundaryι).app _ = s₁.lift ≫ coneObjectBase α d :=
    (congrArg (s₂.lift ≫ ·) sq.π_fst.symm).trans (((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ sq.fst) s₂.fac_right)).trans (sq.isPullback.lift_fst _ _ hb))
  refine ⟨⟨⟨(isPullback_coneObject α d).lift s₂.lift s₁.lift hl, ?_, ?_⟩⟩⟩
  · refine coneObject_hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.lift_fst, s₂.fac_left]
    · rw [Category.assoc, IsPullback.lift_snd, s₁.fac_left]
  · refine coneObject_hom_ext ?_ ?_
    · rw [Category.assoc, coneObjectMap_ι, reassoc_of% IsPullback.lift_fst]
      exact (congrArg (s₂.lift ≫ ·) sq.π_snd.symm).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ sq.snd) s₂.fac_right)).trans (sq.isPullback.lift_snd _ _ hb))
    · rw [Category.assoc, coneObjectMap_π, reassoc_of% IsPullback.lift_snd, s₁.fac_right]

private theorem isLimitCone_app_iff_of_eq {α : Bool} {T : DiagSet.{u}} {d d' : K ⟶ X} (h : d = d')
    (φ : T ⟶ coneObject α d) (ψ : T ⟶ coneObject α d')
    (hι : ψ ≫ coneObjectι α d' = φ ≫ coneObjectι α d)
    (hπ : ψ ≫ coneObjectπ α d' = φ ≫ coneObjectπ α d) (v : T.Vertex) :
    IsLimitCone α d' (v.map ψ) ↔
      IsLimitCone α d (v.map φ) := by
  subst h
  obtain rfl : ψ = φ := coneObject_hom_ext hι hπ
  rfl

private theorem isLimitCone_coneObjectMap_iff_of_rlp (α : Bool) (d : K ⟶ X)
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) {F : X ⟶ Y}
    (hF : (MorphismProperty.monomorphisms DiagSet.{u}).rlp F)
    (v : (coneObject α d).Vertex) :
    IsLimitCone α (d ≫ F) (v.map (coneObjectMap α d F)) ↔
      IsLimitCone α d v :=
  have := weakEquivalence_toInfty_map_of_rlp_monomorphisms 1
    (rlp_monomorphisms_coneObjectMap α d hF)
  DiagSet.hasContractibleHoms_map_iff (isInftyCategory_coneObject α d hX)
    (isInftyCategory_coneObject α (d ≫ F) hY) _ α v

private theorem isLimitCone_coneObjectMap_iff_of_fac (α : Bool) (d : K ⟶ X) {Z : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) (hZ : IsInftyCategory 1 Z) {F : X ⟶ Y}
    {i : X ⟶ Z} {p : Z ⟶ Y} {r : Z ⟶ X} (hir : i ≫ r = 𝟙 X) (hip : i ≫ p = F)
    (hr : (MorphismProperty.monomorphisms DiagSet.{u}).rlp r)
    (hp : (MorphismProperty.monomorphisms DiagSet.{u}).rlp p)
    (v : (coneObject α d).Vertex) :
    IsLimitCone α (d ≫ F) (v.map (coneObjectMap α d F)) ↔
      IsLimitCone α d v := by
  have hdr : d = (d ≫ i) ≫ r := by rw [Category.assoc, hir, Category.comp_id]
  have hdp : d ≫ F = (d ≫ i) ≫ p := by rw [Category.assoc, hip]
  have er := isLimitCone_app_iff_of_eq hdr (𝟙 _)
    (coneObjectMap α d i ≫ coneObjectMap α (d ≫ i) r)
    (by rw [Category.assoc, coneObjectMap_ι, coneObjectMap_ι_assoc, ← Functor.map_comp,
      ← Functor.map_comp, hir, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.comp_id, Category.id_comp])
    (by rw [Category.assoc, coneObjectMap_π, coneObjectMap_π_assoc, hir, Category.comp_id,
      Category.id_comp]) v
  have ep := isLimitCone_app_iff_of_eq hdp (coneObjectMap α d F)
    (coneObjectMap α d i ≫ coneObjectMap α (d ≫ i) p)
    (by rw [Category.assoc, coneObjectMap_ι, coneObjectMap_ι_assoc, coneObjectMap_ι,
      ← Functor.map_comp, ← Functor.map_comp, hip])
    (by rw [Category.assoc, coneObjectMap_π, coneObjectMap_π_assoc, coneObjectMap_π, hip]) v
  rw [DiagSet.Vertex.map_comp, DiagSet.Vertex.map_id] at er
  rw [DiagSet.Vertex.map_comp] at ep
  refine ep.symm.trans ((isLimitCone_coneObjectMap_iff_of_rlp α (d ≫ i) hZ hY hp _).trans
    ((isLimitCone_coneObjectMap_iff_of_rlp α (d ≫ i) hZ hX hr _).symm.trans (er.trans ?_)))
  rfl

theorem isLimitCone_coneObjectMap_iff (α : Bool) (d : K ⟶ X) (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (F : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map F)]
    (v : (coneObject α d).Vertex) :
    IsLimitCone α (d ≫ F) (v.map (coneObjectMap α d F)) ↔
      IsLimitCone α d v := by
  have := (isFibrant_infty_iff 1 ((DiagSet.toInfty 1).obj X)).2 hX
  have := (isFibrant_infty_iff 1 ((DiagSet.toInfty 1).obj Y)).2 hY
  obtain ⟨h⟩ : Nonempty (FibrantBrownFactorization ((DiagSet.toInfty 1).map F)) := inferInstance
  have : Fibration h.p := (fibration_iff _).2 h.hp
  have hZ : IsInftyCategory 1 h.Z := (isFibrant_infty_iff 1 h.Z).1 (isFibrant_of_fibration h.p)
  have : Fibration ((DiagSet.toInfty 1).map (h.r : (h.Z : DiagSet.{u}) ⟶ X)) := h.fibration_r
  have : WeakEquivalence ((DiagSet.toInfty 1).map (h.r : (h.Z : DiagSet.{u}) ⟶ X)) :=
    inferInstanceAs (WeakEquivalence h.r)
  have : WeakEquivalence ((DiagSet.toInfty 1).map (h.p : (h.Z : DiagSet.{u}) ⟶ Y)) :=
    inferInstanceAs (WeakEquivalence h.p)
  have : Fibration ((DiagSet.toInfty 1).map (h.p : (h.Z : DiagSet.{u}) ⟶ Y)) :=
    inferInstanceAs (Fibration h.p)
  exact isLimitCone_coneObjectMap_iff_of_fac α d (Z := h.Z) hX hY hZ (i := h.i) (p := h.p)
    (r := h.r) h.i_r h.fac (rlp_monomorphisms_of_trivialFibration_toInfty_map 1 (g := h.r))
    (rlp_monomorphisms_of_trivialFibration_toInfty_map 1 (g := h.p)) v

theorem IsLimitCone.of_isEquivalence {α : Bool} {d : K ⟶ X} (hX : IsInftyCategory 1 X)
    {v v' : (coneObject α d).Vertex} (e : (coneObject α d).Edge v v')
    (he : IsEquivalence (coneObject α d) e.cell) (hv : IsLimitCone α d v) : IsLimitCone α d v' :=
  (DiagSet.hasContractibleHoms_iff_of_isEquivalence (isInftyCategory_coneObject α d hX) α e he).1 hv

theorem isPullback_coneHomFibre_prod (α : Bool) (d : K ⟶ X)
    (v w : (coneObject α d).Vertex)
    (f : (bipointedHom.obj (X.bipoint
      (v.map (coneObjectπ α d))
      (w.map (coneObjectπ α d)))).Vertex) :
    IsPullback (pullback.fst _ _ ≫ bipointedHom.map (DiagSet.bipointMap (coneObjectι α d) v w))
      (pullback.snd (bipointedHom.map (DiagSet.bipointMap (coneObjectπ α d) v w)) (vertexHom f))
      (bipointedHom.map (DiagSet.bipointMap
        ((grayHomRestrict intervalBoundaryι).app ((grayHomRight K).obj X)) _ _) ≫
        (bipointedHomBoundaryIso _ _ _).hom)
      (vertexHom f ≫ bipointedHom.map (coneObjectBaseBipointMap α d v w) ≫
        (bipointedHomBoundaryIso _ _ _).hom) :=
  (isPullback_coneHomFibre α d v w f).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (bipointedHomBoundaryIso _ _ _) (by simp only [Iso.refl_hom, Category.comp_id,
      Category.id_comp]) (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (Category.id_comp _).symm (by simp only [Iso.refl_hom, Category.assoc, Category.id_comp]; rfl)

private theorem toSSet_map_diagramPoint_app (d : K ⟶ X) (e : (DiagSet.toSSet.obj X) _⦋1⦌) :
    (DiagSet.toSSet.map (isTerminalBallAtomPoint.from X ≫ diagramPoint d)).app _ e =
      (DiagSet.toSSet.obj ((grayHomRight K).obj X)).σ 0
        (DiagSet.vertexEquivSSet _ (diagramVertex d)) := by
  have h : (DiagSet.toSSet.map (isTerminalBallAtomPoint.from X)).app _ e =
      (DiagSet.toSSet.obj (ball.{u} atomPoint)).σ 0
        (uliftYonedaEquiv (X := atomSimplex 0) (F := ball.{u} atomPoint)
          (isTerminalBallAtomPoint.from (ball.{u} atomPoint))) :=
    ULift.ext _ _ (isTerminalAtomPoint.hom_ext _ _)
  rw [Functor.map_comp, NatTrans.comp_app, types_comp_apply, h]
  exact NatTrans.naturality_apply (DiagSet.toSSet.map (diagramPoint d)) _ _

private theorem bipointedHomVerticesEquiv_coneObjectBase_edge (α : Bool) (d : K ⟶ X)
    (v w : (coneObject α d).Vertex)
    (f : (bipointedHom.obj (X.bipoint
      (v.map (coneObjectπ α d))
      (w.map (coneObjectπ α d)))).Vertex) {B : DiagSet.{u}}
    (ev : (grayHomRight intervalBoundary.{u}).obj ((grayHomRight K).obj X) ⟶ B) :
    (DiagSet.edgeEquivSSet (DiagSet.bipointedHomVerticesEquiv _ _
      ((DiagSet.vertexEquivSSet _).symm ((DiagSet.toSSet.map
      (bipointedHom.map (coneObjectBaseBipointMap α d v w) ≫
        bipointedHom.map (DiagSet.bipointMap ev _ _))).app _ f)))).edge =
      (DiagSet.toSSet.map (coneObjectBase α d ≫ ev)).app _
        (DiagSet.edgeEquivSSet (DiagSet.bipointedHomVerticesEquiv _ _
          ((DiagSet.vertexEquivSSet _).symm f))).edge := by
  rw [DiagSet.bipointedHomVerticesEquiv_edge, DiagSet.bipointedHomVerticesEquiv_edge]
  exact (NatTrans.naturality_apply (coneObjectBase α d ≫ ev) _ _).symm

theorem coneObjectBase_fst_edge (α : Bool) (d : K ⟶ X)
    (v w : (coneObject α d).Vertex)
    (f : (bipointedHom.obj (X.bipoint
      (v.map (coneObjectπ α d))
      (w.map (coneObjectπ α d)))).Vertex) :
    (DiagSet.edgeEquivSSet (DiagSet.bipointedHomVerticesEquiv _ _
      ((DiagSet.vertexEquivSSet _).symm ((DiagSet.toSSet.map
      ((bipointedHom.map (coneObjectBaseBipointMap α d v w) ≫
        (bipointedHomBoundaryIso _ _ _).hom) ≫ prod.fst)).app _ f)))).edge =
      cond α ((DiagSet.toSSet.map (constDiagram K X)).app _
          (DiagSet.edgeEquivSSet (DiagSet.bipointedHomVerticesEquiv _ _
          ((DiagSet.vertexEquivSSet _).symm f))).edge)
        ((DiagSet.toSSet.obj ((grayHomRight K).obj X)).σ 0
        (DiagSet.vertexEquivSSet _ (diagramVertex d))) := by
  rw [Category.assoc, bipointedHomBoundaryIso_hom_fst]
  refine (bipointedHomVerticesEquiv_coneObjectBase_edge α d v w f _).trans ?_
  refine (congrArg (fun g => (DiagSet.toSSet.map g).app _
      (X.edgeEquivSSet (X.bipointedHomVerticesEquiv _ _ ((DiagSet.vertexEquivSSet _).symm f))).edge)
    (coneObjectBase_comp_grayHomBoundaryFan_fst α d)).trans ?_
  cases α
  · exact toSSet_map_diagramPoint_app d _
  · rfl

theorem coneObjectBase_snd_edge (α : Bool) (d : K ⟶ X)
    (v w : (coneObject α d).Vertex)
    (f : (bipointedHom.obj (X.bipoint
      (v.map (coneObjectπ α d))
      (w.map (coneObjectπ α d)))).Vertex) :
    (DiagSet.edgeEquivSSet (DiagSet.bipointedHomVerticesEquiv _ _
      ((DiagSet.vertexEquivSSet _).symm ((DiagSet.toSSet.map
      ((bipointedHom.map (coneObjectBaseBipointMap α d v w) ≫
        (bipointedHomBoundaryIso _ _ _).hom) ≫ prod.snd)).app _ f)))).edge =
      cond α ((DiagSet.toSSet.obj ((grayHomRight K).obj X)).σ 0
        (DiagSet.vertexEquivSSet _ (diagramVertex d)))
        ((DiagSet.toSSet.map (constDiagram K X)).app _
          (DiagSet.edgeEquivSSet (DiagSet.bipointedHomVerticesEquiv _ _
          ((DiagSet.vertexEquivSSet _).symm f))).edge) := by
  rw [Category.assoc, bipointedHomBoundaryIso_hom_snd]
  refine (bipointedHomVerticesEquiv_coneObjectBase_edge α d v w f _).trans ?_
  refine (congrArg (fun g => (DiagSet.toSSet.map g).app _
      (X.edgeEquivSSet (X.bipointedHomVerticesEquiv _ _ ((DiagSet.vertexEquivSSet _).symm f))).edge)
    (coneObjectBase_comp_grayHomBoundaryFan_snd α d)).trans ?_
  cases α
  · rfl
  · exact toSSet_map_diagramPoint_app d _

end Atoms.Diagrammatic
