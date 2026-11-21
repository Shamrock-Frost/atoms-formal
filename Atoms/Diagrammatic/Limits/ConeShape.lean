import Atoms.Diagrammatic.Limits.ProductPullback
import Atoms.Diagrammatic.Limits.ConeHom

open CategoryTheory Limits Opposite Simplicial Atoms.Shape HomotopicalAlgebra

universe u

namespace Atoms.Diagrammatic

variable {K K' X : DiagSet.{u}}

private noncomputable def isTerminalGrayHomRightTerminal (K : DiagSet.{u}) :
    IsTerminal ((grayHomRight K).obj (⊤_ DiagSet.{u})) :=
  have := (grayTensorRightAdjunction K).rightAdjoint_preservesLimits
  terminalIsTerminal.isTerminalObj (grayHomRight K) _

theorem rlp_monomorphisms_grayHomRestrict (k : K' ⟶ K) [Mono k]
    [WeakEquivalence ((DiagSet.toInfty 1).map k)] (hX : IsInftyCategory 1 X) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp ((grayHomRestrict k).app X) := by
  have : Fibration ((DiagSet.toInfty 1).map (terminal.from X)) :=
    (isFibrant_iff_of_isTerminal _ terminalIsTerminal).1 ((isFibrant_infty_iff 1 _).2 hX)
  let sq := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u} k (terminal.from X)
  have : IsIso sq.fst := sq.isPullback.isIso_fst_of_isIso
    (isIso_of_isTerminal (isTerminalGrayHomRightTerminal K) (isTerminalGrayHomRightTerminal K') _)
  have : WeakEquivalence ((DiagSet.toInfty 1).map sq.π) :=
    weakEquivalence_toInfty_one_grayHomRight_pullbackObjObj k (terminal.from X)
      (Or.inl inferInstance)
  have : Fibration ((DiagSet.toInfty 1).map ((grayHomRestrict k).app X)) :=
    fibration_toInfty_one_grayHomRestrict k hX
  have : WeakEquivalence ((DiagSet.toInfty 1).map ((grayHomRestrict k).app X)) := by
    have h : (DiagSet.toInfty 1).map ((grayHomRestrict k).app X) =
        (DiagSet.toInfty 1).map sq.π ≫ (DiagSet.toInfty 1).map sq.fst := by
      rw [← Functor.map_comp]
      exact congrArg _ sq.π_fst.symm
    have : WeakEquivalence ((DiagSet.toInfty 1).map sq.fst) :=
      (weakEquivalence_iff _).2 ((weakEquivalences _).of_isIso _)
    rw [h]
    exact (weakEquivalence_iff _).2 ((weakEquivalences _).comp_mem _ _
      ((weakEquivalence_iff _).1 ‹_›) ((weakEquivalence_iff _).1 ‹_›))
  exact rlp_monomorphisms_of_trivialFibration_toInfty_map 1

theorem rlp_monomorphisms_coneObjectRestrict (α : Bool) (hX : IsInftyCategory 1 X)
    {k : K' ⟶ K} [Mono k] [WeakEquivalence ((DiagSet.toInfty 1).map k)] {d : K ⟶ X}
    {d' : K' ⟶ X} (h : k ≫ d = d') :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp (coneObjectRestrict α k h) := by
  intro T' T j hj
  let sq := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u} intervalBoundaryι
    ((grayHomRestrict k).app X)
  have hL : HasLiftingProperty j sq.π := rlp_monomorphisms_grayHomRight_pullbackObjObj
    intervalBoundaryι (rlp_monomorphisms_grayHomRestrict k hX) j hj
  refine ⟨fun {a b} s => ?_⟩
  have hb : ((b ≫ coneObjectπ α d') ≫ coneObjectBase α d) ≫
      (grayHomRight intervalBoundary.{u}).map ((grayHomRestrict k).app X) =
      (b ≫ coneObjectι α d') ≫ (grayHomRestrict intervalBoundaryι).app _ := by
    rw [Category.assoc, Category.assoc, coneObjectBase_comp_grayHomRestrict α k h,
      Category.assoc, (isPullback_coneObject α d').w]
  have hπ : a ≫ coneObjectπ α d = j ≫ b ≫ coneObjectπ α d' := by
    rw [← coneObjectRestrict_π α k h, reassoc_of% s.w]
  have s₂ : CommSq (a ≫ coneObjectι α d) j sq.π (sq.isPullback.lift _ _ hb) := by
    refine ⟨sq.isPullback.hom_ext ?_ ?_⟩
    · refine (Category.assoc _ _ _).trans ((congrArg _ sq.π_fst).trans ?_)
      refine Eq.trans ?_ (congrArg (j ≫ ·) (sq.isPullback.lift_fst _ _ hb)).symm
      refine (Category.assoc _ _ _).trans
        ((congrArg (a ≫ ·) (isPullback_coneObject α d).w).trans ?_)
      rw [← Category.assoc, hπ, Category.assoc, Category.assoc]
      rfl
    · refine (Category.assoc _ _ _).trans ((congrArg _ sq.π_snd).trans ?_)
      refine Eq.trans ?_ (congrArg (j ≫ ·) (sq.isPullback.lift_snd _ _ hb)).symm
      exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (coneObjectRestrict_ι α k h)).symm.trans
        ((reassoc_of% s.w) (coneObjectι α d')))
  have : s₂.HasLift := hL.sq_hasLift s₂
  have hl : s₂.lift ≫ (grayHomRestrict intervalBoundaryι).app _ =
      (b ≫ coneObjectπ α d') ≫ coneObjectBase α d :=
    (congrArg (s₂.lift ≫ ·) sq.π_fst.symm).trans (((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ sq.fst) s₂.fac_right)).trans (sq.isPullback.lift_fst _ _ hb))
  refine ⟨⟨⟨(isPullback_coneObject α d).lift s₂.lift (b ≫ coneObjectπ α d') hl, ?_, ?_⟩⟩⟩
  · refine coneObject_hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.lift_fst, s₂.fac_left]
    · rw [Category.assoc, IsPullback.lift_snd, hπ]
  · refine coneObject_hom_ext ?_ ?_
    · rw [Category.assoc, coneObjectRestrict_ι, reassoc_of% IsPullback.lift_fst]
      exact (congrArg (s₂.lift ≫ ·) sq.π_snd.symm).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ sq.snd) s₂.fac_right)).trans (sq.isPullback.lift_snd _ _ hb))
    · rw [Category.assoc, coneObjectRestrict_π, IsPullback.lift_snd]

theorem coneObjectRestrict_congr (α : Bool) {k₁ k₂ : K' ⟶ K} (hk : k₁ = k₂) {d : K ⟶ X}
    {d' : K' ⟶ X} (h₁ : k₁ ≫ d = d') (h₂ : k₂ ≫ d = d') :
    coneObjectRestrict α k₁ h₁ = coneObjectRestrict α k₂ h₂ := by
  subst hk
  rfl

private theorem coneObjectRestrict_eq_id (α : Bool) {k : K ⟶ K} (hk : k = 𝟙 K) {d : K ⟶ X}
    (h : k ≫ d = d) : coneObjectRestrict α k h = 𝟙 _ :=
  (coneObjectRestrict_congr α hk h (Category.id_comp d)).trans (coneObjectRestrict_id α d)

theorem weakEquivalence_toInfty_one_coneObjectRestrict (α : Bool) (hX : IsInftyCategory 1 X)
    (k : K' ⟶ K) [WeakEquivalence ((DiagSet.toInfty 1).map k)] {d : K ⟶ X} {d' : K' ⟶ X}
    (h : k ≫ d = d') :
    WeakEquivalence ((DiagSet.toInfty 1).map (coneObjectRestrict α k h)) := by
  obtain ⟨b⟩ : Nonempty (CofibrantBrownFactorization ((DiagSet.toInfty 1).map k)) :=
    inferInstance
  let Z : DiagSet.{u} := b.Z
  let i : K' ⟶ Z := b.i
  let p : Z ⟶ K := b.p
  let s : K ⟶ Z := b.s
  have : Mono i := (cofibration_iff b.i).1 (cofibration_iff b.i |>.2 b.hi)
  have : Mono s := (cofibration_iff b.s).1 inferInstance
  have : WeakEquivalence ((DiagSet.toInfty 1).map i) := inferInstanceAs (WeakEquivalence b.i)
  have : WeakEquivalence ((DiagSet.toInfty 1).map s) := inferInstanceAs (WeakEquivalence b.s)
  have hip : i ≫ p = k := b.fac
  have hsp : s ≫ p = 𝟙 K := b.s_p
  have hi : i ≫ p ≫ d = d' := by rw [← Category.assoc, hip, h]
  have hs : s ≫ p ≫ d = d := by rw [← Category.assoc, hsp, Category.id_comp]
  have : WeakEquivalence ((DiagSet.toInfty 1).map (coneObjectRestrict α i hi)) :=
    weakEquivalence_toInfty_map_of_rlp_monomorphisms 1
      (rlp_monomorphisms_coneObjectRestrict α hX hi)
  have : WeakEquivalence ((DiagSet.toInfty 1).map (coneObjectRestrict α s hs)) :=
    weakEquivalence_toInfty_map_of_rlp_monomorphisms 1
      (rlp_monomorphisms_coneObjectRestrict α hX hs)
  have hps : (DiagSet.toInfty 1).map (coneObjectRestrict α p (d' := p ≫ d) rfl) ≫
      (DiagSet.toInfty 1).map (coneObjectRestrict α s hs) = 𝟙 _ := by
    rw [← Functor.map_comp, coneObjectRestrict_comp, coneObjectRestrict_eq_id α hsp]
    rfl
  have : WeakEquivalence ((DiagSet.toInfty 1).map (coneObjectRestrict α p (d' := p ≫ d) rfl)) := by
    have : WeakEquivalence ((DiagSet.toInfty 1).map (coneObjectRestrict α p (d' := p ≫ d) rfl) ≫
        (DiagSet.toInfty 1).map (coneObjectRestrict α s hs)) := by
      rw [hps]
      infer_instance
    exact weakEquivalence_of_postcomp _ ((DiagSet.toInfty 1).map (coneObjectRestrict α s hs))
  have hk : coneObjectRestrict α k h =
      coneObjectRestrict α p (d' := p ≫ d) rfl ≫ coneObjectRestrict α i hi := by
    rw [coneObjectRestrict_comp]
    exact coneObjectRestrict_congr α hip.symm _ _
  rw [hk, Functor.map_comp]
  infer_instance

theorem isLimitCone_coneObjectRestrict_iff (α : Bool) (hX : IsInftyCategory 1 X)
    (k : K' ⟶ K) [WeakEquivalence ((DiagSet.toInfty 1).map k)] {d : K ⟶ X} {d' : K' ⟶ X}
    (h : k ≫ d = d') (v : (coneObject α d).Vertex) :
    IsLimitCone α d' (v.map (coneObjectRestrict α k h)) ↔
      IsLimitCone α d v :=
  have := weakEquivalence_toInfty_one_coneObjectRestrict α hX k h
  DiagSet.hasContractibleHoms_map_iff (isInftyCategory_coneObject α d hX)
    (isInftyCategory_coneObject α d' hX) _ α v

private theorem hasContractibleHoms_map_iff_of_isIso {Y : DiagSet.{u}} (F : X ⟶ Y) [IsIso F]
    (α : Bool) (t : X.Vertex) :
    Y.HasContractibleHoms α (t.map F) ↔ X.HasContractibleHoms α t := by
  have hmap (x : X.Vertex) :
      (bipointedHom.obj (Y.bipoint (cond α (x.map F)
        (t.map F)) (cond α (t.map F)
          (x.map F)))).IsContractible ↔
        (bipointedHom.obj (X.bipoint (cond α x t) (cond α t x))).IsContractible := by
    rw [← Bool.apply_cond (DiagSet.Vertex.map F),
      ← Bool.apply_cond (DiagSet.Vertex.map F)]
    have : IsIso ((Under.forget _).map (DiagSet.bipointMap F (cond α x t) (cond α t x))) :=
      inferInstanceAs (IsIso F)
    have : IsIso (DiagSet.bipointMap F (cond α x t) (cond α t x)) :=
      isIso_of_reflects_iso _ (Under.forget _)
    have : WeakEquivalence ((DiagSet.toInfty 0).map
        (bipointedHom.map (DiagSet.bipointMap F (cond α x t) (cond α t x)))) :=
      (weakEquivalence_iff _).2 ((weakEquivalences _).of_isIso _)
    exact (DiagSet.isContractible_iff_of_weakEquivalence
      (bipointedHom.map (DiagSet.bipointMap F (cond α x t) (cond α t x)))).symm
  refine ⟨fun h x => (hmap x).1 (h _), fun h y => ?_⟩
  obtain ⟨x, rfl⟩ : ∃ x : X.Vertex, x.map F = y :=
    ⟨y.map (inv F), by rw [← DiagSet.Vertex.map_comp, IsIso.inv_hom_id, DiagSet.Vertex.map_id]⟩
  exact (hmap x).2 (h x)

theorem isLimitCone_coneObjectRestrict_iff_of_isIso (α : Bool) (k : K' ⟶ K) [IsIso k]
    {d : K ⟶ X} {d' : K' ⟶ X} (h : k ≫ d = d') (v : (coneObject α d).Vertex) :
    IsLimitCone α d' (v.map (coneObjectRestrict α k h)) ↔
      IsLimitCone α d v :=
  hasContractibleHoms_map_iff_of_isIso (coneObjectRestrict α k h) α v

private theorem grayHomRightCellEquiv_uliftYonedaEquiv {B Z : DiagSet.{u}} {U : Atom}
    (g : ball.{u} U ⟶ (grayHomRight B).obj Z) :
    grayHomRightCellEquiv B Z U (uliftYonedaEquiv g) =
      ((grayTensorRightAdjunction B).homEquiv _ Z).symm g := by
  obtain ⟨F, rfl⟩ := ((grayTensorRightAdjunction B).homEquiv _ Z).surjective g
  rw [Equiv.symm_apply_apply, ← Category.id_comp ((grayTensorRightAdjunction B).homEquiv _ Z F),
    uliftYonedaEquiv_comp, grayHomRightCellEquiv_homEquiv_app, Equiv.symm_apply_apply,
    CategoryTheory.Functor.map_id, Category.id_comp]

private theorem uliftYonedaEquiv_symm_coneObjectVerticesEquiv_edge (α : Bool) (d : K ⟶ X)
    (v : (coneObject α d).Vertex) :
    edgeHom (coneObjectVerticesEquiv α d v).2 =
      inv (grayTensorSnd (ball.{u} atomPoint) (ball (atomSimplex 1))) ≫
        ((grayTensorRightAdjunction (ball.{u} (atomSimplex 1))).homEquiv _ _).symm
          (vertexHom v ≫ coneObjectι α d) := by
  refine (congrArg (uliftYonedaEquiv (X := atomSimplex 1) (F := (grayHomRight K).obj X)).symm
    (DiagSet.mappingSpaceVerticesEquiv_edge _ _
      (coneObjectFibreVerticesEquiv α d _ ⟨v, rfl⟩))).trans ?_
  rw [Equiv.symm_apply_apply]
  refine congrArg (inv (grayTensorSnd (ball.{u} atomPoint) (ball (atomSimplex 1))) ≫ ·) ?_
  refine (grayHomRightCellEquiv_uliftYonedaEquiv
    ((isPullback_mappingSpace_coneObject α d _).lift (vertexHom v) (𝟙 _)
      (by rw [vertexHom_comp, Category.id_comp]) ≫ Subfunctor.ι _)).trans ?_
  congr 1
  exact (congrArg (_ ≫ ·) (pullback.lift_fst _ _ _).symm).trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ coneObjectι α d) (IsPullback.lift_fst _ _ _ _)))

private noncomputable def edgeEquivGrayTensor
    (a b : ((grayHomRight K).obj X).Vertex) :
    ((grayHomRight K).obj X).Edge a b ≃
      {σ : grayTensor (ball.{u} (atomSimplex 1)) K ⟶ X //
      (grayTensorRight K).map intervalSource ≫ σ =
          ((grayTensorRightAdjunction K).homEquiv _ X).symm (vertexHom a) ∧
        (grayTensorRight K).map intervalTarget ≫ σ =
          ((grayTensorRightAdjunction K).homEquiv _ X).symm (vertexHom b)} where
  toFun e := ⟨((grayTensorRightAdjunction K).homEquiv _ X).symm (edgeHom e), by
    rw [← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_left_symm]
    exact ⟨congrArg _ (intervalSource_comp_edgeHom e),
      congrArg _ (intervalTarget_comp_edgeHom e)⟩⟩
  invFun σ := edgeOfHom (((grayTensorRightAdjunction K).homEquiv _ X) σ.1)
    (by rw [← Adjunction.homEquiv_naturality_left, σ.2.1, Equiv.apply_symm_apply])
    (by rw [← Adjunction.homEquiv_naturality_left, σ.2.2, Equiv.apply_symm_apply])
  left_inv e := edgeHom_injective (by
    rw [edgeHom_edgeOfHom, Equiv.apply_symm_apply])
  right_inv σ := Subtype.ext (by
    dsimp only
    rw [edgeHom_edgeOfHom, Equiv.symm_apply_apply])

private theorem homEquiv_symm_vertexHom_constDiagram (l : X.Vertex) :
    ((grayTensorRightAdjunction K).homEquiv _ X).symm
        (vertexHom (l.map (constDiagram K X))) =
      grayTensorFst _ K ≫ vertexHom l := by
  rw [← vertexHom_comp, constDiagram, Adjunction.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply, grayTensorRight_map_grayTensorFst]

private theorem homEquiv_symm_vertexHom_diagramVertex (d : K ⟶ X) :
    ((grayTensorRightAdjunction K).homEquiv _ X).symm (vertexHom (diagramVertex d)) =
      grayTensorSnd _ K ≫ d := by
  have h : vertexHom (diagramVertex d) =
      isTerminalBallAtomPoint.from (ball.{u} atomPoint) ≫ diagramPoint d :=
    Equiv.symm_apply_apply _ _
  rw [h, comp_diagramPoint, Equiv.symm_apply_apply]

noncomputable def coneObjectVerticesGrayTensorEquiv (α : Bool) (d : K ⟶ X) :
    (coneObject α d).Vertex ≃ Σ l : X.Vertex,
      {σ : grayTensor (ball.{u} (atomSimplex 1)) K ⟶ X //
        (grayTensorRight K).map (cond α intervalSource intervalTarget) ≫ σ =
            grayTensorFst _ K ≫ vertexHom l ∧
          (grayTensorRight K).map (cond α intervalTarget intervalSource) ≫ σ =
            grayTensorSnd _ K ≫ d} :=
  (coneObjectVerticesEquiv α d).trans (Equiv.sigmaCongrRight fun l =>
    (edgeEquivGrayTensor _ _).trans (Equiv.subtypeEquivRight fun σ => by
      cases α
      · simp only [cond, homEquiv_symm_vertexHom_constDiagram,
          homEquiv_symm_vertexHom_diagramVertex]
        exact And.comm
      · simp only [cond, homEquiv_symm_vertexHom_constDiagram,
          homEquiv_symm_vertexHom_diagramVertex]))

@[simp]
theorem coneObjectVerticesGrayTensorEquiv_fst (α : Bool) (d : K ⟶ X)
    (v : (coneObject α d).Vertex) :
    (coneObjectVerticesGrayTensorEquiv α d v).1 =
      v.map (coneObjectπ α d) :=
  rfl

private theorem coneObjectVerticesGrayTensorEquiv_snd_coe (α : Bool) (d : K ⟶ X)
    (v : (coneObject α d).Vertex) :
    ((coneObjectVerticesGrayTensorEquiv α d v).2 : grayTensor _ K ⟶ X) =
      ((grayTensorRightAdjunction K).homEquiv _ X).symm
        (inv (grayTensorSnd (ball.{u} atomPoint) (ball (atomSimplex 1))) ≫
          ((grayTensorRightAdjunction (ball.{u} (atomSimplex 1))).homEquiv _ _).symm
            (vertexHom v ≫ coneObjectι α d)) :=
  congrArg ((grayTensorRightAdjunction K).homEquiv _ X).symm
    (uliftYonedaEquiv_symm_coneObjectVerticesEquiv_edge α d v)

theorem coneObjectVerticesGrayTensorEquiv_coneObjectRestrict (α : Bool) (k : K' ⟶ K)
    {d : K ⟶ X} {d' : K' ⟶ X} (h : k ≫ d = d')
    (v : (coneObject α d).Vertex) :
    ((coneObjectVerticesGrayTensorEquiv α d' (v.map (coneObjectRestrict α k h))).2 :
        grayTensor (ball.{u} (atomSimplex 1)) K' ⟶ X) =
      (grayTensorLeft _).map k ≫
        ((coneObjectVerticesGrayTensorEquiv α d v).2 :
          grayTensor (ball.{u} (atomSimplex 1)) K ⟶ X) := by
  rw [coneObjectVerticesGrayTensorEquiv_snd_coe, coneObjectVerticesGrayTensorEquiv_snd_coe,
    ← vertexHom_comp, Category.assoc, coneObjectRestrict_ι, ← Category.assoc,
    Adjunction.homEquiv_naturality_right_symm, ← Category.assoc,
    homEquiv_symm_comp_grayHomRestrict]

@[reassoc]
private theorem grayTensorLeft_map_grayTensorFst' (A : DiagSet.{u}) {B B' : DiagSet.{u}}
    (g : B ⟶ B') : (grayTensorLeft A).map g ≫ grayTensorFst A B' = grayTensorFst A B := by
  rw [grayTensorLeft_map_eq, grayTensorBifunctor_map_grayTensorFst, Category.comp_id]

private theorem grayTensorRight_map_grayTensorLeft_map_assoc {A A' B B' Z : DiagSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (σ : grayTensor A' B' ⟶ Z) :
    (grayTensorRight B).map f ≫ (grayTensorLeft A').map g ≫ σ =
      (grayTensorLeft A).map g ≫ (grayTensorRight B').map f ≫ σ := by
  rw [← Category.assoc, ← grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc]

private theorem isPushout_grayTensorLeft_cornerShape (α : Bool) (A : DiagSet.{u}) :
    IsPushout ((grayTensorLeft A).map (cond α intervalTarget.{u} intervalSource))
      ((grayTensorLeft A).map (cond α intervalTarget.{u} intervalSource))
      ((grayTensorLeft A).map (pushout.inl (cond α intervalTarget.{u} intervalSource)
        (cond α intervalTarget intervalSource) : ball.{u} (atomSimplex 1) ⟶ cornerShape.{u} α))
      ((grayTensorLeft A).map (pushout.inr (cond α intervalTarget.{u} intervalSource)
        (cond α intervalTarget intervalSource) : ball.{u} (atomSimplex 1) ⟶ cornerShape.{u} α)) :=
  (IsPushout.of_hasPushout _ _).map (grayTensorLeft A)

private noncomputable def grayTensorCornerEquiv (α : Bool) (f g : ball.{u} (atomSimplex 1) ⟶ X)
    (h : cond α intervalTarget intervalSource ≫ f = cond α intervalTarget intervalSource ≫ g)
    (l : X.Vertex) :
    {σ : grayTensor (ball.{u} (atomSimplex 1)) (cornerShape α) ⟶ X //
        (grayTensorRight _).map (cond α intervalSource intervalTarget) ≫ σ =
            grayTensorFst _ _ ≫ vertexHom l ∧
          (grayTensorRight _).map (cond α intervalTarget intervalSource) ≫ σ =
            grayTensorSnd _ _ ≫ cornerDiagram α f g h} ≃
      {σ : (grayTensor (ball.{u} (atomSimplex 1)) (ball (atomSimplex 1)) ⟶ X) ×
            (grayTensor (ball.{u} (atomSimplex 1)) (ball (atomSimplex 1)) ⟶ X) //
          ((grayTensorRight _).map (cond α intervalSource intervalTarget) ≫ σ.1 =
              grayTensorFst _ _ ≫ vertexHom l ∧
            (grayTensorRight _).map (cond α intervalTarget intervalSource) ≫ σ.1 =
              grayTensorSnd _ _ ≫ f) ∧
          ((grayTensorRight _).map (cond α intervalSource intervalTarget) ≫ σ.2 =
              grayTensorFst _ _ ≫ vertexHom l ∧
            (grayTensorRight _).map (cond α intervalTarget intervalSource) ≫ σ.2 =
              grayTensorSnd _ _ ≫ g) ∧
          (grayTensorLeft _).map (cond α intervalTarget intervalSource) ≫ σ.1 =
            (grayTensorLeft _).map (cond α intervalTarget intervalSource) ≫ σ.2} :=
  have hP := isPushout_grayTensorLeft_cornerShape α (ball.{u} (atomSimplex 1))
  have hpt := isPushout_grayTensorLeft_cornerShape α (ball.{u} atomPoint)
  have fst {j : ball.{u} (atomSimplex 1) ⟶ cornerShape α}
      {e : ball.{u} atomPoint ⟶ ball.{u} (atomSimplex 1)}
      {σ : grayTensor (ball.{u} (atomSimplex 1)) (cornerShape α) ⟶ X}
      (hσ : (grayTensorRight (cornerShape α)).map e ≫ σ =
        grayTensorFst (ball.{u} atomPoint) (cornerShape α) ≫ vertexHom l) :
      (grayTensorRight (ball.{u} (atomSimplex 1))).map e ≫
          (grayTensorLeft (ball.{u} (atomSimplex 1))).map j ≫ σ =
        grayTensorFst (ball.{u} atomPoint) (ball.{u} (atomSimplex 1)) ≫ vertexHom l :=
    (grayTensorRight_map_grayTensorLeft_map_assoc e j σ).trans
      ((congrArg _ hσ).trans (grayTensorLeft_map_grayTensorFst'_assoc _ j (vertexHom l)))
  have snd {j : ball.{u} (atomSimplex 1) ⟶ cornerShape α}
      {e : ball.{u} atomPoint ⟶ ball.{u} (atomSimplex 1)}
      {σ : grayTensor (ball.{u} (atomSimplex 1)) (cornerShape α) ⟶ X} {D : cornerShape α ⟶ X}
      (hσ : (grayTensorRight (cornerShape α)).map e ≫ σ =
        grayTensorSnd (ball.{u} atomPoint) (cornerShape α) ≫ D) :
      (grayTensorRight (ball.{u} (atomSimplex 1))).map e ≫
          (grayTensorLeft (ball.{u} (atomSimplex 1))).map j ≫ σ =
        grayTensorSnd (ball.{u} atomPoint) (ball.{u} (atomSimplex 1)) ≫ j ≫ D :=
    (grayTensorRight_map_grayTensorLeft_map_assoc e j σ).trans
      ((congrArg _ hσ).trans
        ((reassoc_of% (grayTensorLeft_map_grayTensorSnd (ball.{u} atomPoint) j)) D))
  have fstInv {σ₁ σ₂ : grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ X}
      (hw : (grayTensorLeft _).map (cond α intervalTarget intervalSource) ≫ σ₁ =
        (grayTensorLeft _).map (cond α intervalTarget intervalSource) ≫ σ₂)
      {e : ball.{u} atomPoint ⟶ ball.{u} (atomSimplex 1)}
      (h₁ : (grayTensorRight (ball.{u} (atomSimplex 1))).map e ≫ σ₁ =
        grayTensorFst (ball.{u} atomPoint) (ball.{u} (atomSimplex 1)) ≫ vertexHom l)
      (h₂ : (grayTensorRight (ball.{u} (atomSimplex 1))).map e ≫ σ₂ =
        grayTensorFst (ball.{u} atomPoint) (ball.{u} (atomSimplex 1)) ≫ vertexHom l) :
      (grayTensorRight (cornerShape α)).map e ≫ hP.desc σ₁ σ₂ hw =
        grayTensorFst (ball.{u} atomPoint) (cornerShape α) ≫ vertexHom l :=
    hpt.hom_ext
      ((grayTensorRight_map_grayTensorLeft_map_assoc e (pushout.inl _ _ : _ ⟶ cornerShape.{u} α)
          (hP.desc σ₁ σ₂ hw)).symm.trans
        ((congrArg _ (hP.inl_desc σ₁ σ₂ hw)).trans
          (h₁.trans (grayTensorLeft_map_grayTensorFst'_assoc _ _ (vertexHom l)).symm)))
      ((grayTensorRight_map_grayTensorLeft_map_assoc e (pushout.inr _ _ : _ ⟶ cornerShape.{u} α)
          (hP.desc σ₁ σ₂ hw)).symm.trans
        ((congrArg _ (hP.inr_desc σ₁ σ₂ hw)).trans
          (h₂.trans (grayTensorLeft_map_grayTensorFst'_assoc _ _ (vertexHom l)).symm)))
  have sndInv {σ₁ σ₂ : grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ X}
      (hw : (grayTensorLeft _).map (cond α intervalTarget intervalSource) ≫ σ₁ =
        (grayTensorLeft _).map (cond α intervalTarget intervalSource) ≫ σ₂)
      {e : ball.{u} atomPoint ⟶ ball.{u} (atomSimplex 1)}
      (h₁ : (grayTensorRight (ball.{u} (atomSimplex 1))).map e ≫ σ₁ =
        grayTensorSnd (ball.{u} atomPoint) (ball.{u} (atomSimplex 1)) ≫ f)
      (h₂ : (grayTensorRight (ball.{u} (atomSimplex 1))).map e ≫ σ₂ =
        grayTensorSnd (ball.{u} atomPoint) (ball.{u} (atomSimplex 1)) ≫ g) :
      (grayTensorRight (cornerShape α)).map e ≫ hP.desc σ₁ σ₂ hw =
        grayTensorSnd (ball.{u} atomPoint) (cornerShape α) ≫ cornerDiagram α f g h :=
    hpt.hom_ext
      ((grayTensorRight_map_grayTensorLeft_map_assoc e (pushout.inl _ _ : _ ⟶ cornerShape.{u} α)
          (hP.desc σ₁ σ₂ hw)).symm.trans
        ((congrArg _ (hP.inl_desc σ₁ σ₂ hw)).trans (h₁.trans
          ((congrArg _ (pushout.inl_desc f g h)).symm.trans
            ((reassoc_of% (grayTensorLeft_map_grayTensorSnd (ball.{u} atomPoint)
              (pushout.inl _ _ : _ ⟶ cornerShape.{u} α))) (cornerDiagram α f g h)).symm))))
      ((grayTensorRight_map_grayTensorLeft_map_assoc e (pushout.inr _ _ : _ ⟶ cornerShape.{u} α)
          (hP.desc σ₁ σ₂ hw)).symm.trans
        ((congrArg _ (hP.inr_desc σ₁ σ₂ hw)).trans (h₂.trans
          ((congrArg _ (pushout.inr_desc f g h)).symm.trans
            ((reassoc_of% (grayTensorLeft_map_grayTensorSnd (ball.{u} atomPoint)
              (pushout.inr _ _ : _ ⟶ cornerShape.{u} α))) (cornerDiagram α f g h)).symm))))
  { toFun σ := ⟨((grayTensorLeft _).map (pushout.inl _ _ : _ ⟶ cornerShape.{u} α) ≫ σ.1,
        (grayTensorLeft _).map (pushout.inr _ _ : _ ⟶ cornerShape.{u} α) ≫ σ.1),
      ⟨fst σ.2.1, (snd σ.2.2).trans (congrArg _ (pushout.inl_desc f g h))⟩,
      ⟨fst σ.2.1, (snd σ.2.2).trans (congrArg _ (pushout.inr_desc f g h))⟩,
      (reassoc_of% hP.w) σ.1⟩
    invFun σ := ⟨hP.desc σ.1.1 σ.1.2 σ.2.2.2,
      fstInv σ.2.2.2 σ.2.1.1 σ.2.2.1.1, sndInv σ.2.2.2 σ.2.1.2 σ.2.2.1.2⟩
    left_inv _ := Subtype.ext (hP.hom_ext (hP.inl_desc _ _ _) (hP.inr_desc _ _ _))
    right_inv _ := Subtype.ext (Prod.ext (hP.inl_desc _ _ _) (hP.inr_desc _ _ _)) }

noncomputable def coneObjectCornerVerticesEquiv (α : Bool) (f g : ball.{u} (atomSimplex 1) ⟶ X)
    (h : cond α intervalTarget intervalSource ≫ f = cond α intervalTarget intervalSource ≫ g) :
    (coneObject α (cornerDiagram α f g h)).Vertex ≃
      Σ l : X.Vertex,
        {σ : (grayTensor (ball.{u} (atomSimplex 1)) (ball (atomSimplex 1)) ⟶ X) ×
            (grayTensor (ball.{u} (atomSimplex 1)) (ball (atomSimplex 1)) ⟶ X) //
          ((grayTensorRight _).map (cond α intervalSource intervalTarget) ≫ σ.1 =
              grayTensorFst _ _ ≫ vertexHom l ∧
            (grayTensorRight _).map (cond α intervalTarget intervalSource) ≫ σ.1 =
              grayTensorSnd _ _ ≫ f) ∧
          ((grayTensorRight _).map (cond α intervalSource intervalTarget) ≫ σ.2 =
              grayTensorFst _ _ ≫ vertexHom l ∧
            (grayTensorRight _).map (cond α intervalTarget intervalSource) ≫ σ.2 =
              grayTensorSnd _ _ ≫ g) ∧
          (grayTensorLeft _).map (cond α intervalTarget intervalSource) ≫ σ.1 =
            (grayTensorLeft _).map (cond α intervalTarget intervalSource) ≫ σ.2} :=
  (coneObjectVerticesGrayTensorEquiv α _).trans
    (Equiv.sigmaCongrRight (grayTensorCornerEquiv α f g h))

@[simp]
theorem coneObjectCornerVerticesEquiv_fst (α : Bool) (f g : ball.{u} (atomSimplex 1) ⟶ X)
    (h : cond α intervalTarget intervalSource ≫ f = cond α intervalTarget intervalSource ≫ g)
    (v : (coneObject α (cornerDiagram α f g h)).Vertex) :
    (coneObjectCornerVerticesEquiv α f g h v).1 =
      v.map (coneObjectπ α (cornerDiagram α f g h)) :=
  rfl

end Atoms.Diagrammatic
