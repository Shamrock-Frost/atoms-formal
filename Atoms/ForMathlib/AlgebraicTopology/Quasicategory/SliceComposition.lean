import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.FinalObject

open CategoryTheory Limits Simplicial MorphismProperty

universe u

namespace SSet

section Slice

private lemma hasLiftingProperty_sliceπ {K L T : SSet.{u}} (i : K ⟶ L) (t : Under T)
    (sq : (Functor.curry.obj joinFunctor).PushoutObjObj i (⊥ : T.Subcomplex).ι)
    (h : ∀ u : sq.pt ⟶ t.right, ∃ v, sq.ι ≫ v = u) : HasLiftingProperty i (sliceπ t) := by
  refine ⟨fun {a b} sqab ↦ ?_⟩
  have : IsIso (joinInclLeft K ((⊥ : T.Subcomplex) : SSet.{u})) :=
    isIso_joinInclLeft_of_isEmpty _ _
  let eL := @asIso _ _ _ _ (joinInclLeft L ((⊥ : T.Subcomplex) : SSet.{u}))
    (isIso_joinInclLeft_of_isEmpty _ _)
  have hL : eL.hom ≫ joinMap (𝟙 L) (⊥ : T.Subcomplex).ι = joinInclLeft L T :=
    (joinInclLeft_comp_joinMap _ _).trans (Category.id_comp _)
  let a' : join K T ⟶ t.right := (((joinRightUnderAdjunction T).homEquiv _ _).symm a).right
  have hw : joinMap i (𝟙 _) ≫ eL.inv ≫ b = joinMap (𝟙 _) (⊥ : T.Subcomplex).ι ≫ a' := by
    rw [← cancel_epi (joinInclLeft K _), joinInclLeft_comp_joinMap_assoc]
    refine (congrArg (i ≫ ·) (eL.hom_inv_id_assoc b)).trans ?_
    exact sqab.w.symm.trans ((comp_sliceπ a).trans ((joinInclLeft_comp_joinMap_assoc (𝟙 _) _
      a').trans (Category.id_comp _)).symm)
  have ha : joinInclRight K T ≫ a' = t.hom :=
    Under.w (((joinRightUnderAdjunction T).homEquiv _ _).symm a)
  obtain ⟨v, hv⟩ := h (sq.isPushout.desc (eL.inv ≫ b) a' hw)
  have hinr : joinMap i (𝟙 T) ≫ v = a' :=
    (congrArg (· ≫ v) sq.inr_ι.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg _ hv).trans (sq.isPushout.inr_desc _ _ _)))
  have hl : joinInclRight L T ≫ v = t.hom :=
    (congrArg (· ≫ v) ((joinInclRight_comp_joinMap i (𝟙 T)).trans
      (Category.id_comp _)).symm).trans ((Category.assoc _ _ _).trans ((congrArg _ hinr).trans ha))
  refine ⟨⟨⟨(joinRightUnderAdjunction T).homEquiv _ _ (Under.homMk v hl), ?_, ?_⟩⟩⟩
  · rw [← Adjunction.homEquiv_naturality_left]
    exact (((joinRightUnderAdjunction T).homEquiv _ _).symm_apply_eq.1
      (Under.UnderMorphism.ext hinr).symm).symm
  · rw [comp_sliceπ, Equiv.symm_apply_apply]
    refine ((joinInclLeft_comp_joinMap_assoc (𝟙 L) (⊥ : T.Subcomplex).ι v).symm.trans ?_).trans
      (eL.hom_inv_id_assoc b)
    exact congrArg (joinInclLeft _ _ ≫ ·) ((congrArg (· ≫ v) ((Category.id_comp _).trans
      sq.inl_ι.symm)).trans ((Category.assoc _ _ _).trans ((congrArg _ hv).trans
        (sq.isPushout.inl_desc _ _ _))))

theorem rightFibrations_sliceπ {K X : SSet.{u}} [X.Quasicategory] (d : K ⟶ X) :
    rightFibrations (sliceπ (Under.mk d)) := by
  have hX : innerFibrations (terminal.from X) := mem_innerFibrations _
  rintro _ _ _ @⟨n, k, hk⟩
  let sq := Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj joinFunctor) Λ[n + 1, k].ι
    (⊥ : K.Subcomplex).ι
  refine hasLiftingProperty_sliceπ _ _ sq fun u ↦ ?_
  have hu := innerAnodyneExtensions_pushoutObjObjι_join sq (rightAnodyneExtensions.horn_ι hk)
    _ hX
  obtain ⟨l⟩ := (hu.sq_hasLift (⟨terminal.hom_ext _ _⟩ :
    CommSq u sq.ι _ (terminal.from _))).exists_lift
  exact ⟨l.l, l.fac_left⟩

end Slice

section SliceAtMap

noncomputable def sliceAtMap {E X : SSet.{u}} (p : E ⟶ X) (e : E _⦋0⦌) :
    sliceAt E e ⟶ sliceAt X (p.app _ e) :=
  (slice Δ[0]).map (Under.homMk p (yonedaEquiv_symm_comp e p))

@[reassoc]
theorem sliceAtMap_comp_sliceAtπ {E X : SSet.{u}} (p : E ⟶ X) (e : E _⦋0⦌) :
    sliceAtMap p e ≫ sliceAtπ X (p.app _ e) = sliceAtπ E e ≫ p :=
  slice_map_sliceπ _

theorem sliceAtMap_comp {E F X : SSet.{u}} (Φ : E ⟶ F) (p : F ⟶ X) (e : E _⦋0⦌) :
    sliceAtMap (Φ ≫ p) e = sliceAtMap Φ e ≫ sliceAtMap p (Φ.app _ e) := by
  rw [sliceAtMap, sliceAtMap, sliceAtMap, ← Functor.map_comp]
  rfl

theorem sliceAtMap_sliceId {E X : SSet.{u}} (p : E ⟶ X) (e : E _⦋0⦌) :
    (sliceAtMap p e).app _ (sliceId E e) = sliceId X (p.app _ e) := by
  rw [sliceId, sliceId, ← yonedaEquiv_comp, sliceAtMap, ← Adjunction.homEquiv_naturality_right]
  refine congrArg (fun f ↦ yonedaEquiv ((joinRightUnderAdjunction Δ[0]).homEquiv _ _ f))
    (Under.UnderMorphism.ext ?_)
  exact (Category.assoc (stdSimplex.isTerminalObj₀.from _) (yonedaEquiv.symm e) p).trans
    (congrArg (stdSimplex.isTerminalObj₀.from _ ≫ ·) (yonedaEquiv_symm_comp e p))

theorem trivialFibration_sliceAtMap {E X : SSet.{u}} {p : E ⟶ X} (hp : rightFibrations p)
    (e : E _⦋0⦌) : modelCategoryQuillen.I.rlp (sliceAtMap p e) := by
  have key : ∀ {w : Δ[0] ⟶ X} (hw : yonedaEquiv.symm e ≫ p = w),
      modelCategoryQuillen.I.rlp ((slice Δ[0]).map
        (Under.homMk p hw : Under.mk (yonedaEquiv.symm e) ⟶ Under.mk w)) := by
    rintro _ rfl _ _ _ ⟨n⟩
    exact (hasLiftingProperty_joinMap_id_iff _ p).1 (rightAnodyneExtensions_joinMap_id _ _ hp) _
  exact key _

noncomputable def sliceAtMapOfEq {E X : SSet.{u}} (p : E ⟶ X) {e : E _⦋0⦌} {a : X _⦋0⦌}
    (ha : p.app _ e = a) : sliceAt E e ⟶ sliceAt X a :=
  (slice Δ[0]).map (Under.homMk p ((yonedaEquiv_symm_comp e p).trans (congrArg _ ha)))

@[reassoc]
theorem sliceAtMapOfEq_comp_sliceAtπ {E X : SSet.{u}} (p : E ⟶ X) {e : E _⦋0⦌} {a : X _⦋0⦌}
    (ha : p.app _ e = a) : sliceAtMapOfEq p ha ≫ sliceAtπ X a = sliceAtπ E e ≫ p :=
  slice_map_sliceπ _

theorem sliceAtMap_comp_sliceAtMapOfEq {E F X : SSet.{u}} {Φ : E ⟶ F} {q : F ⟶ X} {p : E ⟶ X}
    (hΦ : Φ ≫ q = p) {e : E _⦋0⦌} {a : X _⦋0⦌} (ha : q.app _ (Φ.app _ e) = a)
    (ha' : p.app _ e = a) : sliceAtMap Φ e ≫ sliceAtMapOfEq q ha = sliceAtMapOfEq p ha' := by
  subst hΦ ha
  exact (sliceAtMap_comp Φ q e).symm

theorem trivialFibration_sliceAtMapOfEq {E X : SSet.{u}} {p : E ⟶ X} (hp : rightFibrations p)
    {e : E _⦋0⦌} {a : X _⦋0⦌} (ha : p.app _ e = a) :
    modelCategoryQuillen.I.rlp (sliceAtMapOfEq p ha) := by
  subst ha
  exact trivialFibration_sliceAtMap hp e

end SliceAtMap

section YonedaMap

private lemma exists_section_sliceAtMap {E X : SSet.{u}} {p : E ⟶ X} (hp : rightFibrations p)
    (e : E _⦋0⦌) : ∃ s : sliceAt X (p.app _ e) ⟶ sliceAt E e, s ≫ sliceAtMap p e = 𝟙 _ ∧
      yonedaEquiv.symm (sliceId X (p.app _ e)) ≫ s = yonedaEquiv.symm (sliceId E e) := by
  have : Mono (yonedaEquiv.symm (sliceId X (p.app _ e)) : Δ[0] ⟶ sliceAt X (p.app _ e)) :=
    stdSimplex.isTerminalObj₀.mono_from _
  have h := trivialFibration_sliceAtMap hp e
  rw [← rlp_monomorphisms] at h
  have := h _ (monomorphisms.infer_property (yonedaEquiv.symm (sliceId X (p.app _ e))))
  obtain ⟨l⟩ := (this.sq_hasLift (CommSq.mk (by
    rw [Category.comp_id, yonedaEquiv_symm_comp, sliceAtMap_sliceId]) :
    CommSq (yonedaEquiv.symm (sliceId E e)) (yonedaEquiv.symm (sliceId X (p.app _ e)))
      (sliceAtMap p e) (𝟙 _))).exists_lift
  exact ⟨l.l, l.fac_right, l.fac_left⟩

noncomputable def yonedaMap {E X : SSet.{u}} {p : E ⟶ X} (hp : rightFibrations p)
    (e : E _⦋0⦌) : sliceAt X (p.app _ e) ⟶ E :=
  (exists_section_sliceAtMap hp e).choose ≫ sliceAtπ E e

@[reassoc]
theorem yonedaMap_comp {E X : SSet.{u}} {p : E ⟶ X} (hp : rightFibrations p) (e : E _⦋0⦌) :
    yonedaMap hp e ≫ p = sliceAtπ X (p.app _ e) := by
  rw [yonedaMap, Category.assoc, ← sliceAtMap_comp_sliceAtπ, ← Category.assoc,
    (exists_section_sliceAtMap hp e).choose_spec.1, Category.id_comp]

theorem yonedaMap_sliceId {E X : SSet.{u}} {p : E ⟶ X} (hp : rightFibrations p) (e : E _⦋0⦌) :
    (yonedaMap hp e).app _ (sliceId X (p.app _ e)) = e := by
  apply yonedaEquiv.symm.injective
  rw [← yonedaEquiv_symm_comp, yonedaMap, ← Category.assoc,
    (exists_section_sliceAtMap hp e).choose_spec.2, sliceId_comp_sliceAtπ]

end YonedaMap

end SSet
