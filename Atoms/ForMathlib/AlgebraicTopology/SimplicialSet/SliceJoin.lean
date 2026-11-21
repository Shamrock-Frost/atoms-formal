import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Right
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.JoinAssoc
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.JoinSlice

open CategoryTheory Limits Simplicial Opposite

universe u

namespace SSet

private lemma joinMap_id_id (X Y : SSet.{u}) : joinMap (𝟙 X) (𝟙 Y) = 𝟙 (join X Y) :=
  joinFunctor.map_id (X, Y)

section Transpose

variable {A A' T : SSet.{u}} {t t' : Under T}

private noncomputable def sliceTranspose (ψ : A ⟶ (slice T).obj t) : join A T ⟶ t.right :=
  (((joinRightUnderAdjunction T).homEquiv _ _).symm ψ).right

private lemma joinInclRight_comp_sliceTranspose (ψ : A ⟶ (slice T).obj t) :
    joinInclRight A T ≫ sliceTranspose ψ = t.hom :=
  Under.w (((joinRightUnderAdjunction T).homEquiv _ _).symm ψ)

private lemma sliceTranspose_injective {ψ ψ' : A ⟶ (slice T).obj t}
    (h : sliceTranspose ψ = sliceTranspose ψ') : ψ = ψ' :=
  ((joinRightUnderAdjunction T).homEquiv _ _).symm.injective (Under.UnderMorphism.ext h)

private noncomputable def sliceUntranspose (φ : join A T ⟶ t.right)
    (h : joinInclRight A T ≫ φ = t.hom) : A ⟶ (slice T).obj t :=
  (joinRightUnderAdjunction T).homEquiv _ _ (Under.homMk φ h)

private lemma sliceTranspose_sliceUntranspose (φ : join A T ⟶ t.right)
    (h : joinInclRight A T ≫ φ = t.hom) : sliceTranspose (sliceUntranspose φ h) = φ := by
  rw [sliceTranspose, sliceUntranspose, Equiv.symm_apply_apply]
  rfl

private lemma sliceTranspose_comp (f : A' ⟶ A) (ψ : A ⟶ (slice T).obj t) :
    sliceTranspose (f ≫ ψ) = joinMap f (𝟙 T) ≫ sliceTranspose ψ := by
  rw [sliceTranspose, Adjunction.homEquiv_naturality_left_symm, Under.comp_right]
  rfl

private lemma sliceTranspose_comp_map (ψ : A ⟶ (slice T).obj t) (k : t ⟶ t') :
    sliceTranspose (ψ ≫ (slice T).map k) = sliceTranspose ψ ≫ k.right := by
  rw [sliceTranspose, Adjunction.homEquiv_naturality_right_symm, Under.comp_right]
  rfl

private lemma sliceTranspose_comp_sliceRes {B : SSet.{u}} (g : B ⟶ T) (ψ : A ⟶ (slice T).obj t) :
    sliceTranspose (ψ ≫ sliceRes g t) = joinMap (𝟙 A) g ≫ sliceTranspose ψ := by
  have h : sliceRes g t = sliceUntranspose (joinMap (𝟙 _) g ≫ sliceTranspose (𝟙 _)) (by
      rw [joinInclRight_comp_joinMap_assoc, joinInclRight_comp_sliceTranspose]
      rfl) := rfl
  rw [h, sliceTranspose_comp, sliceTranspose_sliceUntranspose, joinMap_comp_joinMap_assoc]
  conv_rhs => rw [← Category.comp_id ψ, sliceTranspose_comp, joinMap_comp_joinMap_assoc]
  simp only [Category.comp_id, Category.id_comp]

private lemma sliceTranspose_sliceRes {B : SSet.{u}} (g : B ⟶ T) (t : Under T) :
    sliceTranspose (sliceRes g t) = joinMap (𝟙 _) g ≫ sliceTranspose (𝟙 ((slice T).obj t)) :=
  (congrArg sliceTranspose (Category.id_comp _).symm).trans (sliceTranspose_comp_sliceRes g (𝟙 _))

end Transpose

section Iterated

variable {S T X : SSet.{u}}

noncomputable def joinAdjunct (t : join S T ⟶ X) :
    S ⟶ (slice T).obj (Under.mk (joinInclRight S T ≫ t)) :=
  (joinRightUnderAdjunction T).homEquiv S (Under.mk (joinInclRight S T ≫ t)) (Under.homMk t)

private lemma sliceTranspose_joinAdjunct (t : join S T ⟶ X) :
    sliceTranspose (joinAdjunct t) = t := by
  rw [sliceTranspose, joinAdjunct, Equiv.symm_apply_apply]
  rfl

private lemma joinInclRight_comp_joinAssoc_inv_comp (A : SSet.{u}) (t : join S T ⟶ X)
    (ψ : A ⟶ (slice S).obj (Under.mk (joinAdjunct t))) :
    joinInclRight A (join S T) ≫ (joinAssoc A S T).inv ≫ sliceTranspose (sliceTranspose ψ) =
      t := by
  rw [← reassoc_of% joinMap_joinInclRight_comp_joinAssoc_hom, Iso.hom_inv_id_assoc,
    ← sliceTranspose_comp, joinInclRight_comp_sliceTranspose]
  exact sliceTranspose_joinAdjunct t

private noncomputable def sliceJoinHom (t : join S T ⟶ X) :
    (slice S).obj (Under.mk (joinAdjunct t)) ⟶ (slice (join S T)).obj (Under.mk t) :=
  sliceUntranspose ((joinAssoc ((slice S).obj (Under.mk (joinAdjunct t))) S T).inv ≫
    sliceTranspose (sliceTranspose (𝟙 ((slice S).obj (Under.mk (joinAdjunct t))))))
    (joinInclRight_comp_joinAssoc_inv_comp _ t _)

private lemma sliceTranspose_sliceJoinHom (t : join S T ⟶ X) :
    sliceTranspose (sliceJoinHom t) =
      (joinAssoc ((slice S).obj (Under.mk (joinAdjunct t))) S T).inv ≫
        sliceTranspose (sliceTranspose (𝟙 ((slice S).obj (Under.mk (joinAdjunct t))))) :=
  sliceTranspose_sliceUntranspose _ _

private noncomputable def sliceJoinInvTranspose (t : join S T ⟶ X) :
    join ((slice (join S T)).obj (Under.mk t)) S ⟶
      (slice T).obj (Under.mk (joinInclRight S T ≫ t)) :=
  sliceUntranspose ((joinAssoc ((slice (join S T)).obj (Under.mk t)) S T).hom ≫
    sliceTranspose (𝟙 ((slice (join S T)).obj (Under.mk t)))) (by
      have h := joinInclRight_comp_joinMap
        (joinInclRight ((slice (join S T)).obj (Under.mk t)) S) (𝟙 T)
      rw [Category.id_comp] at h
      rw [← h, Category.assoc, joinMap_joinInclRight_comp_joinAssoc_hom_assoc,
        joinInclRight_comp_sliceTranspose]
      rfl)

private noncomputable def sliceJoinInv (t : join S T ⟶ X) :
    (slice (join S T)).obj (Under.mk t) ⟶ (slice S).obj (Under.mk (joinAdjunct t)) :=
  sliceUntranspose (sliceJoinInvTranspose t) (by
    apply sliceTranspose_injective
    rw [sliceTranspose_comp, sliceJoinInvTranspose, sliceTranspose_sliceUntranspose,
      joinMap_joinInclRight_comp_joinAssoc_hom_assoc, joinInclRight_comp_sliceTranspose]
    exact (sliceTranspose_joinAdjunct t).symm)

noncomputable def sliceJoinIso (t : join S T ⟶ X) :
    (slice S).obj (Under.mk (joinAdjunct t)) ≅ (slice (join S T)).obj (Under.mk t) where
  hom := sliceJoinHom t
  inv := sliceJoinInv t
  hom_inv_id := by
    apply sliceTranspose_injective
    apply sliceTranspose_injective
    rw [sliceTranspose_comp, sliceJoinInv, sliceTranspose_sliceUntranspose, sliceTranspose_comp,
      sliceJoinInvTranspose, sliceTranspose_sliceUntranspose,
      joinMap_joinMap_comp_joinAssoc_hom_assoc, joinMap_id_id, ← sliceTranspose_comp,
      Category.comp_id, sliceTranspose_sliceJoinHom, Iso.hom_inv_id_assoc]
  inv_hom_id := by
    apply sliceTranspose_injective
    have h := (Iso.comp_inv_eq _).2 (((Iso.eq_inv_comp _).2
      (joinMap_joinMap_comp_joinAssoc_hom (sliceJoinInv t) (𝟙 S) (𝟙 T)).symm).trans
        (Category.assoc _ _ _).symm)
    rw [joinMap_id_id] at h
    rw [sliceTranspose_comp, sliceTranspose_sliceJoinHom, reassoc_of% h, ← sliceTranspose_comp,
      ← sliceTranspose_comp, Category.comp_id, sliceJoinInv, sliceTranspose_sliceUntranspose,
      sliceJoinInvTranspose, sliceTranspose_sliceUntranspose, Iso.inv_hom_id_assoc]

theorem sliceJoinIso_hom_comp_sliceRes (t : join S T ⟶ X) :
    (sliceJoinIso t).hom ≫ sliceRes (joinInclRight S T) (Under.mk t) =
      sliceπ (Under.mk (joinAdjunct t)) := by
  apply sliceTranspose_injective
  rw [sliceTranspose_comp_sliceRes, ← Category.id_comp (sliceπ _), comp_sliceπ, ← sliceTranspose,
    sliceTranspose_comp]
  refine (congrArg (_ ≫ ·) (sliceTranspose_sliceJoinHom t)).trans ?_
  rw [← joinMap_joinInclLeft_comp_joinAssoc_hom_assoc, Iso.hom_inv_id_assoc]

theorem yonedaEquiv_joinAdjunct {K : SSet.{u}} (c : join Δ[0] K ⟶ X) :
    yonedaEquiv (joinAdjunct c) =
      (sliceObjEquiv K (Under.mk (joinInclRight Δ[0] K ≫ c)) 0).symm ⟨c, rfl⟩ := by
  apply (sliceObjEquiv K _ 0).injective
  rw [Equiv.apply_symm_apply, ← Category.id_comp (joinAdjunct c), yonedaEquiv_comp]
  apply Subtype.ext
  have : PreservesColimitsOfSize.{0, u} (joinRightUnder K) := preservesColimitsOfSize_shrink _
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} (joinRightUnder K)
    (Iso.refl _)
  have h := Presheaf.uliftYonedaAdjunction_homEquiv_app.{u} (joinRightUnder K) (Iso.refl _).hom
    (Under.homMk c rfl : (joinRightUnder K).obj Δ[0] ⟶ Under.mk (joinInclRight Δ[0] K ≫ c))
    (Z := op ⦋0⦌) (yonedaEquiv (𝟙 Δ[0]))
  refine (congrArg (fun w ↦ (ULift.down w).right) h).trans ?_
  have e : uliftYonedaEquiv.symm (yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) = 𝟙 _ :=
    uliftYonedaEquiv.symm_apply_apply _
  simp only [e, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  exact (congrArg (· ≫ c) (joinMap_id_id _ K)).trans (Category.id_comp c)

end Iterated

section Pushout

private lemma isPushout_joinMap_id {C A B P : SSet.{u}} {f : C ⟶ A} {g : C ⟶ B} {inl : A ⟶ P}
    {inr : B ⟶ P} (h : IsPushout f g inl inr) (Y : SSet.{u}) :
    IsPushout (joinMap (𝟙 Y) f) (joinMap (𝟙 Y) g) (joinMap (𝟙 Y) inl) (joinMap (𝟙 Y) inr) :=
  have : PreservesColimitsOfSize.{0, 0} (joinLeftUnder Y) := preservesColimitsOfSize_shrink _
  h.map (joinLeftUnder Y ⋙ Under.forget Y)

private noncomputable def sliceLiftOfIsPushout {C A B P X W : SSet.{u}} {f : C ⟶ A} {g : C ⟶ B}
    {inl : A ⟶ P} {inr : B ⟶ P} (h : IsPushout f g inl inr) (t : P ⟶ X)
    (a : W ⟶ (slice A).obj (Under.mk (inl ≫ t))) (b : W ⟶ (slice B).obj (Under.mk (inr ≫ t)))
    (hab : joinMap (𝟙 W) f ≫ sliceTranspose a = joinMap (𝟙 W) g ≫ sliceTranspose b) :
    W ⟶ (slice P).obj (Under.mk t) :=
  sliceUntranspose ((isPushout_joinMap_id h W).desc (sliceTranspose a) (sliceTranspose b) hab)
    (h.hom_ext
      (by
        rw [← reassoc_of% joinInclRight_comp_joinMap (𝟙 W) inl, IsPushout.inl_desc,
          joinInclRight_comp_sliceTranspose]
        rfl)
      (by
        rw [← reassoc_of% joinInclRight_comp_joinMap (𝟙 W) inr, IsPushout.inr_desc,
          joinInclRight_comp_sliceTranspose]
        rfl))

private lemma sliceTranspose_sliceLiftOfIsPushout {C A B P X W : SSet.{u}} {f : C ⟶ A}
    {g : C ⟶ B} {inl : A ⟶ P} {inr : B ⟶ P} (h : IsPushout f g inl inr) (t : P ⟶ X)
    (a : W ⟶ (slice A).obj (Under.mk (inl ≫ t))) (b : W ⟶ (slice B).obj (Under.mk (inr ≫ t)))
    (hab : joinMap (𝟙 W) f ≫ sliceTranspose a = joinMap (𝟙 W) g ≫ sliceTranspose b) :
    sliceTranspose (sliceLiftOfIsPushout h t a b hab) =
      (isPushout_joinMap_id h W).desc (sliceTranspose a) (sliceTranspose b) hab :=
  sliceTranspose_sliceUntranspose _ _

theorem isPullback_sliceRes {C A B P X : SSet.{u}} {f : C ⟶ A} {g : C ⟶ B} {inl : A ⟶ P}
    {inr : B ⟶ P} (h : IsPushout f g inl inr) (t : P ⟶ X) :
    IsPullback (sliceRes inl (Under.mk t)) (sliceRes inr (Under.mk t))
      (sliceRes f (Under.mk (inl ≫ t)))
      (sliceRes g (Under.mk (inr ≫ t)) ≫
        (slice C).map (Under.homMk (𝟙 X) (by simp [reassoc_of% h.w]) :
          Under.mk (g ≫ inr ≫ t) ⟶ Under.mk (f ≫ inl ≫ t))) := by
  have key : ∀ {W : SSet.{u}} (ψ : W ⟶ (slice B).obj (Under.mk (inr ≫ t))),
      sliceTranspose (ψ ≫ sliceRes g (Under.mk (inr ≫ t)) ≫
        (slice C).map (Under.homMk (𝟙 X) (by simp [reassoc_of% h.w]) :
          Under.mk (g ≫ inr ≫ t) ⟶ Under.mk (f ≫ inl ≫ t))) =
        joinMap (𝟙 W) g ≫ sliceTranspose ψ := fun ψ ↦ by
    have e := sliceTranspose_comp_map (ψ ≫ sliceRes g (Under.mk (inr ≫ t)))
      (Under.homMk (𝟙 X) (by simp [reassoc_of% h.w]) :
        Under.mk (g ≫ inr ≫ t) ⟶ Under.mk (f ≫ inl ≫ t))
    rw [Category.assoc] at e
    exact e.trans ((congrArg (· ≫ _) (sliceTranspose_comp_sliceRes g ψ)).trans
      (Category.comp_id _))
  have hc : ∀ {W : SSet.{u}} (a : W ⟶ (slice A).obj (Under.mk (inl ≫ t)))
      (b : W ⟶ (slice B).obj (Under.mk (inr ≫ t))),
      a ≫ sliceRes f (Under.mk (inl ≫ t)) = b ≫ sliceRes g (Under.mk (inr ≫ t)) ≫
        (slice C).map (Under.homMk (𝟙 X) (by simp [reassoc_of% h.w]) :
          Under.mk (g ≫ inr ≫ t) ⟶ Under.mk (f ≫ inl ≫ t)) →
      joinMap (𝟙 W) f ≫ sliceTranspose a = joinMap (𝟙 W) g ≫ sliceTranspose b :=
    fun a b hab ↦ (sliceTranspose_comp_sliceRes f a).symm.trans
      ((congrArg sliceTranspose hab).trans (key b))
  have w : sliceRes inl (Under.mk t) ≫ sliceRes f (Under.mk (inl ≫ t)) =
      sliceRes inr (Under.mk t) ≫ sliceRes g (Under.mk (inr ≫ t)) ≫
        (slice C).map (Under.homMk (𝟙 X) (by simp [reassoc_of% h.w]) :
          Under.mk (g ≫ inr ≫ t) ⟶ Under.mk (f ≫ inl ≫ t)) := by
    apply sliceTranspose_injective
    refine (sliceTranspose_comp_sliceRes f (sliceRes inl (Under.mk t))).trans
      (Eq.trans ?_ (key (sliceRes inr (Under.mk t))).symm)
    rw [sliceTranspose_sliceRes, sliceTranspose_sliceRes, joinMap_comp_joinMap_assoc,
      joinMap_comp_joinMap_assoc]
    exact congrArg (fun k ↦ joinMap (𝟙 _ ≫ 𝟙 _) k ≫ sliceTranspose (𝟙 _)) h.w
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w
    (fun s ↦ sliceLiftOfIsPushout h t s.fst s.snd (hc _ _ s.condition)) (fun s ↦ ?_)
    (fun s ↦ ?_) (fun s m hl hr ↦ ?_))
  · apply sliceTranspose_injective
    refine (sliceTranspose_comp_sliceRes inl _).trans ?_
    rw [sliceTranspose_sliceLiftOfIsPushout, IsPushout.inl_desc]
  · apply sliceTranspose_injective
    refine (sliceTranspose_comp_sliceRes inr _).trans ?_
    rw [sliceTranspose_sliceLiftOfIsPushout, IsPushout.inr_desc]
  · apply sliceTranspose_injective
    rw [sliceTranspose_sliceLiftOfIsPushout]
    apply (isPushout_joinMap_id h _).hom_ext
    · rw [IsPushout.inl_desc]
      exact (sliceTranspose_comp_sliceRes inl m).symm.trans (congrArg _ hl)
    · rw [IsPushout.inr_desc]
      exact (sliceTranspose_comp_sliceRes inr m).symm.trans (congrArg _ hr)

end Pushout

end SSet
